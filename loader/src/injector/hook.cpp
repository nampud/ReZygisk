#include <sys/mount.h>
#include <dlfcn.h>
#include <regex.h>
#include <bitset>
#include <list>
#include <map>
#include <array>
#include <vector>
#include <string>
#include <fstream>
#include <sstream>

#include <lsplt.hpp>

#include <fcntl.h>
#include <dirent.h>
#include <sys/types.h>
#include <sys/prctl.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <sys/socket.h>
#include <sys/sysmacros.h>
#include <mntent.h>

#include <unistd.h>
#include <pthread.h>

#include "daemon.h"
#include "zygisk.hpp"
#include "module.hpp"
#include "misc.h"

#include "solist.h"

#include "art_method.hpp"
#include "umount.hpp"
#include "utils.hpp"
#include "rules.hpp"
#include "socket_utils.h"

using namespace std;

static void hook_unloader();
static void unhook_functions();
static void do_umounts();

namespace {

enum {
    POST_SPECIALIZE,
    APP_FORK_AND_SPECIALIZE,
    APP_SPECIALIZE,
    SERVER_FORK_AND_SPECIALIZE,
    DO_REVERT_UNMOUNT,
    SKIP_FD_SANITIZATION,

    FLAG_MAX
};

enum mns_stages {
    MNS_INIT,
    MNS_MID,
    MNS_PRE_APP,
    MNS_APP
};

#define DCL_PRE_POST(name) \
void name##_pre();         \
void name##_post();

#define MAX_FD_SIZE 1024

struct ZygiskContext;

// Current context
ZygiskContext *g_ctx;

struct ZygiskContext {
    JNIEnv *env;
    union {
        void *ptr;
        AppSpecializeArgs_v5 *app;
        ServerSpecializeArgs_v1 *server;
    } args;

    const char *process;

    int pid;
    bitset<FLAG_MAX> flags;
    uint32_t info_flags;
    bitset<MAX_FD_SIZE + 1> allowed_fds;
    vector<int> exempted_fds;

    struct RegisterInfo {
        regex_t regex;
        string symbol;
        void *callback;
        void **backup;
    };

    struct IgnoreInfo {
        regex_t regex;
        string symbol;
    };

    pthread_mutex_t hook_info_lock;
    vector<RegisterInfo> register_info;
    vector<IgnoreInfo> ignore_info;

    ZygiskContext(JNIEnv *env, void *args) :
    env(env), args{args}, process(nullptr), pid(-1), info_flags(0),
    hook_info_lock(PTHREAD_MUTEX_INITIALIZER) {
        g_ctx = this;
    }
    ~ZygiskContext();

    /* Zygisksu changed: Load module fds */
    void run_modules_pre();
    void run_modules_post();
    DCL_PRE_POST(fork)
    DCL_PRE_POST(app_specialize)
    DCL_PRE_POST(nativeForkAndSpecialize)
    DCL_PRE_POST(nativeSpecializeAppProcess)
    DCL_PRE_POST(nativeForkSystemServer)

    void sanitize_fds();
    bool exempt_fd(int fd);
    bool is_child() const { return pid <= 0; }
    bool is_mounted() const {
        return (info_flags & (PROCESS_IS_MANAGER | PROCESS_GRANTED_ROOT)) || !(flags[DO_REVERT_UNMOUNT]);
    }

    // Compatibility shim
    void plt_hook_register(const char *regex, const char *symbol, void *fn, void **backup);
    void plt_hook_exclude(const char *regex, const char *symbol);
    void plt_hook_process_regex();

    bool plt_hook_commit();
};

#undef DCL_PRE_POST

bool load_modules_only();

// Global variables
vector<tuple<dev_t, ino_t, const char *, void **>> *plt_hook_list;
map<string, vector<JNINativeMethod>> *jni_hook_list;
bool should_unmap_zygisk = false;
bool enable_unloader = false;
bool hooked_unloader = false;
bool clean_zygote = false;
bool modules_loaded = false;
bool zygote_dlopen = false;
enum mns_stages mns_stage = MNS_INIT;
std::vector<lsplt::MapInfo> *cached_map_infos = nullptr;
list<ZygiskModule> *modules = nullptr;

} // namespace

namespace {

#define DCL_HOOK_FUNC(ret, func, ...) \
ret (*old_##func)(__VA_ARGS__);       \
ret new_##func(__VA_ARGS__)

// Skip actual fork and return cached result if applicable
DCL_HOOK_FUNC(int, fork) {
    if (g_ctx && g_ctx->pid >= 0) return g_ctx->pid;
    do_umounts();
    return old_fork();
}

bool update_mnt_ns(enum mount_namespace_state mns_state, bool dry_run) {
    char ns_path[PATH_MAX];
    if (rezygiskd_update_mns(mns_state, ns_path, sizeof(ns_path)) == false) {
        PLOGE("Failed to update mount namespace");

        return false;
    }

    if (dry_run) return true;

    int updated_ns = open(ns_path, O_RDONLY);
    if (updated_ns == -1) {
        PLOGE("Failed to open mount namespace [%s]", ns_path);

        return false;
    }

    const char *mns_state_str = NULL;
    if (mns_state == Clean) mns_state_str = "clean";
    else if (mns_state == Mounted) mns_state_str = "mounted";
    else mns_state_str = "unknown";

    LOGD("set mount namespace to [%s] fd=[%d]: %s", ns_path, updated_ns, mns_state_str);
    if (setns(updated_ns, CLONE_NEWNS) == -1) {
        PLOGE("Failed to set mount namespace [%s]", ns_path);
        close(updated_ns);

        return false;
    }

    close(updated_ns);

    return true;
}

pid_t fork_create(int *socket) {
    int sockets[2] = {-1, -1};
    if (socket) {
        if (socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, sockets) == -1) {
            PLOGE("fork_create: socketpair");
            *socket = -1;
            return -1;
        }
    }
    pid_t pid = fork();
    if (pid == 0) {
        if (socket) {
            close(sockets[0]);
            *socket = sockets[1];
        }
        return pid;
    }
    if (socket) {
        close(sockets[1]);
        *socket = sockets[0];
    }
    if (pid < 0) {
        PLOGE("fork_create: fork");
        if (socket) {
            close(sockets[0]);
            *socket = -1;
        }
        return pid;
    }
    return pid;
}

void fork_wait(pid_t pid) {
    if (pid <= 0) {
        LOGE("fork_wait: illegal pid %d", pid);
        return;
    }
    int status;
    pid_t w = TEMP_FAILURE_RETRY(waitpid(pid, &status, 0));
    if (w != pid) {
        PLOGE("fork_wait: waitpid(%d) = %d", pid, w);
    }
}

bool fork_and_wait() {
    pid_t pid = fork_create(nullptr);
    if (pid == 0) return true;
    fork_wait(pid);
    return false;
}

// Mount stuffs in the process's private mount namespace
DCL_HOOK_FUNC(int, unshare, int flags) {
    if (clean_zygote && (flags & CLONE_NEWNS) != 0) {
        if (g_ctx) {
            mns_stage = MNS_APP;
        } else if (mns_stage == MNS_INIT) {
            do_umounts();
            mns_stage = MNS_MID;
            flags &= ~CLONE_NEWNS;
            if (!flags) return 0;
        }
    }
    return old_unshare(flags);
}

DCL_HOOK_FUNC(int, mount, const char *source, const char *target, const char *fs_type, unsigned long flags, const void *data) {
    int ret = old_mount(source, target, fs_type, flags, data);
    if (!clean_zygote || mns_stage != MNS_MID || ret != 0) {
        return ret;
    }
    if (fork_and_wait()) {
        if (!update_mnt_ns(Mounted, false)) {
            PLOGE("mount hook: update_mnt_ns");
        } else if (old_mount(source, target, fs_type, flags, data) != 0) {
            PLOGE("mount hook: old_mount");
        }
        _exit(0);
    }
    return ret;
}

DCL_HOOK_FUNC(int, umount2, const char *target, int flags) {
    int ret = old_umount2(target, flags);
    if (!clean_zygote || mns_stage != MNS_MID || ret != 0) {
        return ret;
    }
    if (fork_and_wait()) {
        if (!update_mnt_ns(Mounted, false)) {
            PLOGE("umount2 hook: update_mnt_ns");
        } else if (old_umount2(target, flags) != 0) {
            PLOGE("umount2 hook: old_umount2");
        }
        _exit(0);
    }
    return ret;
}

// We cannot directly call `dlclose` to unload ourselves, otherwise when `dlclose` returns,
// it will return to our code which has been unmapped, causing segmentation fault.
// Instead, we hook `pthread_attr_setstacksize` which will be called when VM daemon threads start.
DCL_HOOK_FUNC(int, pthread_attr_setstacksize, void *target, size_t size) {
    int res = old_pthread_attr_setstacksize((pthread_attr_t *)target, size);
    LOGV("Call pthread_attr_setstacksize in [tid, pid]: %d, %d", gettid(), getpid());

    if (!enable_unloader)
        return res;

    // Only perform unloading on the main thread
    if (gettid() != getpid())
        return res;

    if (should_unmap_zygisk) {
        unhook_functions();

        if (should_unmap_zygisk) {
            // Because both `pthread_attr_setstacksize` and `dlclose` have the same function signature,
            // we can use `musttail` to let the compiler reuse our stack frame and thus
            // `dlclose` will directly return to the caller of `pthread_attr_setstacksize`.
            LOGD("unmap libzygisk.so loaded at %p with size %zu", start_addr, block_size);

            [[clang::musttail]] return munmap(start_addr, block_size);
        }
    }

    return res;
}

void initialize_jni_hook();

DCL_HOOK_FUNC(char *, strdup, const char *s) {
  if (strcmp(s, "com.android.internal.os.ZygoteInit") == 0) {
      LOGV("strdup %s", s);
      initialize_jni_hook();
      *cached_map_infos = lsplt::MapInfo::Scan();
      LOGD("cached_map_infos updated");
    }

    return old_strdup(s);
}

/*
 * INFO: Our goal is to get called after libart.so is loaded, but before ART actually starts running.
 * If we are too early, we won't find libart.so in maps, and if we are too late, we could make other
 * threads crash if they try to use the PLT while we are in the process of hooking it.
 * For this task, hooking property_get was chosen as there are lots of calls to this, so it's
 * relatively unlikely to break.
 *
 * The line where libart.so is loaded is:
 * https://github.com/aosp-mirror/platform_frameworks_base/blob/1cdfff555f4a21f71ccc978290e2e212e2f8b168/core/jni/AndroidRuntime.cpp#L1266
 *
 * And shortly after that, in the startVm method that is called right after, there are many calls to property_get:
 * https://github.com/aosp-mirror/platform_frameworks_base/blob/1cdfff555f4a21f71ccc978290e2e212e2f8b168/core/jni/AndroidRuntime.cpp#L791
 *
 * After we succeed in getting called at a point where libart.so is already loaded, we will ignore
 * the rest of the property_get calls.
 */
DCL_HOOK_FUNC(int, property_get, const char *key, char *value, const char *default_value) {
    hook_unloader();
    return old_property_get(key, value, default_value);
}

#undef DCL_HOOK_FUNC

// -----------------------------------------------------------------

static bool can_hook_jni = false;
static jint MODIFIER_NATIVE = 0;
static jmethodID member_getModifiers = nullptr;

void hookJniNativeMethods(JNIEnv *env, const char *clz, JNINativeMethod *methods, int numMethods) {
    if (!can_hook_jni) return;
    auto clazz = env->FindClass(clz);
    if (clazz == nullptr) {
        env->ExceptionClear();
        for (int i = 0; i < numMethods; i++) {
            methods[i].fnPtr = nullptr;
        }
        return;
    }

    vector<JNINativeMethod> hooks;
    for (int i = 0; i < numMethods; i++) {
        auto &nm = methods[i];
        auto mid = env->GetMethodID(clazz, nm.name, nm.signature);
        bool is_static = false;
        if (mid == nullptr) {
            env->ExceptionClear();
            mid = env->GetStaticMethodID(clazz, nm.name, nm.signature);
            is_static = true;
        }
        if (mid == nullptr) {
            env->ExceptionClear();
            nm.fnPtr = nullptr;
            continue;
        }
        auto method = lsplant::JNI_ToReflectedMethod(env, clazz, mid, is_static);
        auto modifier = lsplant::JNI_CallIntMethod(env, method, member_getModifiers);
        if ((modifier & MODIFIER_NATIVE) == 0) {
            nm.fnPtr = nullptr;
            continue;
        }
        auto artMethod = lsplant::art::ArtMethod::FromReflectedMethod(env, method);
        hooks.push_back(nm);
        auto orig = artMethod->GetData();
        LOGV("replaced %s %s orig %p", clz, nm.name, orig);
        nm.fnPtr = orig;
    }

    if (hooks.empty()) return;
    env->RegisterNatives(clazz, hooks.data(), hooks.size());
}

// JNI method hook definitions, auto generated
#include "jni_hooks.hpp"

void initialize_jni_hook() {
    auto get_created_java_vms = reinterpret_cast<jint (*)(JavaVM **, jsize, jsize *)>(
            dlsym(RTLD_DEFAULT, "JNI_GetCreatedJavaVMs"));
    if (!get_created_java_vms) {
        for (auto &map: *cached_map_infos) {
            if (!map.path.ends_with("/libnativehelper.so")) continue;
            void *h = dlopen(map.path.data(), RTLD_LAZY);
            if (!h) {
                LOGW("cannot dlopen libnativehelper.so: %s", dlerror());
                break;
            }
            get_created_java_vms = reinterpret_cast<decltype(get_created_java_vms)>(dlsym(h, "JNI_GetCreatedJavaVMs"));
            dlclose(h);
            break;
        }
        if (!get_created_java_vms) {
            LOGW("JNI_GetCreatedJavaVMs not found");
            return;
        }
    }
    JavaVM *vm = nullptr;
    jsize num = 0;
    jint res = get_created_java_vms(&vm, 1, &num);
    if (res != JNI_OK || vm == nullptr) return;
    JNIEnv *env = nullptr;
    res = vm->GetEnv(reinterpret_cast<void **>(&env), JNI_VERSION_1_6);
    if (res != JNI_OK || env == nullptr) return;

    auto classMember = lsplant::JNI_FindClass(env, "java/lang/reflect/Member");
    if (classMember != nullptr) member_getModifiers = lsplant::JNI_GetMethodID(env, classMember, "getModifiers", "()I");
    auto classModifier = lsplant::JNI_FindClass(env, "java/lang/reflect/Modifier");
    if (classModifier != nullptr) {
        auto fieldId = lsplant::JNI_GetStaticFieldID(env, classModifier, "NATIVE", "I");
        if (fieldId != nullptr) MODIFIER_NATIVE = lsplant::JNI_GetStaticIntField(env, classModifier, fieldId);
    }
    if (member_getModifiers == nullptr || MODIFIER_NATIVE == 0) return;
    if (!lsplant::art::ArtMethod::Init(env)) {
        LOGE("failed to init ArtMethod");
        return;
    }

    can_hook_jni = true;
    do_hook_zygote(env);
}

// -----------------------------------------------------------------

ZygiskModule::ZygiskModule(int id, void *handle, void *entry)
: id(id), handle(handle), entry{entry}, api{}, mod{nullptr} {
    // Make sure all pointers are null
    memset(&api, 0, sizeof(api));
    api.base.impl = this;
    api.base.registerModule = &ZygiskModule::RegisterModuleImpl;
}

bool ZygiskModule::RegisterModuleImpl(ApiTable *api, long *module) {
    if (api == nullptr || module == nullptr)
        return false;

    long api_version = *module;
    // Unsupported version
    if (api_version > ZYGISK_API_VERSION)
        return false;

    // Set the actual module_abi*
    api->base.impl->mod = { module };

    // Fill in API accordingly with module API version
    if (api_version >= 1) {
        api->v1.hookJniNativeMethods = hookJniNativeMethods;
        api->v1.pltHookRegister = [](auto a, auto b, auto c, auto d) {
            if (g_ctx) g_ctx->plt_hook_register(a, b, c, d);
        };
        api->v1.pltHookExclude = [](auto a, auto b) {
            if (g_ctx) g_ctx->plt_hook_exclude(a, b);
        };
        api->v1.pltHookCommit = []() { return g_ctx && g_ctx->plt_hook_commit(); };
        api->v1.connectCompanion = [](ZygiskModule *m) { return m->connectCompanion(); };
        api->v1.setOption = [](ZygiskModule *m, auto opt) { m->setOption(opt); };
    }
    if (api_version >= 2) {
        api->v2.getModuleDir = [](ZygiskModule *m) { return m->getModuleDir(); };
        api->v2.getFlags = [](auto) { return ZygiskModule::getFlags(); };
    }
    if (api_version >= 4) {
        api->v4.pltHookCommit = []() { return lsplt::CommitHook(*cached_map_infos); };
        api->v4.pltHookRegister = [](dev_t dev, ino_t inode, const char *symbol, void *fn, void **backup) {
            if (dev == 0 || inode == 0 || symbol == nullptr || fn == nullptr)
                return;
            lsplt::RegisterHook(dev, inode, symbol, fn, backup);
        };
        api->v4.exemptFd = [](int fd) { return g_ctx && g_ctx->exempt_fd(fd); };
    }

    return true;
}

void ZygiskContext::plt_hook_register(const char *regex, const char *symbol, void *fn, void **backup) {
    if (regex == nullptr || symbol == nullptr || fn == nullptr)
        return;
    regex_t re;
    if (regcomp(&re, regex, REG_NOSUB) != 0)
        return;
    pthread_mutex_lock(&hook_info_lock);
    register_info.emplace_back(RegisterInfo{re, symbol, fn, backup});
    pthread_mutex_unlock(&hook_info_lock);
}

void ZygiskContext::plt_hook_exclude(const char *regex, const char *symbol) {
    if (!regex) return;
    regex_t re;
    if (regcomp(&re, regex, REG_NOSUB) != 0)
        return;
    pthread_mutex_lock(&hook_info_lock);
    ignore_info.emplace_back(IgnoreInfo{re, symbol ?: ""});
    pthread_mutex_unlock(&hook_info_lock);
}

void ZygiskContext::plt_hook_process_regex() {
    if (register_info.empty())
        return;
    for (auto &map : *cached_map_infos) {
        if (map.offset != 0 || !map.is_private || !(map.perms & PROT_READ)) continue;
        for (auto &reg: register_info) {
            if (regexec(&reg.regex, map.path.data(), 0, nullptr, 0) != 0)
                continue;
            bool ignored = false;
            for (auto &ign: ignore_info) {
                if (regexec(&ign.regex, map.path.data(), 0, nullptr, 0) != 0)
                    continue;
                if (ign.symbol.empty() || ign.symbol == reg.symbol) {
                    ignored = true;
                    break;
                }
            }
            if (!ignored) {
                lsplt::RegisterHook(map.dev, map.inode, reg.symbol, reg.callback, reg.backup);
            }
        }
    }
}

bool ZygiskContext::plt_hook_commit() {
    {
        pthread_mutex_lock(&hook_info_lock);
        plt_hook_process_regex();
        register_info.clear();
        ignore_info.clear();
        pthread_mutex_unlock(&hook_info_lock);
    }

    return lsplt::CommitHook(*cached_map_infos);
}


bool ZygiskModule::valid() const {
    if (mod.api_version == nullptr)
        return false;
    switch (*mod.api_version) {
        case 4:
        case 3:
        case 2:
        case 1:
            return mod.v1->impl && mod.v1->preAppSpecialize && mod.v1->postAppSpecialize &&
                   mod.v1->preServerSpecialize && mod.v1->postServerSpecialize;
        default:
            return false;
    }
}

/* Zygisksu changed: Use own zygiskd */
int ZygiskModule::connectCompanion() const {
    return rezygiskd_connect_companion(id);
}

/* Zygisksu changed: Use own zygiskd */
int ZygiskModule::getModuleDir() const {
    return rezygiskd_get_module_dir(id);
}

void ZygiskModule::setOption(zygisk::Option opt) {
    if (g_ctx == nullptr)
        return;
    switch (opt) {
    case zygisk::FORCE_DENYLIST_UNMOUNT:
        g_ctx->flags[DO_REVERT_UNMOUNT] = true;
        break;
    case zygisk::DLCLOSE_MODULE_LIBRARY:
        unload = true;
        break;
    }
}

uint32_t ZygiskModule::getFlags() {
    return g_ctx ? (g_ctx->info_flags & ~PRIVATE_MASK) : 0;
}

// -----------------------------------------------------------------

int sigmask(int how, int signum) {
    sigset_t set;
    sigemptyset(&set);
    sigaddset(&set, signum);
    return sigprocmask(how, &set, nullptr);
}

void ZygiskContext::fork_pre() {
    if (zygote_dlopen && !modules_loaded) {
        load_modules_only();
    }

    /* INFO: Do our own fork before loading any 3rd party code.
             First block SIGCHLD, unblock after original fork is done.
    */
    sigmask(SIG_BLOCK, SIGCHLD);
    do_umounts();
    pid = old_fork();
    if (pid != 0 || flags[SKIP_FD_SANITIZATION])
        return;

    /* INFO: Record all open fds */
    DIR *dir = opendir("/proc/self/fd");
    if (dir == nullptr) {
        PLOGE("Failed to open /proc/self/fd");

        return;
    }

    struct dirent *entry;
    int dir_fd = dirfd(dir);

    while ((entry = readdir(dir))) {
        int fd = parse_int(entry->d_name);
        if (fd >= 0 && fd != dir_fd) allowed_fds[min(fd, MAX_FD_SIZE)] = true;
    }

    closedir(dir);
}

void ZygiskContext::sanitize_fds() {
    if (flags[SKIP_FD_SANITIZATION])
        return;

    if (flags[APP_FORK_AND_SPECIALIZE]) {
        auto update_fd_array = [&](int off) -> jintArray {
            if (exempted_fds.empty())
                return nullptr;

            jintArray array = env->NewIntArray(static_cast<int>(off + exempted_fds.size()));
            if (array == nullptr)
                return nullptr;

            env->SetIntArrayRegion(array, off, static_cast<int>(exempted_fds.size()), exempted_fds.data());
            for (int fd : exempted_fds) {
                if (fd >= 0) {
                    allowed_fds[min(fd, MAX_FD_SIZE)] = true;
                }
            }
            *args.app->fds_to_ignore = array;
            flags[SKIP_FD_SANITIZATION] = true;
            return array;
        };

        if (jintArray fdsToIgnore = *args.app->fds_to_ignore) {
            int *arr = env->GetIntArrayElements(fdsToIgnore, nullptr);
            int len = env->GetArrayLength(fdsToIgnore);
            for (int i = 0; i < len; ++i) {
                int fd = arr[i];
                if (fd >= 0) {
                    allowed_fds[min(fd, MAX_FD_SIZE)] = true;
                }
            }
            if (jintArray newFdList = update_fd_array(len)) {
                env->SetIntArrayRegion(newFdList, 0, len, arr);
            }
            env->ReleaseIntArrayElements(fdsToIgnore, arr, JNI_ABORT);
        } else {
            update_fd_array(0);
        }
    }

    if (pid != 0)
        return;

    // Close all forbidden fds to prevent crashing
    DIR *dir = opendir("/proc/self/fd");
    if (dir == nullptr) {
        PLOGE("Failed to open /proc/self/fd");

        return;
    }

    int dfd = dirfd(dir);
    struct dirent *entry;
    while ((entry = readdir(dir))) {
        int fd = parse_int(entry->d_name);
        if (fd < 0 || fd == dfd || allowed_fds[min(fd, MAX_FD_SIZE)]) continue;

        close(fd);

        LOGW("Closed leaked fd: %d", fd);
    }

    closedir(dir);
}

void ZygiskContext::fork_post() {
    // Unblock SIGCHLD in case the original method didn't
    sigmask(SIG_UNBLOCK, SIGCHLD);
    g_ctx = nullptr;
}

bool load_modules_only() {
  if (modules_loaded) {
      return true;
  }

  modules_loaded = true;

  struct zygisk_modules ms;
  if (rezygiskd_read_modules(&ms) == false) {
    LOGE("Failed to read modules from zygiskd");

    return false;
  }

  for (size_t i = 0; i < ms.modules_count; i++) {
    char *lib_path = ms.modules[i];

    void *handle = dlopen(lib_path, RTLD_NOW);
    if (!handle) {
      LOGE("Failed to load module [%s]: %s", lib_path, dlerror());

      continue;
    }

    void *entry = dlsym(handle, "zygisk_module_entry");
    if (!entry) {
      LOGE("Failed to find entry point in module [%s]: %s", lib_path, dlerror());

      dlclose(handle);

      continue;
    }

    modules->emplace_back(i, handle, entry);
  }

  free_modules(&ms);
  return true;
}

/* Zygisksu changed: Load module fds */
void ZygiskContext::run_modules_pre() {
  for (auto &m : *modules) {
    m.onLoad(env);

    if (flags[APP_SPECIALIZE]) m.preAppSpecialize(args.app);
    else if (flags[SERVER_FORK_AND_SPECIALIZE]) m.preServerSpecialize(args.server);
  }
}

void ZygiskContext::run_modules_post() {
    flags[POST_SPECIALIZE] = true;

    size_t modules_unloaded = 0;
    for (const auto &m : *modules) {
        if (flags[APP_SPECIALIZE]) m.postAppSpecialize(args.app);
        else if (flags[SERVER_FORK_AND_SPECIALIZE]) m.postServerSpecialize(args.server);

        /* INFO: If module is unloaded by dlclose, there's no need to
                   hide it from soinfo manually. */
        if (m.tryUnload()) modules_unloaded++;
        else {
            bool has_dropped = solist_drop_so_path(m.getEntry(), false);
            if (!has_dropped) continue;

            LOGD("Dropped solist record for %p", m.getEntry());
        }
    }

    if (modules->size() > 0) {
        LOGD("Modules unloaded: %zu/%zu", modules_unloaded, modules->size());

        solist_reset_counters(modules->size(), modules_unloaded);

        LOGD("Returned global counters to their original values");
    }
}

/* Zygisksu changed: Load module fds */
void ZygiskContext::app_specialize_pre() {
    flags[APP_SPECIALIZE] = true;
    mns_stage = MNS_PRE_APP;

    auto app_uid = (uid_t) g_ctx->args.app->uid;
    info_flags = rezygiskd_get_process_flags(app_uid, (const char *const)process);

    const char *data_dir_p = args.app->app_data_dir ? env->GetStringUTFChars(args.app->app_data_dir, nullptr) : nullptr;
    std::string data_dir(data_dir_p ? data_dir_p : "");
    std::string cmdline(process);

    /* INFO: Get main app UID of isolated processes through app_data_dir */
    if ((info_flags & PROCESS_ON_DENYLIST) == 0 && !data_dir.empty()) {
        struct stat st = {};
        if (stat(data_dir.c_str(), &st) == 0 && st.st_uid != app_uid) {
            app_uid = st.st_uid;
            uint32_t main_flags = rezygiskd_get_process_flags(st.st_uid, (const char *const)process);
            info_flags |= (main_flags & PROCESS_ON_DENYLIST);
        }
    }

    if ((info_flags & (PROCESS_GRANTED_ROOT | PROCESS_IS_MANAGER)) == 0) {
        if (rules_should_deny(app_uid, cmdline, data_dir,
                              (info_flags & PROCESS_ON_DENYLIST) != 0)) {
            info_flags |= PROCESS_ON_DENYLIST;
        } else {
            info_flags &= ~PROCESS_ON_DENYLIST;
        }
    } else {
        info_flags &= ~PROCESS_ON_DENYLIST;
    }

    if (data_dir_p) {
        env->ReleaseStringUTFChars(args.app->app_data_dir, data_dir_p);
    }

     if (info_flags & PROCESS_IS_FIRST_STARTED) {
        /* INFO: To ensure we are really using a clean mount namespace, we use
                   the first process it as reference for clean mount namespace,
                   before it even does something, so that it will be clean yet
                   with expected mounts.
        */
        if (!clean_zygote) {
            update_mnt_ns(Clean, true);
        }
    }

    if ((info_flags & PROCESS_IS_MANAGER) == PROCESS_IS_MANAGER) {
        LOGD("Manager process detected. Notifying that Zygisk has been enabled.");

        /* INFO: This environment variable is related to Magisk Zygisk/Manager. It
                   it used by Magisk's Zygisk to communicate to Magisk Manager whether
                   Zygisk is working or not, allowing Zygisk modules to both work properly
                   and for the manager to mark Zygisk as enabled.

                 However, to enhance capabilities of root managers, it is also set for
                   any other supported manager, so that, if they wish, they can recognize
                   if Zygisk is enabled.
        */
        setenv("ZYGISK_ENABLED", "1", 1);
    }

    if ((info_flags & PROCESS_ON_DENYLIST) == PROCESS_ON_DENYLIST) {
        flags[DO_REVERT_UNMOUNT] = true;
    }

    if (clean_zygote) {
        if (is_mounted()) {
            update_mnt_ns(Mounted, false);
        }
    }

    /* INFO: Because we load directly from the file, we need to do it before we umount
               the mounts, or else it won't have access to /data/adb anymore.
    */
    if (!load_modules_only()) {
        LOGE("Failed to load modules");
        return;
    }

    /* INFO: Modules only have two "start off" points from Zygisk, preSpecialize and
                postSpecialize. In preSpecialize, the process still has privileged
                permissions, and therefore can execute mount/umount/setns functions.
                If we update the mount namespace AFTER executing them, any mounts made
                will be lost, and the process will not have access to them anymore.

                In postSpecialize, while still could have its mounts modified with the
                assistance of a Zygisk companion, it will already have the mount
                namespace switched by then, so there won't be issues.

                Knowing this, we update the mns before execution, so that they can still
                make changes to mounts in DenyListed processes without being reverted.
    */
    bool in_denylist = (info_flags & PROCESS_ON_DENYLIST) == PROCESS_ON_DENYLIST;
    if (in_denylist) {
        if (!clean_zygote) update_mnt_ns(Clean, false);
    }


    if (!clean_zygote) {
        FILE *fp = setmntent("/proc/mounts", "r");
        if (fp) {
            while (getmntent(fp));
            endmntent(fp);
        }
    }

    /* INFO: Executed after setns to ensure a module can update the mounts of an
                application without worrying about it being overwritten by setns.
    */
    run_modules_pre();

    /* INFO: The modules may request that although the process is NOT in
                the DenyList, it has its mount namespace switched to the clean
                one.

                So to ensure this behavior happens, we must also check after the
                modules are loaded and executed, so that the modules can have
                the chance to request it.
    */
    // if (!in_denylist && flags[DO_REVERT_UNMOUNT])
    //    update_mnt_ns(Clean, false);

}


void ZygiskContext::app_specialize_post() {
    run_modules_post();

    // Cleanups
    env->ReleaseStringUTFChars(args.app->nice_name, process);
    g_ctx = nullptr;
}

bool ZygiskContext::exempt_fd(int fd) {
    if (flags[POST_SPECIALIZE] || flags[SKIP_FD_SANITIZATION])
        return true;
    if (!flags[APP_FORK_AND_SPECIALIZE])
        return false;
    exempted_fds.push_back(fd);
    return true;
}

// -----------------------------------------------------------------

void ZygiskContext::nativeSpecializeAppProcess_pre() {
    process = env->GetStringUTFChars(args.app->nice_name, nullptr);
    LOGV("pre specialize [%s]", process);
    // App specialize does not check FD
    flags[SKIP_FD_SANITIZATION] = true;
    app_specialize_pre();
}

void ZygiskContext::nativeSpecializeAppProcess_post() {
    LOGV("post specialize [%s]", process);
    app_specialize_post();
}

/* Zygisksu changed: No system_server status write back */
void ZygiskContext::nativeForkSystemServer_pre() {
    LOGV("pre forkSystemServer");
    flags[SERVER_FORK_AND_SPECIALIZE] = true;

    fork_pre();
    if (!is_child())
      return;

    mns_stage = MNS_PRE_APP;

    if (clean_zygote) {
        const std::string proc = "system_server";
        info_flags = rezygiskd_get_process_flags(1000, proc.c_str());

        if (rules_should_deny(1000, proc, proc, (info_flags & PROCESS_ON_DENYLIST) != 0)) {
            info_flags |= PROCESS_ON_DENYLIST;
        } else {
            info_flags &= ~PROCESS_ON_DENYLIST;
        }

        if ((info_flags & PROCESS_ON_DENYLIST) == PROCESS_ON_DENYLIST) {
            flags[DO_REVERT_UNMOUNT] = true;
        }

        if (is_mounted()) {
            update_mnt_ns(Mounted, false);
        }
    }

    load_modules_only();
    run_modules_pre();
    rezygiskd_system_server_started();

    sanitize_fds();
}

void ZygiskContext::nativeForkSystemServer_post() {
    if (pid == 0) {
        LOGV("post forkSystemServer");
        run_modules_post();
    }
    fork_post();
}

void ZygiskContext::nativeForkAndSpecialize_pre() {
    process = env->GetStringUTFChars(args.app->nice_name, nullptr);
    LOGV("pre forkAndSpecialize [%s]", process);
    flags[APP_FORK_AND_SPECIALIZE] = true;

    fork_pre();
    if (pid == 0)
        app_specialize_pre();

    sanitize_fds();
}

void ZygiskContext::nativeForkAndSpecialize_post() {
    if (pid == 0) {
        LOGV("post forkAndSpecialize [%s]", process);
        app_specialize_post();
    }
    fork_post();
}

ZygiskContext::~ZygiskContext() {
    // This global pointer points to a variable on the stack.
    // Set this to nullptr to prevent leaking local variable.
    // This also disables most plt hooked functions.
    g_ctx = nullptr;

    if (!is_child())
        return;

    should_unmap_zygisk = true;

    // Unhook JNI methods
    for (const auto &[clz, methods] : *jni_hook_list) {
        if (!methods.empty() && env->RegisterNatives(
                env->FindClass(clz.data()), methods.data(),
                static_cast<int>(methods.size())) != 0) {
            LOGE("Failed to restore JNI hook of class [%s]", clz.data());
            should_unmap_zygisk = false;
        }
    }
    delete jni_hook_list;
    jni_hook_list = nullptr;

    // Strip out all API function pointers
    for (auto &m : *modules) {
        m.clearApi();
    }

    enable_unloader = true;
}

} // namespace

static bool hook_commit(std::vector<lsplt::MapInfo> &map_infos = *cached_map_infos) {
    if (lsplt::CommitHook(map_infos)) {
        return true;
    } else {
        LOGE("plt_hook failed");
        return false;
    }
}

static void hook_register(dev_t dev, ino_t inode, const char *symbol, void *new_func, void **old_func) {
    if (!lsplt::RegisterHook(dev, inode, symbol, new_func, old_func)) {
        LOGE("Failed to register plt_hook \"%s\"", symbol);
        return;
    }
    plt_hook_list->emplace_back(dev, inode, symbol, old_func);
}

#define PLT_HOOK_REGISTER_SYM(DEV, INODE, SYM, NAME) \
    hook_register(DEV, INODE, SYM, (void*) new_##NAME, (void **) &old_##NAME)

#define PLT_HOOK_REGISTER(DEV, INODE, NAME) \
    PLT_HOOK_REGISTER_SYM(DEV, INODE, #NAME, NAME)

static bool set_exec_con(const char *con) {
    FILE *fp = fopen("/proc/self/attr/exec", "w");
    if (!fp) {
        PLOGE("set_exec_con: fopen exec");
        return false;
    }
    size_t len = strlen(con);
    size_t written;
    if ((written = fwrite(con, 1, len, fp)) != len) {
        PLOGE("set_exec_con: fwrite exec (actual %d, expected %d)", (int) written, (int) len);
        fclose(fp);
        return false;
    }
    if (fclose(fp) != 0) {
        PLOGE("set_exec_con: fclose exec");
        return false;
    }
    return true;
}

static int is_zygote_con() {
    const std::string path = "/proc/self/attr/current";
    std::ifstream file(path);

    if (!file.is_open()) {
        PLOGE("is_zygote_con: ifstream(/proc/self/attr/current)");
        return -1;
    }

    std::string contents((std::istreambuf_iterator<char>(file)),
                         std::istreambuf_iterator<char>());

    return contents.find("zygote") != std::string::npos;
}

static bool load_early_mns() {
    const char *path = TMP_PATH "/" LP_SELECT("mns32", "mns64");

    int early_ns = open(path, O_RDONLY | O_CLOEXEC);
    if (early_ns == -1) {
        PLOGE("load_early_mns: open(%s)", path);
        return false;
    }

    if (setns(early_ns, CLONE_NEWNS) == -1) {
        PLOGE("load_early_mns: setns(%d)", early_ns);
        close(early_ns);
        return false;
    }

    close(early_ns);
    return true;
}

void clean_mounts(char **argv, char **envp) {
    if (!argv && !envp) {
        /* INFO: If argv is null, it means that we are past re-exec (see ptracer.c is_first) */
        /* INFO: Re-exec only happens in clean_zygote mode so we should assume it to be active */
        clean_zygote = true;
        return;
    }

    if (!argv || !envp) {
        PLOGE("clean_mounts: argv = %p, envp = %p", argv, envp);
    }

    clean_zygote = access(TMP_PATH "/clean_zygote", F_OK) == 0;
    if (!clean_zygote) {
        LOGE("clean_mounts: clean_zygote is not active");
        return;
    }

    LOGD("clean_mounts: cleaning mounts");

    int orig_ns = open("/proc/self/ns/mnt", O_RDONLY | O_CLOEXEC);
    if (orig_ns == -1) {
        PLOGE("clean_mounts: orig_ns = open(/proc/self/ns/mnt) orig");
        return;
    }

    if (!load_early_mns()) {
        if (unshare(CLONE_NEWNS) == -1) {
            PLOGE("clean_mounts: unshare(CLONE_NEWNS) for clean");
            close(orig_ns);
            return;
        }
    }

    if (mount(nullptr, "/", nullptr, MS_REC | MS_SLAVE, nullptr) == -1) {
        PLOGE("clean_mounts: mount(/, MS_REC | MS_SLAVE) for clean");
        close(orig_ns);
        return;
    }

    do_umounts();

    int clean_ns = open("/proc/self/ns/mnt", O_RDONLY | O_CLOEXEC);
    if (clean_ns == -1) {
        PLOGE("clean_mounts: clean_ns = open(/proc/self/ns/mnt)");
        close(orig_ns);
        return;
    }

    int mns_proc_sock = -1;
    pid_t mns_proc_pid;
    if ((mns_proc_pid = fork_create(&mns_proc_sock)) == 0) {
        /*
         * INFO: Having a mount namespace with no processes in it can cause weird things
         * to happen, so we create this process to keep the clean namespace active while
         * we temporarily switch back to the original namespace.
         */
        char dummy;
        TEMP_FAILURE_RETRY(read(mns_proc_sock, &dummy, 1));
        _exit(0);
    }

    if (setns(orig_ns, CLONE_NEWNS) == -1) {
        PLOGE("clean_mounts: setns(orig_ns)");
    }

    close(orig_ns);

    if (unshare(CLONE_NEWNS) == -1) {
        PLOGE("clean_mounts: unshare(CLONE_NEWNS) for mounted");
        goto fail_close;
    }

    if (mount(nullptr, "/", nullptr, MS_REC | MS_SLAVE, nullptr) == -1) {
        PLOGE("clean_mounts: mount(/, MS_REC | MS_SLAVE) for mounted");
        goto fail_close;
    }

    if (!update_mnt_ns(Mounted, true)) {
        PLOGE("clean_mounts: update_mnt_ns(Mounted)");
        fail_close:
        close(clean_ns);
        close(mns_proc_sock);
        fork_wait(mns_proc_pid);
        return;
    }

    if (setns(clean_ns, CLONE_NEWNS) == -1) {
        PLOGE("clean_mounts: setns(clean_ns)");
    }

    close(clean_ns);
    close(mns_proc_sock);
    fork_wait(mns_proc_pid);

    if (is_zygote_con() != 0) {
        /*
         * INFO: If we are here, it means that the ptrace code (breakpoint.c) failed to set
         * our security context to init. In this case, calling execve will cause a worse
         * detection than what it fixes, so we don't.
         */
        LOGE("clean_mounts: in zygote context, skip reexec");
    } else {
        if (!set_exec_con("u:r:zygote:s0")) {
            exit(1);
        }

        LOGD("clean_mounts: restarting self: execve(%s)", argv[0]);
        execve(argv[0], argv, envp);
        PLOGE("clean_mounts: restart with execve(%s)", argv[0]);
        exit(1);
    }
}

static MappedBuffer mountinfo_buf;
static MappedBuffer mountinfo_prev;

static void do_umounts() {
    if (!clean_zygote) return;
    if (mns_stage == MNS_PRE_APP || mns_stage == MNS_APP) return;
    pid_t my_pid = getpid();
    if (gettid() != my_pid) return;

    if (!rules_reload()) {
        if (mountinfo_buf.file_read("/proc/self/mounts", mountinfo_prev.size)) {
            if (mountinfo_buf == mountinfo_prev) return;
            std::swap(mountinfo_prev, mountinfo_buf);
        }
    }

    int client = socket(PF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0);
    if (client == -1) {
        PLOGE("do_umounts: socket");
        return;
    }

    if (TEMP_FAILURE_RETRY(connect(client, (const sockaddr *) &umountd_sock_addr,
                                   sizeof(umountd_sock_addr))) == -1) {
        PLOGE("do_umounts: connect");
        close(client);
        return;
    }

    if (write_n(client, &my_pid, sizeof(my_pid)) <= 0) {
        PLOGE("do_umounts: write_n");
        close(client);
        return;
    }

    char dummy;
    TEMP_FAILURE_RETRY(read(client, &dummy, 1));
    close(client);
}


void hook_functions() {
    zygote_dlopen = access(TMP_PATH "/zygote_dlopen", F_OK) == 0;
    plt_hook_list = new vector<tuple<dev_t, ino_t, const char *, void **>>();
    jni_hook_list = new map<string, vector<JNINativeMethod>>();

    ino_t android_runtime_inode = 0;
    dev_t android_runtime_dev = 0;

    cached_map_infos = new std::vector<lsplt::MapInfo>();
    *cached_map_infos = lsplt::MapInfo::Scan();

    modules = new list<ZygiskModule>();

    for (auto &map : *cached_map_infos) {
        if (map.path.ends_with("libandroid_runtime.so")) {
            android_runtime_inode = map.inode;
            android_runtime_dev = map.dev;

            break;
        }
    }

    PLT_HOOK_REGISTER(android_runtime_dev, android_runtime_inode, fork);
    PLT_HOOK_REGISTER(android_runtime_dev, android_runtime_inode, unshare);
    PLT_HOOK_REGISTER(android_runtime_dev, android_runtime_inode, strdup);
    PLT_HOOK_REGISTER(android_runtime_dev, android_runtime_inode, property_get);
    PLT_HOOK_REGISTER(android_runtime_dev, android_runtime_inode, mount);
    PLT_HOOK_REGISTER(android_runtime_dev, android_runtime_inode, umount2);
    hook_commit();

    // Remove unhooked methods
    plt_hook_list->erase(
            std::remove_if(plt_hook_list->begin(), plt_hook_list->end(),
                           [](auto &t) { return *std::get<3>(t) == nullptr;}),
            plt_hook_list->end());
}

static void hook_unloader() {
    if (hooked_unloader) return;
    hooked_unloader = true;

    ino_t art_inode = 0;
    dev_t art_dev = 0;

    *cached_map_infos = lsplt::MapInfo::Scan();
    for (auto &map : *cached_map_infos) {
        if (map.path.ends_with("/libart.so")) {
            art_inode = map.inode;
            art_dev = map.dev;
            break;
        }
    }

    if (art_dev == 0 || art_inode == 0) {
        /*
         * INFO: If we are here, it means we are too early and libart.so hasn't loaded yet when
         * property_get was called. This doesn't normally happen, but we try again next time
         * just to be safe.
         */

        LOGE("virtual map for libart.so is not cached");

        hooked_unloader = false;

        return;
    } else {
        LOGD("hook_unloader called with libart.so [%zu:%lu]", art_dev, art_inode);
    }
    PLT_HOOK_REGISTER(art_dev, art_inode, pthread_attr_setstacksize);
    hook_commit();
}

static void unhook_functions() {
    // Unhook plt_hook
    for (const auto &[dev, inode, sym, old_func] : *plt_hook_list) {
        if (!lsplt::RegisterHook(dev, inode, sym, *old_func, nullptr)) {
            LOGE("Failed to register plt_hook [%s]", sym);
        }
    }
    delete plt_hook_list;
    if (!hook_commit()) {
        LOGE("Failed to restore plt_hook");
        should_unmap_zygisk = false;
    }

    delete cached_map_infos;
    cached_map_infos = nullptr;
    delete modules;
    modules = nullptr;
    mountinfo_buf.unmap();
    mountinfo_prev.unmap();
    rules_unload();
}

extern "C" int __cxa_atexit(void (*)(void*), void*, void*) {
    return 0;
}
