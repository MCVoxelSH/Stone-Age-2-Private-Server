// Stone Age 2 connection probe: C++ port of sa2_probe_server(2).py.
// Target: C++20. Windows uses WinSock2 and Win32 hotkey/UAC APIs.

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cctype>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <memory>
#include <mutex>
#include <optional>
#include <random>
#include <regex>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <thread>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

#ifdef _WIN32
#  define NOMINMAX
#  include <winsock2.h>
#  include <ws2tcpip.h>
#  include <windows.h>
#  include <shellapi.h>
#  pragma comment(lib, "ws2_32.lib")
using SocketHandle = SOCKET;
static constexpr SocketHandle INVALID_SOCKET_HANDLE = INVALID_SOCKET;
#else
#  include <arpa/inet.h>
#  include <netinet/in.h>
#  include <netdb.h>
#  include <sys/socket.h>
#  include <unistd.h>
using SocketHandle = int;
static constexpr SocketHandle INVALID_SOCKET_HANDLE = -1;
#endif

namespace fs = std::filesystem;
using Bytes = std::vector<std::uint8_t>;
using namespace std::chrono_literals;

static constexpr std::array<int, 5> PORTS = {13101, 13173, 13201, 13273, 13373};
static constexpr std::uint32_t VERSION_SEED = 0;
static constexpr int PROGRAM_VERSION = 180;
static int BATTLE_ANCHOR_X = 25;
static int BATTLE_ANCHOR_Y = 25;
static int BATTLE_MAP_OFFSET_X = -8;
static int BATTLE_MAP_OFFSET_Y = -7;
static constexpr int ALLY_PET_BATTLE_X_SHIFT = -4;
static constexpr int ENEMY_BATTLE_X_SHIFT = 2;
static constexpr int CRITICAL_HIT_CHANCE_PERCENT = 20;
static constexpr int BASE_PLAYER_XP = 1000;
static constexpr int PLAYER_NEXT_XP = 3000;
static constexpr int BASE_PLAYER_LEVEL = 3;
static int WORLD_TIME_SPEED = 720;
static constexpr int SLEEP_HP_REGEN = 5;
static constexpr int SLEEP_SP_REGEN = 5;
static constexpr int SLEEP_ENCOUNTER_CHANCE_PERCENT = 5;
static constexpr int MISS_HI = 5;
static constexpr auto SLEEP_TICK_INTERVAL = 1s;
static constexpr std::size_t CHARACTER_RECORD_SIZE = 0xE3;
static constexpr std::uint32_t TEST_PET_ID = 0x20000001;
static constexpr std::uint16_t ACTIVE_PET_CGNO = 26065;
static const std::string ACTIVE_PET_NAME = "Priestos";
static constexpr std::uint32_t TEST_DROP_MEAT_ITEM_NO = 20001; // 乌力的肉
static constexpr std::uint32_t TEST_DROP_EGG_ITEM_NO  = 20500; // 普通的蛋
static constexpr int TEST_ITEM_DROP_CHANCE_PERCENT = 100; // protocol test
static constexpr std::uint16_t PLAYER_CGNO = 30002; // 3 / Haar 0 / Waffe 0 / Modell 02
static constexpr std::size_t CHARACTER_RECORD_CGNO_OFFSET = 0x22;

// One item is awarded for every defeated enemy.  The deterministic rotation
// makes feeding tests reproducible and covers animal as well as plant food.
static constexpr std::array<std::uint16_t, 11> TEST_FOOD_ITEM_NOS = {
    20001, // URI Fleisch
    20500, // Normales Ei
    20519, // Frischer Fisch
    20709, // Milch
    20625, // Apfel
    20534, // Karotte
    20673, // Gemueseauswahl
    20675, // Bauernhof Grass
    20729, // Samen
    20562, // Pilz
    20820  // Gletschergrass
};

static const char* test_food_ascii_name(std::uint16_t item_no)
{
    switch (item_no) {
    case 20001: return "URI Fleisch";
    case 20500: return "Normales Ei";
    case 20519: return "Frischer Fisch";
    case 20709: return "Milch";
    case 20625: return "Apfel";
    case 20534: return "Karotte";
    case 20673: return "Gemueseauswahl";
    case 20675: return "Bauernhof-Gras";
    case 20729: return "Samen";
    case 20562: return "Pilz";
    case 20820: return "Gletschergras";
    default:    return nullptr;
    }
}

static bool is_ractos_family(std::uint16_t cgno)
{
    // Ractos/Bbaros/Selahtoss/Sebos use 25/26/27/28xxx while the
    // family number stays 037.
    return cgno % 1000u == 37u;
}

static std::optional<std::uint16_t> meat_item_no_for_enemy_cgno(
    std::uint16_t cgno)
{
    // Recovered from item.bin:
    //   item_no = 20001 + family * 4 + variant
    //   CGNO    = (25 + variant) * 1000 + family
    //
    // Example family 037:
    //   25037 -> 20149 Ractos meat
    //   26037 -> 20150 Bbaros meat
    //   27037 -> 20151 Selahtoss meat
    //   28037 -> 20152 Sebos meat
    const int variant = static_cast<int>(cgno / 1000u) - 25;
    const int family = static_cast<int>(cgno % 1000u);

    if (variant < 0 || variant > 3)
        return std::nullopt;

    const int item_no = 20001 + family * 4 + variant;

    // Verified meat entries recovered from item.bin.
    if (item_no < 20001 || item_no > 20209)
        return std::nullopt;

    return static_cast<std::uint16_t>(item_no);
}


static bool is_test_plant_food(std::uint16_t item_no)
{
    switch (item_no) {
    case 20625: // Apfel
    case 20534: // Karotte
    case 20673: // Gemueseauswahl
    case 20675: // Bauernhof Grass
    case 20729: // Samen
    case 20562: // Pilz
    case 20820: // Gletschergrass
        return true;
    default:
        return false;
    }
}

static std::uint32_t feeding_reaction_action(
    std::uint16_t pet_cgno,
    std::uint16_t item_no)
{
    // Verified client reactions in category 1:
    //   15 = happily ate it
    //   19 = does not seem to like it
    //   12 = angry and did not eat it (reserved for rotten/harmful food)
    if (is_ractos_family(pet_cgno) && is_test_plant_food(item_no))
        return 15;

    return 19;
}

// v138: BattleInit group is a TEAM/side field, not merely a flee group.
// Keep every enemy in group 1 (members 0,1,2,...) so they remain on the same
// combat side and keep the correct facing/target orientation.
static constexpr bool ENEMY_SEPARATE_FLEE_GROUPS = false;

// Battle actor IDs used by the 0x0B10 BattleInit records.
static constexpr std::uint32_t PLAYER_BATTLE_ACTOR_ID = 21;
// Own battle pets must keep the same object IDs as the normal pet list.
// Captured pets are persisted starting at 0x20000002 (0x20000001 is the
// separate world/test pet).  The Chinese client's pet battle menu matches the
// current BattleActor object ID directly against the pet-list object ID; using
// synthetic 0x20000015+ IDs makes the menu open only briefly and then skip.
static constexpr std::uint32_t PET_BATTLE_ACTOR_BASE = 0x20000002u;

static constexpr std::size_t CHARACTER_RECORD_APPEARANCE_OFFSET = 0x32;

// Modellnummer 02 -> interner Index 1 in Bits 9–13.
// Alle übrigen Appearance-Komponenten bleiben 0.
static constexpr std::uint16_t PLAYER_APPEARANCE =
static_cast<std::uint16_t>(2u << 9); // 0x0400 = Modell 02

// Source - https://stackoverflow.com/a/17860606
// Posted by ST3, modified by community. See post 'Timeline' for change history
// Retrieved 2026-09-29, License - CC BY-SA 3.0

bool IsUserAdmin()
{
    struct Data
    {
        PACL   pACL;
        PSID   psidAdmin;
        HANDLE hToken;
        HANDLE hImpersonationToken;
        PSECURITY_DESCRIPTOR     psdAdmin;
        Data() : pACL(NULL), psidAdmin(NULL), hToken(NULL),
            hImpersonationToken(NULL), psdAdmin(NULL)
        {
        }
        ~Data()
        {
            if (pACL)
                LocalFree(pACL);
            if (psdAdmin)
                LocalFree(psdAdmin);
            if (psidAdmin)
                FreeSid(psidAdmin);
            if (hImpersonationToken)
                CloseHandle(hImpersonationToken);
            if (hToken)
                CloseHandle(hToken);
        }
    } data;

    BOOL   fReturn = FALSE;
    DWORD  dwStatus;
    DWORD  dwAccessMask;
    DWORD  dwAccessDesired;
    DWORD  dwACLSize;
    DWORD  dwStructureSize = sizeof(PRIVILEGE_SET);

    PRIVILEGE_SET   ps;
    GENERIC_MAPPING GenericMapping;
    SID_IDENTIFIER_AUTHORITY SystemSidAuthority = SECURITY_NT_AUTHORITY;

    const DWORD ACCESS_READ = 1;
    const DWORD ACCESS_WRITE = 2;

    if (!OpenThreadToken(GetCurrentThread(), TOKEN_DUPLICATE | TOKEN_QUERY, TRUE, &data.hToken))
    {
        if (GetLastError() != ERROR_NO_TOKEN)
            return false;

        if (!OpenProcessToken(GetCurrentProcess(), TOKEN_DUPLICATE | TOKEN_QUERY, &data.hToken))
            return false;
    }

    if (!DuplicateToken(data.hToken, SecurityImpersonation, &data.hImpersonationToken))
        return false;

    if (!AllocateAndInitializeSid(&SystemSidAuthority, 2,
        SECURITY_BUILTIN_DOMAIN_RID,
        DOMAIN_ALIAS_RID_ADMINS,
        0, 0, 0, 0, 0, 0, &data.psidAdmin))
        return false;

    data.psdAdmin = LocalAlloc(LPTR, SECURITY_DESCRIPTOR_MIN_LENGTH);
    if (data.psdAdmin == NULL)
        return false;

    if (!InitializeSecurityDescriptor(data.psdAdmin, SECURITY_DESCRIPTOR_REVISION))
        return false;

    // Compute size needed for the ACL.
    dwACLSize = sizeof(ACL) + sizeof(ACCESS_ALLOWED_ACE) + GetLengthSid(data.psidAdmin) - sizeof(DWORD);

    data.pACL = (PACL)LocalAlloc(LPTR, dwACLSize);
    if (data.pACL == NULL)
        return false;

    if (!InitializeAcl(data.pACL, dwACLSize, ACL_REVISION2))
        return false;

    dwAccessMask = ACCESS_READ | ACCESS_WRITE;

    if (!AddAccessAllowedAce(data.pACL, ACL_REVISION2, dwAccessMask, data.psidAdmin))
        return false;

    if (!SetSecurityDescriptorDacl(data.psdAdmin, TRUE, data.pACL, FALSE))
        return false;

    // AccessCheck validates a security descriptor somewhat; set the group
    // and owner so that enough of the security descriptor is filled out 
    // to make AccessCheck happy.

    SetSecurityDescriptorGroup(data.psdAdmin, data.psidAdmin, FALSE);
    SetSecurityDescriptorOwner(data.psdAdmin, data.psidAdmin, FALSE);

    if (!IsValidSecurityDescriptor(data.psdAdmin))
        return false;

    dwAccessDesired = ACCESS_READ;

    GenericMapping.GenericRead = ACCESS_READ;
    GenericMapping.GenericWrite = ACCESS_WRITE;
    GenericMapping.GenericExecute = 0;
    GenericMapping.GenericAll = ACCESS_READ | ACCESS_WRITE;

    if (!AccessCheck(data.psdAdmin, data.hImpersonationToken, dwAccessDesired,
        &GenericMapping, &ps, &dwStructureSize, &dwStatus,
        &fReturn))
    {
        return false;
    }

    return fReturn;
}

static std::uint32_t battle_slot_from_actor_id(
    std::uint32_t actor_id)
{
    if (actor_id == PLAYER_BATTLE_ACTOR_ID)
        return 0x00000000u;

    if (actor_id >= 0x60000015u &&
        actor_id < 0x60000015u + 0x100u)
    {
        const std::uint32_t enemy_index =
            actor_id - 0x60000015u;

        if (ENEMY_SEPARATE_FLEE_GROUPS) {
            // Diagnostic v137: low byte is treated as the flee group.
            // group = 1+i, member = 0 -> 0x00000001, 0x00000002, ...
            return 0x00000001u + enemy_index;
        }

        // V145: restore the older compact enemy Battle-ID layout that was
        // used when individual enemy flee worked and in earlier 0x0B20 orders.
        // Low byte remains group 1; byte 1 remains member/index.
        // enemy 0 => 0x01000001, enemy 1 => 0x01000101, ...
        return 0x01000001u + (enemy_index << 8);
    }

    if (actor_id >= PET_BATTLE_ACTOR_BASE &&
        actor_id < PET_BATTLE_ACTOR_BASE + 0x100u)
    {
        const std::uint32_t pet_index =
            actor_id - PET_BATTLE_ACTOR_BASE;

        // Chinese 2010 developer BattleInit:
        // pet 0 => bytes 00 00 00 01 => 0x01000000
        // pet 1 => bytes 00 01 00 01 => 0x01000100, ...
        return 0x01000000u + (pet_index << 8);
    }

    throw std::runtime_error("Unknown battle actor ID");
}

// V145: flee now uses the same compact ID as BattleInit/attack/defend.
static std::uint32_t enemy_single_flee_battle_id(std::uint32_t actor_id)
{
    return battle_slot_from_actor_id(actor_id);
}

static std::uint32_t actor_id_from_battle_slot(std::uint32_t battle_id)
{
    if (battle_id == 0x00000000u)
        return PLAYER_BATTLE_ACTOR_ID;

    if (ENEMY_SEPARATE_FLEE_GROUPS) {
        // Diagnostic v137: enemy group itself identifies the enemy; member=0.
        if ((battle_id & 0xFFFFFF00u) == 0 &&
            (battle_id & 0xFFu) >= 1u)
        {
            const std::uint32_t index = (battle_id & 0xFFu) - 1u;
            return 0x60000015u + index;
        }
    }
    else {
        // V145 restored layout: low byte group 1, high byte 1,
        // byte 1 is member/index.
        if ((battle_id & 0xFF0000FFu) == 0x01000001u)
        {
            const std::uint32_t index = (battle_id >> 8) & 0xFFu;
            return 0x60000015u + index;
        }
    }

    // Pet: low byte 0, high byte 1; byte 1 is the pet index.
    if ((battle_id & 0xFF0000FFu) == 0x01000000u)
    {
        const std::uint32_t index = (battle_id >> 8) & 0xFFu;
        return PET_BATTLE_ACTOR_BASE + index;
    }

    throw std::runtime_error("Unknown compact battle ID");
}


struct ItemCatalogEntry {
    std::uint16_t item_no = 0;
    std::uint16_t picture_no = 0;
    std::uint16_t category = 1;
    // Local item.bin +0x96.  The Chinese client maps the same property selector
    // (0x9A) to ItemInfo +0xC4 on the network structure.  In the food UI this
    // is the numeric value that was previously displayed as 0.
    std::uint16_t food_value = 0;
    Bytes wire_definition;
};

struct InventoryItemState {
    std::uint32_t object_id = 0;
    std::uint16_t item_no = 0;
    // ItemHave +0x06/+0x08 are equipment-specific state.  The client only
    // interprets them as equipment CGNO/slot while option bit 0x10 is set.
    // Ordinary bag items must keep all three neutral.
    std::uint16_t cgno = 0;
    std::uint16_t category = 0;
    std::uint16_t option = 0;
    std::uint16_t field_0c = 0;
    std::uint16_t field_0e = 0;
    std::uint16_t quantity = 1;  // record +0x10
};

struct ActorConfig {
    std::uint16_t cgno{};
    std::string name;
    int level{};
    int hp{};        // current HP for BattleInit
    int max_hp = 0; // 0 = use hp as max HP (legacy/static configs)
};

struct EncounterPet {
    std::string name;
    int cgno{};
    int family{};
};

struct PlayerStatus {
    std::string name;

    int earned_xp = 0;
    int level = BASE_PLAYER_LEVEL;
    int current_xp = BASE_PLAYER_XP;
    int next_xp = PLAYER_NEXT_XP;
    int skill_points = 0;

    int max_hp = 30 + level * 10;
    int current_hp = 30;

    int max_sp = 100;
    int current_sp = 100;

    bool defending = false;

    std::vector<InventoryItemState> items;
};

struct MoveState {
    std::uint32_t char_id = 21;
    int map = 100;
    int x = 150;
    int y = 150;
    int direction = 4;
    int flags = 0;
    std::uint16_t field_0c = 0x7532;
    std::uint16_t field_0e = 0;
    std::uint32_t field_10 = 0;
    std::uint16_t event_a = 150;
    std::uint16_t event_b = 150;
};

struct BattleEnemyState {
    std::uint32_t actor_id;
    std::uint8_t group;
    std::uint8_t member;
    int hp;
    int max_hp;
    int level;
    std::uint16_t cgno;
    std::string name;
};

struct CapturedPetState {
    std::uint32_t pet_id;
    std::uint16_t slot;
    std::uint16_t cgno;
    int current_hp;
    int max_hp;
    int level;
    int current_xp = 0;
    int next_xp = 100;
    std::string name;
};

struct PlannedBattleAction {
    std::uint32_t actor_id;
    std::uint32_t action;
    std::uint32_t target_id;
    Bytes wire_order;
};

struct Session {
    std::vector<BattleEnemyState> battle_enemies;
    std::vector<PlannedBattleAction> planned_battle_actions;
    SocketHandle socket = INVALID_SOCKET_HANDLE;
    int port = 0;
    std::string peer;
    std::atomic<bool> closing{false};
    std::mutex send_mutex;
    std::mutex state_mutex;

    MoveState move_state;
    std::map<int, std::pair<int, int>> map_positions{{100, {150, 150}}};
    std::string character_name = "Adri";
    bool battle_active = false;
    // 0x0BD1 is a phase-start/sync command, not a "select next actor" command.
    // Set once when the current order-selection phase has been started.
    bool battle_order_phase_started = false;
    // Set when the actor roster changes during a round (currently enemy K.O.).
    // The Chinese client opens the next order phase itself after such a change,
    // so finish_battle_turn must not send a second 0x0BD1 in that case.
    bool battle_roster_changed_this_round = false;
    int battle_enemy_hp = 0;
    int battle_enemy_max_hp = 0;
    int battle_enemy_level = 1;

    // Player first, followed by the battle pets in their BattleInit order.
    // The index is advanced only after the current actor has completed a turn.
    std::vector<std::uint32_t> battle_turn_order;
    // Exact pet object IDs in BattleInit record order.  This is deliberately
    // separate from persistent IDs/slots: released pets can leave object-ID
    // gaps, while the compact battle member index must stay 0..N-1.
    std::vector<std::uint32_t> battle_pet_actor_ids;
    std::size_t battle_turn_index = 0;

    // Actors that are currently in a defending state.  The state survives
    // until that actor gets its next action, so it can protect against all
    // incoming attacks in between.
    std::set<std::uint32_t> battle_defending_actors;

    PlayerStatus player_stats;
    bool player_sleeping = false;
    std::chrono::steady_clock::time_point next_sleep_tick;
    // World packets emitted while leaving a battle can look like movement or
    // even like the sleep/status packet.  Do not allow those resync packets
    // to immediately start another random encounter.
    std::chrono::steady_clock::time_point encounter_block_until{};
    int encounter_battle_map = 12000;
    int encounter_steps = 64;
    std::optional<EncounterPet> encounter_pet;
    std::vector<CapturedPetState> captured_pets;
    std::optional<CapturedPetState> pending_captured_pet;
    std::uint32_t next_captured_pet_id = 0x20000002;
    std::uint16_t next_captured_pet_slot = 0;

    // Minimal inventory state for the verified TCMD_ITEM_HAVE (0x04B0) path.
    // Item object IDs use type/high-nibble 4 in the Chinese client.
    std::vector<InventoryItemState> inventory_items;
    std::uint32_t next_inventory_item_id = 0x40000001u;
    std::size_t next_test_food_drop_index = 0;

    // Reserved for later controlled feeding-reaction tests.
    std::uint32_t pet_feed_reaction_test_index = 0;
};

// Session-aware battle-ID mapping.  Pet object IDs are persistent and may have
// gaps after releases (e.g. 0x20000002, 0x20000004, 0x20000005), so NEVER
// derive their compact BattleInit member from object_id - PET_BATTLE_ACTOR_BASE.
static std::uint32_t battle_slot_from_actor_id(
    const Session& session,
    std::uint32_t actor_id)
{
    if ((actor_id & 0xF0000000u) != 0x20000000u)
        return battle_slot_from_actor_id(actor_id);

    auto it = std::find(
        session.battle_pet_actor_ids.begin(),
        session.battle_pet_actor_ids.end(),
        actor_id);

    if (it == session.battle_pet_actor_ids.end())
        throw std::runtime_error("Unknown pet battle actor ID in current battle");

    const std::uint32_t member = static_cast<std::uint32_t>(
        std::distance(session.battle_pet_actor_ids.begin(), it));

    // Own team/group = 0, member = record index, own-pet marker = high byte 1.
    return 0x01000000u + (member << 8);
}

static std::unordered_map<std::string, std::vector<EncounterPet>> ENCOUNTER_REGIONS;
static std::map<int, std::string> ENCOUNTER_MAP_REGIONS;
static const std::array<std::string, 8> ENCOUNTER_REGION_NAMES = {
    "Badawal", "Glacier of Nol", "Namda Heights", "Nazuth Rocks",
    "Notte", "Sanau Ruins", "Suna Valley", "North Macca"
};

static const std::unordered_map<int, std::string> BATTLE_ACTION_NAMES = {
    {0, "WARTEN"}, {3, "ANGREIFEN"}, {8, "VERTEIDIGEN"},
    {88, "FANGEN"}, {150, "AI"}, {0x99, "FLUECHTEN"}
};

static const std::vector<ActorConfig> ENEMIES = {
    {25065, "Darumatos", 5, 50},
    {26037, "Bbaros", 7, 80},
    {25070, "Enemy C", 6, 65},
};

static std::string read_string(
    const Bytes& data,
    std::size_t offset,
    std::size_t max_length)
{
    std::string result;

    const std::size_t end =
        std::min(data.size(), offset + max_length);

    for (std::size_t i = offset; i < end && data[i] != 0; ++i) {
        result.push_back(static_cast<char>(data[i]));
    }

    return result;
}

static const std::vector<ActorConfig> PETS = {
    {27065, "Sumotos", 5, 50},
    {26037, "Bbaros", 7, 80},
    {25070, "Enemy C", 6, 65},
};

static std::optional<Bytes> created_character_record;
static std::weak_ptr<Session> active_cheat_session;
static std::mutex active_session_mutex;
static std::mutex console_mutex;
static std::mt19937 rng{std::random_device{}()};
static std::mutex rng_mutex;
static std::atomic<bool> running{true};
static std::unordered_map<std::uint16_t, ItemCatalogEntry> ITEM_CATALOG;
static std::optional<fs::path> ITEM_CATALOG_PATH;
static std::optional<fs::path> ITEM_CATALOG_OVERRIDE_PATH;

// Existing low-numbered outdoor/area maps in the client. IDs 5..9 do not
// exist; the numbering intentionally jumps between regional groups.
static std::map<int, std::pair<int, int>> EXPLORATION_MAP_SIZES = {
    {1,{1420,1100}}, {2,{2000,1430}}, {3,{1100,1000}}, {4,{400,300}},
    {11,{1200,1570}}, {12,{1526,1570}}, {13,{1818,800}}, {14,{1990,1400}},
    {21,{1640,1344}}, {22,{1608,1344}}, {23,{100,100}}, {31,{1480,1000}},
    {32,{1482,1030}}, {33,{830,672}}, {34,{906,1164}}, {35,{1040,980}},
    {36,{598,586}}, {37,{100,350}}, {40,{1370,1064}}, {50,{1296,760}}, {60,{106,52}}
};
static std::vector<int> EXPLORATION_MAPS;
static std::map<int, fs::path> EXPLORATION_MAP_FILES;

struct WarpTarget { int map, x, y, direction; };
static const std::map<int, WarpTarget> HALBOL_INTERIORS = {
    {141,{10000,18,31,7}}, {166,{10004,16,27,7}},
    {176,{10006,2,18,1}}, {175,{10020,2,11,1}},
};
static const std::set<int> INTERIOR_MAPS = {10000,10004,10006,10020,10007};
static constexpr int DEN_PORTAL_EVENT = 50000;
static const WarpTarget DEN_ENTRY_TARGET{10007,12,12,4};
static const WarpTarget DEN_RETURN_TARGET{10006,34,16,4};

// The decoded warp.tsv names portal ID 2 as Harubao/Halbol village.
static const std::map<int, WarpTarget> HALBOL_OUTDOOR_EXITS = {
    {49,{1,225,877,1}},{116,{1,300,796,1}},{117,{1,300,796,1}}, {118,{1,300,796,1}}, {119,{1,300,796,1}}, {120,{1,300,796,1}},
    {121,{1,300,796,1}}, {122,{1,300,796,1}}, {123,{1,300,796,1}}, {124,{1,300,796,1}},
};
static const std::map<int, WarpTarget> NORTH_MACCA_EXITS = { {230,{100,51,126,1}},
    {294,{100,116,51,1}}, {295,{100,117,51,1100}}, {296,{100,118,51,1}},
    {297,{100,119,51,1}}, {298,{100,120,51,1}}, {299,{100,121,51,1}},
    {300,{100,122,51,1}}, {301,{100,123,51,1}}, {302,{100,124,51,1}},
    {303,{100,125,51,1}}, {551,{1500,125,51,1}}, {552,{1500,125,51,1}}, {558,{1204,85,55,1}},
    {220,{1000,55,103,1}}, {221,{1000,55,103,1}}, {222,{1000,55,103,1}}
};
static const std::set<int> HALBOL_WORLD_RETURN_EVENTS = {2};

static const std::map<int, WarpTarget> UNNAMEDCAVE_EXITS0 = { { 8,{1,557,332,1} }, { 85,{1001,70,45,1} }, { 76,{1001,70,45,1} } };
static const std::map<int, WarpTarget> UNNAMEDCAVE_EXITS1 = { { 70,{1000,75,45,1} }, { 71,{1000,75,45,1} }, { 14,{1002,22,55,1} }, { 15,{1002,22,55,1} }, { 16,{1002,22,55,1} } };
static const std::map<int, WarpTarget> UNNAMEDCAVE_EXITS2 = { { 14,{1003,21,89,1} },  { 21,{1001,70,45,1} }, { 22,{1001,70,45,1} }, { 23,{1001,70,45,1} } };
static const std::map<int, WarpTarget> UNNAMEDCAVE_EXITS3 = { { 22,{1002,15,94,1} },  { 111,{1004,70,45,1} },  { 112,{1004,70,45,1} } };
static const std::map<int, WarpTarget> UNNAMEDCAVE_EXITS4 = { { 72,{1003,110,54,6} },  { 73,{1003,110,54,6} },  { 111,{1004,110,54,6} } };

static const std::map<int, WarpTarget> BADAWAL_EXITS0 = { { 55,{1,221,632,1} }, { 75,{1001,70,45,1} }, { 76,{1001,70,45,1} } };
static const std::map<int, WarpTarget> BADAWAL_EXITS1 = { { 70,{1000,75,45,1} }, { 71,{1000,75,45,1} }, { 14,{1002,22,55,1} }, { 15,{1002,22,55,1} }, { 16,{1002,22,55,1} } };
static const std::map<int, WarpTarget> BADAWAL_EXITS2 = { { 14,{1003,21,89,1} },  { 21,{1001,70,45,1} }, { 22,{1001,70,45,1} }, { 23,{1001,70,45,1} } };
static const std::map<int, WarpTarget> BADAWAL_EXITS3 = { { 22,{1002,15,94,1} },  { 111,{1004,70,45,1} },  { 112,{1004,70,45,1} } };
static const std::map<int, WarpTarget> BADAWAL_EXITS4 = { { 72,{1003,110,54,6} },  { 73,{1003,110,54,6} },  { 111,{1004,110,54,6} } };

static void log_line(const std::string& s) {
    std::lock_guard lock(console_mutex);
    std::cout << s << std::endl;
}

template <class... T>
static std::string str(T&&... parts) {
    std::ostringstream os;
    (os << ... << std::forward<T>(parts));
    return os.str();
}

static void initialize_battle_turn_order_locked(
    Session& session,
    const std::vector<std::uint32_t>& pet_actor_ids)
{
    session.battle_turn_order.clear();
    session.battle_pet_actor_ids = pet_actor_ids;
    session.planned_battle_actions.clear();
    session.battle_defending_actors.clear();
    session.player_stats.defending = false;
    session.battle_order_phase_started = false;

    session.battle_turn_order.reserve(1 + pet_actor_ids.size());
    session.battle_turn_order.push_back(PLAYER_BATTLE_ACTOR_ID);

    for (std::uint32_t pet_id : pet_actor_ids) {
        // A K.O. pet remains present in BattleInit with HP=0 so the client can
        // render the correct roster, but it must not receive an order slot.
        auto pet_it = std::find_if(
            session.captured_pets.begin(),
            session.captured_pets.end(),
            [&](const CapturedPetState& pet) { return pet.pet_id == pet_id; });

        if (pet_it != session.captured_pets.end() && pet_it->current_hp <= 0) {
            log_line(str("[KAMPF-ZUGFOLGE] Pet 0x",
                [&] { std::ostringstream os; os << std::hex << std::uppercase << pet_id; return os.str(); }(),
                " ist K.O. und wird in der Auswahlphase uebersprungen."));
            continue;
        }

        session.battle_turn_order.push_back(pet_id);
    }

    // The first actor is the player unless the client tells us otherwise in
    // the following 0x0B01 packet.
    session.battle_turn_index = 0;

    std::ostringstream os;
    os << "[KAMPF-ZUGFOLGE] Initialisiert: ";
    for (std::size_t i = 0; i < session.battle_turn_order.size(); ++i) {
        if (i) os << " -> ";
        os << "0x" << std::hex << std::uppercase
           << session.battle_turn_order[i];
    }
    log_line(os.str());
}

static void initialize_battle_turn_order(
    const std::shared_ptr<Session>& session,
    std::size_t pet_count)
{
    std::vector<std::uint32_t> synthetic_pet_ids;
    synthetic_pet_ids.reserve(pet_count);
    for (std::size_t i = 0; i < pet_count; ++i)
        synthetic_pet_ids.push_back(
            PET_BATTLE_ACTOR_BASE + static_cast<std::uint32_t>(i));

    std::lock_guard lock(session->state_mutex);
    initialize_battle_turn_order_locked(*session, synthetic_pet_ids);
}

static void set_battle_current_actor(
    const std::shared_ptr<Session>& session,
    std::uint32_t actor_id)
{
    std::lock_guard lock(session->state_mutex);

    auto it = std::find(
        session->battle_turn_order.begin(),
        session->battle_turn_order.end(),
        actor_id);

    if (it == session->battle_turn_order.end()) {
        log_line(str(
            "[KAMPF-ZUGFOLGE] 0x0B01 meldet unbekannten actor_id=0x",
            [&] {
                std::ostringstream os;
                os << std::hex << std::uppercase << actor_id;
                return os.str();
            }(),
            "; Zugfolge bleibt unveraendert."));
        return;
    }

    session->battle_turn_index =
        static_cast<std::size_t>(
            std::distance(session->battle_turn_order.begin(), it));

    log_line(str(
        "[KAMPF-ZUGFOLGE] Aktueller Actor laut 0x0B01: 0x",
        [&] {
            std::ostringstream os;
            os << std::hex << std::uppercase << actor_id;
            return os.str();
        }()));
}

static bool all_battle_actions_selected(
    const std::shared_ptr<Session>& session)
{
    std::lock_guard lock(session->state_mutex);

    if (session->battle_turn_order.empty())
        return false;

    for (std::uint32_t actor_id : session->battle_turn_order) {
        auto it = std::find_if(
            session->planned_battle_actions.begin(),
            session->planned_battle_actions.end(),
            [&](const PlannedBattleAction& a) {
                return a.actor_id == actor_id;
            });

        if (it == session->planned_battle_actions.end())
            return false;
    }

    return true;
}

static std::vector<std::uint32_t> fill_missing_battle_actions_with_wait(
    const std::shared_ptr<Session>& session)
{
    std::vector<std::uint32_t> missing;

    std::lock_guard lock(session->state_mutex);

    for (std::uint32_t actor_id : session->battle_turn_order) {
        auto it = std::find_if(
            session->planned_battle_actions.begin(),
            session->planned_battle_actions.end(),
            [&](const PlannedBattleAction& a) {
                return a.actor_id == actor_id;
            });

        if (it == session->planned_battle_actions.end()) {
            session->planned_battle_actions.push_back({
                actor_id,
                0,          // WARTEN
                actor_id
            });
            missing.push_back(actor_id);
        }
    }

    return missing;
}

static void store_battle_action(
    const std::shared_ptr<Session>& session,
    std::uint32_t actor_id,
    std::uint32_t action,
    std::uint32_t target_id,
    const Bytes& wire_order = {})
{
    std::lock_guard lock(session->state_mutex);

    auto it = std::find_if(
        session->planned_battle_actions.begin(),
        session->planned_battle_actions.end(),
        [&](const PlannedBattleAction& a) {
            return a.actor_id == actor_id;
        });

    if (it != session->planned_battle_actions.end()) {
        it->action = action;
        it->target_id = target_id;
        it->wire_order = wire_order;
    }
    else {
        session->planned_battle_actions.push_back({
    actor_id,
    action,
    target_id,
    wire_order
            });
    }
}

static std::uint32_t next_battle_actor(
    const std::shared_ptr<Session>& session,
    std::uint32_t current_actor)
{
    std::lock_guard lock(session->state_mutex);

    if (session->battle_turn_order.empty())
        return PLAYER_BATTLE_ACTOR_ID;

    auto it = std::find(
        session->battle_turn_order.begin(),
        session->battle_turn_order.end(),
        current_actor);

    if (it != session->battle_turn_order.end()) {
        session->battle_turn_index =
            static_cast<std::size_t>(
                std::distance(session->battle_turn_order.begin(), it));
    }

    session->battle_turn_index =
        (session->battle_turn_index + 1) % session->battle_turn_order.size();

    return session->battle_turn_order[session->battle_turn_index];
}

static int random_int(int lo, int hi) {
    std::lock_guard lock(rng_mutex);
    std::uniform_int_distribution<int> d(lo, hi);
    return d(rng);
}

template <typename T>
static T clamp_value(T v, T lo, T hi) {
    return std::max(lo, std::min(hi, v));
}

static void close_socket(SocketHandle s) {
    if (s == INVALID_SOCKET_HANDLE) return;
#ifdef _WIN32
    closesocket(s);
#else
    ::close(s);
#endif
}

static std::uint16_t read_u16(const Bytes& b, std::size_t off) {
    if (off + 2 > b.size()) throw std::out_of_range("read_u16");
    return static_cast<std::uint16_t>(b[off] | (std::uint16_t(b[off+1]) << 8));
}
static std::int16_t read_i16(const Bytes& b, std::size_t off) {
    return static_cast<std::int16_t>(read_u16(b, off));
}
static std::uint32_t read_u32(const Bytes& b, std::size_t off) {
    if (off + 4 > b.size()) throw std::out_of_range("read_u32");
    return std::uint32_t(b[off]) |
           (std::uint32_t(b[off+1]) << 8) |
           (std::uint32_t(b[off+2]) << 16) |
           (std::uint32_t(b[off+3]) << 24);
}
static std::int32_t read_i32(const Bytes& b, std::size_t off) {
    return static_cast<std::int32_t>(read_u32(b, off));
}
static void write_u16(Bytes& b, std::size_t off, std::uint16_t v) {
    if (off + 2 > b.size()) throw std::out_of_range("write_u16");
    b[off] = static_cast<std::uint8_t>(v);
    b[off+1] = static_cast<std::uint8_t>(v >> 8);
}
static void write_i16(Bytes& b, std::size_t off, std::int16_t v) {
    write_u16(b, off, static_cast<std::uint16_t>(v));
}
static void write_u32(Bytes& b, std::size_t off, std::uint32_t v) {
    if (off + 4 > b.size()) throw std::out_of_range("write_u32");
    b[off] = static_cast<std::uint8_t>(v);
    b[off+1] = static_cast<std::uint8_t>(v >> 8);
    b[off+2] = static_cast<std::uint8_t>(v >> 16);
    b[off+3] = static_cast<std::uint8_t>(v >> 24);
}
static void write_i32(Bytes& b, std::size_t off, std::int32_t v) {
    write_u32(b, off, static_cast<std::uint32_t>(v));
}
static void append_u16(Bytes& b, std::uint16_t v) {
    b.push_back(static_cast<std::uint8_t>(v));
    b.push_back(static_cast<std::uint8_t>(v >> 8));
}
static void append_u32(Bytes& b, std::uint32_t v) {
    for (int i=0;i<4;++i) b.push_back(static_cast<std::uint8_t>(v >> (8*i)));
}
static Bytes slice(const Bytes& b, std::size_t start, std::size_t count = std::string::npos) {
    if (start >= b.size()) return {};
    std::size_t end = count == std::string::npos ? b.size() : std::min(b.size(), start + count);
    return Bytes(b.begin() + static_cast<std::ptrdiff_t>(start), b.begin() + static_cast<std::ptrdiff_t>(end));
}
static void copy_into(Bytes& dst, std::size_t off, const Bytes& src) {
    if (off + src.size() > dst.size()) throw std::out_of_range("copy_into");
    std::copy(src.begin(), src.end(), dst.begin() + static_cast<std::ptrdiff_t>(off));
}
static void copy_string(Bytes& dst, std::size_t off, const std::string& s, std::size_t max_len, bool nul=true) {
    std::size_t n = std::min(max_len, s.size());
    if (off + n + (nul ? 1 : 0) > dst.size()) throw std::out_of_range("copy_string");
    std::copy_n(reinterpret_cast<const std::uint8_t*>(s.data()), n, dst.begin() + static_cast<std::ptrdiff_t>(off));
    if (nul) dst[off+n] = 0;
}
static Bytes make_packet(std::uint16_t command, const Bytes& payload) {
    if (payload.size() + 6 > 65535) throw std::runtime_error("packet too large");
    Bytes p(6 + payload.size());
    const auto size = static_cast<std::uint16_t>(p.size());
    write_u16(p, 0, size);
    write_u16(p, 2, size);
    write_u16(p, 4, command);
    std::copy(payload.begin(), payload.end(), p.begin()+6);
    return p;
}

static bool send_all(const std::shared_ptr<Session>& session, const Bytes& data) {
    if (!session || session->closing.load()) return false;
    std::lock_guard lock(session->send_mutex);
    std::size_t sent = 0;
    while (sent < data.size()) {
#ifdef _WIN32
        int n = ::send(session->socket,
                       reinterpret_cast<const char*>(data.data()+sent),
                       static_cast<int>(data.size()-sent), 0);
#else
        ssize_t n = ::send(session->socket, data.data()+sent, data.size()-sent, 0);
#endif
        if (n <= 0) {
            session->closing = true;
            return false;
        }
        sent += static_cast<std::size_t>(n);
    }
    return true;
}

static std::string hexline(const Bytes& data, std::size_t limit = 256) {
    std::ostringstream os;
    std::size_t shown = std::min(limit, data.size());
    os << std::uppercase << std::hex << std::setfill('0');
    for (std::size_t i=0;i<shown;++i) {
        if (i) os << ' ';
        os << std::setw(2) << unsigned(data[i]);
    }
    if (data.size() > limit) os << " ... (+" << std::dec << (data.size()-limit) << " Bytes)";
    return os.str();
}

static std::string stamp() {
    auto now = std::chrono::system_clock::now();
    std::time_t t = std::chrono::system_clock::to_time_t(now);
    std::tm tm{};
#ifdef _WIN32
    localtime_s(&tm, &t);
#else
    localtime_r(&t, &tm);
#endif
    std::ostringstream os;
    os << std::put_time(&tm, "%Y-%m-%d_%H-%M-%S");
    return os.str();
}

static std::vector<std::string> parse_csv_line(const std::string& line) {
    std::vector<std::string> out;
    std::string cur;
    bool quoted = false;
    for (std::size_t i=0;i<line.size();++i) {
        char c=line[i];
        if (c=='"') {
            if (quoted && i+1<line.size() && line[i+1]=='"') { cur.push_back('"'); ++i; }
            else quoted=!quoted;
        } else if (c==',' && !quoted) {
            out.push_back(cur); cur.clear();
        } else cur.push_back(c);
    }
    out.push_back(cur);
    return out;
}

static std::string trim(std::string s) {
    auto not_space=[](unsigned char c){return !std::isspace(c);};
    s.erase(s.begin(), std::find_if(s.begin(), s.end(), not_space));
    s.erase(std::find_if(s.rbegin(), s.rend(), not_space).base(), s.end());
    return s;
}

static fs::path executable_path() {
#ifdef _WIN32
    std::wstring buf(32768, L'\0');
    DWORD n=GetModuleFileNameW(nullptr, buf.data(), static_cast<DWORD>(buf.size()));
    buf.resize(n);
    return fs::path(buf);
#else
    std::error_code ec;
    auto p=fs::read_symlink("/proc/self/exe", ec);
    return ec ? fs::current_path() : p;
#endif
}

static fs::path character_state_path() {
    // Return a stable per-user path that survives replacing the probe folder.
#ifdef _WIN32
    const char* local = std::getenv("LOCALAPPDATA");
    fs::path base = local ? fs::path(local) : (fs::path(std::getenv("USERPROFILE") ? std::getenv("USERPROFILE") : ".") / "AppData" / "Local");
#else
    const char* xdg = std::getenv("XDG_DATA_HOME");
    const char* home = std::getenv("HOME");
    fs::path base = xdg ? fs::path(xdg) : (fs::path(home ? home : ".") / ".local" / "share");
#endif
    return base / "StoneAge2Probe" / "character.bin";
}
static fs::path encounter_region_state_path() { return character_state_path().parent_path() / "encounter_map_regions.json"; }
static fs::path captured_pets_state_path() { return character_state_path().parent_path() / "captured_pets.tsv"; }
static fs::path player_progress_path() { return executable_path().parent_path() / "player_stats.json"; }
static fs::path player_position_path() {
    return executable_path().parent_path() / "player_position.json";
}

static Bytes read_binary_file(const fs::path& p) {
    std::ifstream f(p, std::ios::binary);
    if (!f) throw std::runtime_error("cannot open file: " + p.string());
    return Bytes(std::istreambuf_iterator<char>(f), {});
}
static void write_binary_file(const fs::path& p, const Bytes& b) {
    fs::create_directories(p.parent_path());
    std::ofstream f(p, std::ios::binary | std::ios::trunc);
    if (!f) throw std::runtime_error("cannot write file: " + p.string());
    f.write(reinterpret_cast<const char*>(b.data()), static_cast<std::streamsize>(b.size()));
}
static std::string read_text_file(const fs::path& p) {
    std::ifstream f(p, std::ios::binary);
    if (!f) throw std::runtime_error("cannot open file: " + p.string());
    return std::string(std::istreambuf_iterator<char>(f), {});
}
static void write_text_file(const fs::path& p, const std::string& s) {
    if (!p.parent_path().empty()) fs::create_directories(p.parent_path());
    std::ofstream f(p, std::ios::binary | std::ios::trunc);
    if (!f) throw std::runtime_error("cannot write file: " + p.string());
    f << s;
}


static void write_ascii_cstr(Bytes& dst, std::size_t off, const std::string& text, std::size_t field_bytes)
{
    if (off + field_bytes > dst.size())
        throw std::out_of_range("write_ascii_cstr");

    // ItemInfo name/description are byte strings (MBCS/ANSI), not UTF-16.
    // Zero the complete fixed field first so shorter replacements cannot leave
    // bytes from an earlier/raw item.bin string behind.
    std::fill(dst.begin() + static_cast<std::ptrdiff_t>(off),
              dst.begin() + static_cast<std::ptrdiff_t>(off + field_bytes), 0);

    const std::size_t n = std::min(field_bytes ? field_bytes - 1 : 0, text.size());
    std::copy_n(reinterpret_cast<const std::uint8_t*>(text.data()), n,
                dst.begin() + static_cast<std::ptrdiff_t>(off));
}

static Bytes safe_test_food_wire_definition(
    std::uint16_t item_no,
    std::uint16_t picture_no,
    std::uint16_t food_value,
    const char* ascii_name)
{
    // Do not copy the compact local property block into the expanded network
    // structure.  Its fields are not offset-compatible and caused at least the
    // coconut definition to crash the client.  The inventory/feed path only
    // needs a stable ID, picture, food category/value and readable text.
    Bytes def(0x14A, 0);
    write_u16(def, 0x00, item_no);
    write_u16(def, 0x02, picture_no);
    write_ascii_cstr(def, 0x04, ascii_name ? ascii_name : "Test-Nahrung", 0x40);
    write_u16(def, 0x44, 0x13); // food
    write_u16(def, 0xC4, food_value);
    write_ascii_cstr(def, 0xC6, "Test-Nahrung", 0x78);
    return def;
}

static Bytes item_wire_definition_from_local_record(const Bytes& record)
{
    if (record.size() != 0x128)
        throw std::runtime_error("item.bin record must be 0x128 bytes");

    // Local 2010 item.bin record (after XOR 0xFF decoding):
    //   +0x00 WORD  ItemNo
    //   +0x02       fixed MBCS/ANSI name field
    //   +0x34..97   compact properties
    //   +0x96 WORD  property selector 0x9A (food/calorie value in the UI)
    //   +0x98       fixed MBCS/ANSI description field
    //   +0x11A WORD inventory picture/resource number
    //
    // TCMD_ITEM_INFO uses an expanded 0x14A-byte structure.  Reverse mapping
    // of the client's local and network property renderers gives:
    //   local +0x96  -> wire +0xC4
    // and the inventory renderer reads the picture/resource from wire +0x02.
    Bytes def(0x14A, 0);

    const std::uint16_t item_no = read_u16(record, 0x00);
    const std::uint16_t picture_no = read_u16(record, 0x11A);
    const std::uint16_t food_value = read_u16(record, 0x96);

    write_u16(def, 0x00, item_no);
    write_u16(def, 0x02, picture_no);

    // Local name is already a byte/MBCS string.  The local field is 0x32
    // bytes, while ItemInfo reserves 0x40 bytes at +0x04.  Copy it verbatim
    // and leave the larger destination field zero-padded.
    std::copy_n(record.begin() + 0x02, 0x32, def.begin() + 0x04);
    def[0x42] = 0;
    def[0x43] = 0;

    // Preserve the compact property area used by the older/local structure.
    // Not every network field has a 1:1 offset because ItemInfo is expanded;
    // specifically mapped fields are written separately below.
    std::copy_n(record.begin() + 0x34, 0x64, def.begin() + 0x44);

    // Property 0x9A: local renderer reads record +0x96, while the network
    // renderer reads ItemInfo +0xC4 for the same selector.
    write_u16(def, 0xC4, food_value);

    // Description is likewise a 0x78-byte MBCS/ANSI field.
    std::copy_n(record.begin() + 0x98, 0x78, def.begin() + 0xC6);
    def[0x13C] = 0;
    def[0x13D] = 0;

    return def;
}

static ItemCatalogEntry fallback_item_definition(std::uint16_t item_no)
{
    ItemCatalogEntry entry;
    entry.item_no = item_no;
    entry.wire_definition.assign(0x14A, 0);

    if (item_no == TEST_DROP_MEAT_ITEM_NO) {
        // Protocol fallback only; retail values should come from the client's
        // decoded item.bin whenever it is available.
        entry.picture_no = 180;
        entry.category = 1;
        entry.food_value = 50;
        write_ascii_cstr(entry.wire_definition, 0x04, "Fleisch", 0x40);
        write_ascii_cstr(entry.wire_definition, 0xC6, "Test-Nahrung", 0x78);
    }
    else if (item_no == TEST_DROP_EGG_ITEM_NO) {
        entry.picture_no = 200;
        entry.category = 1;
        entry.food_value = 50;
        write_ascii_cstr(entry.wire_definition, 0x04, "Ei", 0x40);
        write_ascii_cstr(entry.wire_definition, 0xC6, "Test-Ei", 0x78);
    }

    write_u16(entry.wire_definition, 0x00, item_no);
    write_u16(entry.wire_definition, 0x02, entry.picture_no);
    write_u16(entry.wire_definition, 0x44, entry.category);
    write_u16(entry.wire_definition, 0xC4, entry.food_value);
    return entry;
}

static void load_item_catalog()
{
    ITEM_CATALOG.clear();
    ITEM_CATALOG_PATH.reset();

    std::vector<fs::path> roots = {
        fs::current_path(),
        executable_path().parent_path()
    };

    fs::path parent = executable_path().parent_path();
    for (int i = 0; i < 6 && parent.has_parent_path(); ++i) {
        roots.push_back(parent);
        parent = parent.parent_path();
    }

    std::vector<fs::path> candidates;

    // V161: an explicit --item-bin path wins over auto-discovery.  The option
    // may point either to item.bin itself or to the client's data directory.
    if (ITEM_CATALOG_OVERRIDE_PATH) {
        std::error_code ec;
        fs::path explicit_path = *ITEM_CATALOG_OVERRIDE_PATH;
        if (fs::is_directory(explicit_path, ec))
            explicit_path /= "item.bin";
        candidates.push_back(explicit_path);
    }

    for (const auto& root : roots) {
        candidates.push_back(root / "data" / "item.bin");
        candidates.push_back(root / "item.bin");
    }

    std::set<fs::path> seen;
    for (const auto& candidate : candidates) {
        std::error_code ec;
        fs::path p = fs::weakly_canonical(candidate, ec);
        if (ec || !seen.insert(p).second || !fs::is_regular_file(p))
            continue;

        try {
            Bytes encoded = read_binary_file(p);
            if (encoded.empty() || encoded.size() % 0x128 != 0)
                continue;

            for (auto& b : encoded)
                b ^= 0xFF;

            const std::size_t count = encoded.size() / 0x128;
            for (std::size_t i = 0; i < count; ++i) {
                Bytes record(
                    encoded.begin() + static_cast<std::ptrdiff_t>(i * 0x128),
                    encoded.begin() + static_cast<std::ptrdiff_t>((i + 1) * 0x128));

                const std::uint16_t item_no = read_u16(record, 0);
                if (!item_no)
                    continue;

                ItemCatalogEntry entry;
                entry.item_no = item_no;
                // V166: the client's local inventory renderer reads its icon
                // resource from record +0x11A (not +0x36).
                entry.picture_no = read_u16(record, 0x11A);
                entry.category = read_u16(record, 0x34);
                if (entry.category < 1 || entry.category > 19)
                    entry.category = 1;
                entry.food_value = read_u16(record, 0x96);
                entry.wire_definition = item_wire_definition_from_local_record(record);

                // The supplied German item.bin stores its local strings as
                // UTF-16LE, while TCMD_ITEM_INFO uses one-byte text fields.
                // More importantly, the compact local property block is not
                // layout-compatible with the expanded network record.  Build
                // controlled minimal definitions for every test food.
                if (const char* safe_name = test_food_ascii_name(item_no)) {
                    entry.category = 0x13;
                    entry.wire_definition = safe_test_food_wire_definition(
                        item_no,
                        entry.picture_no,
                        entry.food_value,
                        safe_name);
                }

                ITEM_CATALOG[item_no] = std::move(entry);
            }

            ITEM_CATALOG_PATH = p;
            log_line(str(
                "[ITEM-KATALOG] ", ITEM_CATALOG.size(),
                " Eintraege aus ", p.string(), " geladen."));

            auto log_known = [&](std::uint16_t item_no, const char* label) {
                auto it = ITEM_CATALOG.find(item_no);
                if (it != ITEM_CATALOG.end())
                    log_line(str("[ITEM-KATALOG V167] ", label, " ItemNo=", item_no,
                        ", Bild(+0x11A)=", it->second.picture_no,
                        ", Kategorie(+0x34)=", it->second.category,
                        ", FoodValue(+0x96 -> wire+0xC4)=", it->second.food_value));
            };
            log_known(TEST_DROP_MEAT_ITEM_NO, "Fleisch");
            log_known(TEST_DROP_EGG_ITEM_NO, "Ei");
            return;
        }
        catch (const std::exception& e) {
            log_line(str("[WARNUNG] item.bin konnte nicht geladen werden: ", e.what()));
        }
    }

    // The two confirmed 2010 CN item numbers still work as protocol-test
    // definitions if item.bin is not beside/above the probe executable.
    ITEM_CATALOG.emplace(TEST_DROP_MEAT_ITEM_NO, fallback_item_definition(TEST_DROP_MEAT_ITEM_NO));
    ITEM_CATALOG.emplace(TEST_DROP_EGG_ITEM_NO, fallback_item_definition(TEST_DROP_EGG_ITEM_NO));
    log_line("[WARNUNG] item.bin nicht gefunden; verwende minimale Fleisch/Ei-Definitionen.");
}

static const ItemCatalogEntry& item_catalog_entry(std::uint16_t item_no)
{
    auto it = ITEM_CATALOG.find(item_no);
    if (it != ITEM_CATALOG.end())
        return it->second;

    auto [inserted, ok] = ITEM_CATALOG.emplace(
        item_no, fallback_item_definition(item_no));
    (void)ok;
    return inserted->second;
}



static std::string escape_pet_state_field(const std::string& value) {
    std::string out;
    out.reserve(value.size());
    for (char c : value) {
        switch (c) {
        case '\\': out += "\\\\"; break;
        case '\t': out += "\\t"; break;
        case '\r': out += "\\r"; break;
        case '\n': out += "\\n"; break;
        default: out.push_back(c); break;
        }
    }
    return out;
}

static std::string unescape_pet_state_field(const std::string& value) {
    std::string out;
    out.reserve(value.size());
    for (std::size_t i = 0; i < value.size(); ++i) {
        if (value[i] != '\\' || i + 1 >= value.size()) {
            out.push_back(value[i]);
            continue;
        }

        char n = value[++i];
        switch (n) {
        case 't': out.push_back('\t'); break;
        case 'r': out.push_back('\r'); break;
        case 'n': out.push_back('\n'); break;
        case '\\': out.push_back('\\'); break;
        default:
            out.push_back('\\');
            out.push_back(n);
            break;
        }
    }
    return out;
}

static int pet_next_xp_for_level(int level) {
    // Temporary progression curve until the retail table is recovered.
    // It is deliberately small enough to make pet level-up testing practical.
    level = std::max(1, level);
    return std::max(100, level * 100);
}

static int award_pet_xp(CapturedPetState& pet, int xp_gain) {
    pet.current_xp = std::max(0, pet.current_xp) + std::max(0, xp_gain);
    if (pet.next_xp <= 0)
        pet.next_xp = pet_next_xp_for_level(pet.level);

    int levels = 0;
    while (pet.current_xp >= pet.next_xp) {
        pet.current_xp -= pet.next_xp;
        ++pet.level;
        ++levels;
        const int old_max_hp = pet.max_hp;
        pet.max_hp = std::max(pet.max_hp + 10, 30 + pet.level * 10);
        pet.current_hp = std::min(pet.max_hp, pet.current_hp + (pet.max_hp - old_max_hp));
        pet.next_xp = pet_next_xp_for_level(pet.level);
    }
    return levels;
}

static void save_captured_pets_state(const std::vector<CapturedPetState>& pets) {
    fs::path path = captured_pets_state_path();
    fs::create_directories(path.parent_path());

    fs::path tmp = path;
    tmp += ".tmp";

    std::ofstream f(tmp, std::ios::binary | std::ios::trunc);
    if (!f)
        throw std::runtime_error("cannot write captured pets: " + tmp.string());

    f << "# pet_id\tslot\tcgno\tlevel\tcurrent_xp\tnext_xp\tmax_hp\tname\n";
    for (const auto& pet : pets) {
        f << pet.pet_id << '\t'
          << pet.slot << '\t'
          << pet.cgno << '\t'
          << pet.level << '\t'
          << pet.current_xp << '\t'
          << pet.next_xp << '\t'
          << pet.max_hp << '\t'
          << escape_pet_state_field(pet.name) << '\n';
    }
    f.close();

    std::error_code ec;
    fs::remove(path, ec);
    ec.clear();
    fs::rename(tmp, path, ec);
    if (ec)
        throw std::runtime_error("cannot replace captured pets file: " + ec.message());

    log_line(str(
        "[PERSISTENZ] ", pets.size(),
        " gefangene Pets gespeichert: ", path.string()));
}

static std::vector<CapturedPetState> load_captured_pets_state() {
    std::vector<CapturedPetState> pets;
    fs::path path = captured_pets_state_path();

    if (!fs::exists(path)) {
        log_line(str(
            "[PERSISTENZ] Noch keine gespeicherten Pets vorhanden (",
            path.string(), ")."));
        return pets;
    }

    std::ifstream f(path, std::ios::binary);
    if (!f)
        throw std::runtime_error("cannot read captured pets: " + path.string());

    std::string line;
    std::size_t line_no = 0;
    while (std::getline(f, line)) {
        ++line_no;
        if (!line.empty() && line.back() == '\r')
            line.pop_back();
        if (line.empty() || line[0] == '#')
            continue;

        std::vector<std::string> fields;
        std::size_t start = 0;
        for (std::size_t i = 0; i <= line.size(); ++i) {
            if (i == line.size() || line[i] == '\t') {
                fields.push_back(line.substr(start, i - start));
                start = i + 1;
            }
        }

        // Legacy V145 format has 5 columns; V146 has 8.
        if (fields.size() != 5 && fields.size() != 8) {
            log_line(str(
                "[WARNUNG] Ungueltige Pet-Zeile ", line_no,
                " in ", path.string(), "; uebersprungen."));
            continue;
        }

        try {
            CapturedPetState pet{};
            pet.pet_id = static_cast<std::uint32_t>(std::stoul(fields[0]));
            pet.slot = static_cast<std::uint16_t>(std::stoul(fields[1]));
            pet.cgno = static_cast<std::uint16_t>(std::stoul(fields[2]));
            pet.level = std::max(1, std::stoi(fields[3]));

            if (fields.size() == 8) {
                pet.current_xp = std::max(0, std::stoi(fields[4]));
                pet.next_xp = std::max(1, std::stoi(fields[5]));
                pet.max_hp = std::max(1, std::stoi(fields[6]));
                // Preserve the old reconnect behaviour: pets start a new
                // session fully healed until the real healing system exists.
                pet.current_hp = pet.max_hp;
                pet.name = unescape_pet_state_field(fields[7]);
            }
            else {
                pet.current_xp = 0;
                pet.next_xp = pet_next_xp_for_level(pet.level);
                pet.max_hp = 30 + pet.level * 10;
                pet.current_hp = pet.max_hp;
                pet.name = unescape_pet_state_field(fields[4]);
            }

            if (pet.pet_id == 0 || pet.name.empty())
                throw std::runtime_error("missing pet id/name");

            pets.push_back(std::move(pet));
        }
        catch (const std::exception& e) {
            log_line(str(
                "[WARNUNG] Gespeichertes Pet in Zeile ", line_no,
                " ist ungueltig (", e.what(), "); uebersprungen."));
        }
    }

    log_line(str(
        "[PERSISTENZ] ", pets.size(),
        " gefangene Pets geladen: ", path.string()));
    return pets;
}

static bool compact_captured_pet_slots(std::vector<CapturedPetState>& pets) {
    // The client treats the 0x0462 slot as an index into a compact pet array.
    // Holes such as 0,2,3 after releasing slot 1 leave its secondary UI state
    // inconsistent and can make persisted 0x0462 records invalid on next login.
    std::stable_sort(
        pets.begin(),
        pets.end(),
        [](const CapturedPetState& a, const CapturedPetState& b) {
            return a.slot < b.slot;
        });

    bool changed = false;
    for (std::size_t i = 0; i < pets.size(); ++i) {
        const auto wanted = static_cast<std::uint16_t>(i);
        if (pets[i].slot != wanted) {
            pets[i].slot = wanted;
            changed = true;
        }
    }
    return changed;
}

static void restore_captured_pets(Session& session) {
    session.captured_pets = load_captured_pets_state();
    session.pending_captured_pet.reset();

    // Repair old save files created by the release code that left slot holes.
    const bool repaired_slots = compact_captured_pet_slots(session.captured_pets);
    if (repaired_slots) {
        try {
            save_captured_pets_state(session.captured_pets);
            log_line("[PET-SLOT-REPARATUR] Gespeicherte Pet-Slots auf 0..N-1 komprimiert und gespeichert.");
        }
        catch (const std::exception& e) {
            log_line(str("[WARNUNG] Reparierte Pet-Slots konnten nicht gespeichert werden: ", e.what()));
        }
    }

    std::uint32_t max_id = 0x20000001u;
    for (const auto& pet : session.captured_pets)
        max_id = std::max(max_id, pet.pet_id);

    session.next_captured_pet_id =
        max_id < 0xFFFFFFFFu ? std::max(0x20000002u, max_id + 1u)
                             : 0x20000002u;

    // Slots are list indices, not monotonically increasing object IDs.
    session.next_captured_pet_slot = static_cast<std::uint16_t>(
        std::min<std::size_t>(65535, session.captured_pets.size()));

    log_line(str(
        "[PERSISTENZ] Naechste Pet-ID=0x",
        [&] {
            std::ostringstream os;
            os << std::hex << std::uppercase
               << session.next_captured_pet_id;
            return os.str();
        }(),
        ", naechster kompakter Slot=", session.next_captured_pet_slot));
}

static void rebuild_exploration_maps() {
    EXPLORATION_MAPS.clear();
    for (const auto& [id, size] : EXPLORATION_MAP_SIZES) EXPLORATION_MAPS.push_back(id);
}

static void configure_map_catalog(const std::optional<fs::path>& explicit_directory = std::nullopt) {
    // Discover MAP files and replace the built-in fallback catalogue.
    std::vector<fs::path> candidates;
    if (explicit_directory) candidates.push_back(*explicit_directory);
    else {
        std::vector<fs::path> roots = {fs::current_path(), executable_path().parent_path()};
        fs::path p=executable_path().parent_path();
        for (int i=0;i<5 && p.has_parent_path();++i) { roots.push_back(p); p=p.parent_path(); }
        for (const auto& root: roots) {
            candidates.push_back(root/"mapdata");
            candidates.push_back(root/"data"/"mapdata");
            candidates.push_back(root/"map"/"mapdata");
        }
    }
    std::set<fs::path> seen;
    for (auto directory: candidates) {
        std::error_code ec;
        directory=fs::weakly_canonical(directory, ec);
        if (ec || !seen.insert(directory).second || !fs::is_directory(directory)) continue;
        std::map<int,std::pair<int,int>> sizes;
        std::map<int,fs::path> files;
        for (const auto& entry: fs::directory_iterator(directory)) {
            if (!entry.is_regular_file() || entry.path().extension() != ".bin") continue;
            try {
                Bytes h=read_binary_file(entry.path());
                if (h.size()<16 || h[0]!='M' || h[1]!='A' || h[2]!='P' || h[3]!=0) continue;
                int map_id=read_u16(h,10), width=read_u16(h,12), height=read_u16(h,14);
                if (width && height) { sizes[map_id]={width,height}; files[map_id]=entry.path(); }
            } catch (...) {}
        }
        if (!sizes.empty()) {
            EXPLORATION_MAP_SIZES=std::move(sizes);
            EXPLORATION_MAP_FILES=std::move(files);
            rebuild_exploration_maps();
            log_line(str("[KARTENKATALOG] ", EXPLORATION_MAP_FILES.size(), " MAP-Dateien erkannt: ", directory.string()));
            return;
        }
    }
    rebuild_exploration_maps();
    if (explicit_directory) log_line(str("[WARNUNG] Keine gueltigen MAP-Dateien in ", explicit_directory->string(), "; verwende eingebauten Katalog."));
    else log_line("[KARTENKATALOG] Kein mapdata-Ordner automatisch gefunden; verwende eingebauten Katalog. Optional: --mapdata PFAD");
}

static std::tuple<int,int,std::string> default_map_position(int map_id) {
    // Choose a likely walkable point using a JUM2 portal, else map centre.
    auto it=EXPLORATION_MAP_SIZES.find(map_id);
    if (it==EXPLORATION_MAP_SIZES.end()) return {150,150,"Fallback"};
    auto [width,height]=it->second;
    auto fp=EXPLORATION_MAP_FILES.find(map_id);
    if (fp!=EXPLORATION_MAP_FILES.end()) {
        try {
            Bytes data=read_binary_file(fp->second);
            const std::array<std::uint8_t,4> jum2 = {'J','U','M','2'};
            for (std::size_t off=0; off+14<=data.size();) {
                auto found=std::search(data.begin()+static_cast<std::ptrdiff_t>(off), data.end(),
                                       jum2.begin(), jum2.end());
                if (found==data.end()) break;
                off=static_cast<std::size_t>(std::distance(data.begin(),found));
                std::uint32_t chunk_size=read_u32(data,off+4);
                std::uint32_t count=read_u32(data,off+10);
                std::size_t records_at=off+14;
                if (chunk_size>=14 && count && records_at+count*11<=data.size()) {
                    for (std::uint32_t i=0;i<count;++i) {
                        int x=read_u16(data,records_at+i*11+2), y=read_u16(data,records_at+i*11+4);
                        if (x>=width || y>=height) continue;
                        x += x < width/2 ? 8 : -8;
                        y += y < height/2 ? 8 : -8;
                        x=clamp_value(x,0,width-1); y=clamp_value(y,0,height-1);
                        return {x,y,"JUM2-Portal"};
                    }
                }
                off += 4;
            }
        } catch (const std::exception& e) {
            log_line(str("[WARNUNG] Startpunktanalyse fuer Karte ",map_id,": ",e.what()));
        }
    }
    return {width/2,height/2,"Kartenmitte"};
}

static void load_encounter_catalog() {
    // Load Companion pet CGNOs and remembered map assignments.
    ENCOUNTER_REGIONS.clear();
    std::vector<fs::path> candidates = {
        executable_path().parent_path()/"companion_pet_cgno_map.csv",
        fs::current_path()/"companion_pet_cgno_map.csv"
    };
    std::optional<fs::path> catalog;
    for (const auto& p: candidates) if (fs::is_regular_file(p)) { catalog=p; break; }
    if (catalog) {
        try {
            std::ifstream f(*catalog);
            std::string line;
            if (!std::getline(f,line)) throw std::runtime_error("empty CSV");
            auto headers=parse_csv_line(line);
            std::map<std::string,std::size_t> idx;
            for (std::size_t i=0;i<headers.size();++i) idx[trim(headers[i])]=i;
            std::size_t count=0;
            while (std::getline(f,line)) {
                auto cols=parse_csv_line(line);
                if (cols.empty()) continue;
                auto get=[&](const std::string& key)->std::string {
                    auto it=idx.find(key); if (it==idx.end() || it->second>=cols.size()) throw std::runtime_error("missing CSV column " + key);
                    return trim(cols[it->second]);
                };
                std::string region=get("region");
                ENCOUNTER_REGIONS[region].push_back({get("name"),std::stoi(get("cgno")),std::stoi(get("family"))});
                ++count;
            }
            log_line(str("[BEGEGNUNGEN] ",count," Pets aus ",catalog->filename().string()," geladen."));
        } catch (const std::exception& e) {
            log_line(str("[WARNUNG] Begegnungskatalog ungueltig: ",e.what()));
        }
    } else {
        log_line("[WARNUNG] companion_pet_cgno_map.csv fehlt; automatische Begegnungen sind deaktiviert.");
    }

    ENCOUNTER_MAP_REGIONS.clear();
    try {
        std::string raw=read_text_file(encounter_region_state_path());
        std::regex pair_re(R"JSON("([0-9]+)"\s*:\s*"([^"]*)")JSON");
        for (std::sregex_iterator it(raw.begin(),raw.end(),pair_re), end; it!=end; ++it) {
            int map_id=std::stoi((*it)[1].str());
            std::string region=(*it)[2].str();
            if (ENCOUNTER_REGIONS.count(region)) ENCOUNTER_MAP_REGIONS[map_id]=region;
        }
        if (!ENCOUNTER_MAP_REGIONS.empty()) log_line(str("[BEGEGNUNGEN] ",ENCOUNTER_MAP_REGIONS.size()," gespeicherte Karten-Zuordnungen geladen."));
    } catch (...) {}
}

static void save_encounter_map_regions() {
    fs::path p=encounter_region_state_path();
    fs::create_directories(p.parent_path());
    std::ostringstream os; os << "{\n";
    std::size_t i=0;
    for (const auto& [map_id,region]: ENCOUNTER_MAP_REGIONS) {
        os << "  \"" << map_id << "\": \"" << region << "\"";
        if (++i<ENCOUNTER_MAP_REGIONS.size()) os << ',';
        os << '\n';
    }
    os << "}\n";
    write_text_file(p,os.str());
}

static std::optional<Bytes> load_character_state() {
    fs::path p=character_state_path();
    if (!fs::exists(p)) {
        log_line(str("Kein gespeicherter Charakter vorhanden (",p.string(),")."));
        return std::nullopt;
    }
    try {
        Bytes r=read_binary_file(p);
        if (r.size()!=CHARACTER_RECORD_SIZE) {
            log_line(str("[WARNUNG] Ungueltige Charakterdatei (",r.size()," statt ",CHARACTER_RECORD_SIZE," Bytes); sie wird ignoriert: ",p.string()));
            return std::nullopt;
        }
        std::string name;
        for (std::size_t i=2;i<r.size() && r[i];++i) name.push_back(static_cast<char>(r[i]));
        log_line(str("Gespeicherter Charakter geladen: '",name,"' (",p.string(),")"));
        return r;
    } catch (const std::exception& e) {
        log_line(str("[WARNUNG] Charakterdatei konnte nicht gelesen werden: ",e.what()));
        return std::nullopt;
    }
}

static void save_character_state(const Bytes& record) {
    if (record.size()!=CHARACTER_RECORD_SIZE) throw std::runtime_error("character record must be exactly 0xE3 bytes");
    fs::path p=character_state_path();
    fs::create_directories(p.parent_path());
    fs::path tmp=p; tmp += ".tmp";
    write_binary_file(tmp,record);
    std::error_code ec; fs::remove(p,ec); fs::rename(tmp,p);
    log_line(str("[PERSISTENZ] Charakter gespeichert: ",p.string()));
}

static PlayerStatus load_player_progress() {
    PlayerStatus p;
    try {
        std::string raw=read_text_file(player_progress_path());
        auto value=[&](const std::string& key)->std::optional<int> {
            std::regex re("\\\""+key+"\\\"\\s*:\\s*(-?[0-9]+)");
            std::smatch m; if (std::regex_search(raw,m,re)) return std::stoi(m[1].str());
            return std::nullopt;
        };
        int earned=std::max(0,value("earned_xp").value_or(value("xp").value_or(0)));
        p.earned_xp=earned;
        p.level=std::max(BASE_PLAYER_LEVEL,value("level").value_or(BASE_PLAYER_LEVEL));
        p.current_xp=std::max(0,value("current_xp").value_or(BASE_PLAYER_XP+earned));
        p.next_xp=std::max(1,value("next_xp").value_or(std::max(PLAYER_NEXT_XP,p.level*1000)));
        p.skill_points=std::max(0,value("skill_points").value_or(0));
        p.max_hp = std::max(1, value("max_hp").value_or(30));
        p.current_hp = clamp_value(
            value("current_hp").value_or(p.max_hp),
            0,
            p.max_hp);
        p.max_sp = std::max(1, value("max_sp").value_or(100));
        p.current_sp = clamp_value(
            value("current_sp").value_or(p.max_sp),
            0,
            p.max_sp);

        std::regex item_regex(
            R"(\{\s*"item_no"\s*:\s*([0-9]+)\s*,\s*"amount"\s*:\s*([0-9]+)\s*\})");

        for (std::sregex_iterator it(raw.begin(), raw.end(), item_regex), end;
            it != end;
            ++it)
        {
            const unsigned long parsed_item_no =
                std::stoul((*it)[1].str());

            const unsigned long parsed_amount =
                std::stoul((*it)[2].str());

            if (parsed_item_no > std::numeric_limits<std::uint16_t>::max())
                continue;

            InventoryItemState item{};

            item.item_no =
                static_cast<std::uint16_t>(parsed_item_no);

            item.quantity = static_cast<std::uint16_t>(
                std::clamp<unsigned long>(
                    parsed_amount,
                    1,
                    std::numeric_limits<std::uint16_t>::max()));

            // Derzeit werden nur deine Futter-Drops gespeichert.
            item.cgno = 0;
            item.category = 0x13;
            item.option = 0x02;
            item.field_0c = 0;
            item.field_0e = 0;

            // Wird für jede neue Sitzung neu vergeben.
            item.object_id = 0;

            if (p.items.size() < 0x28)
                p.items.push_back(item);
        }


    } catch (...) {}
    return p;
}

static void save_player_progress(const PlayerStatus& p) {
    std::ostringstream os;
    os << "{\n"
        << "  \"current_xp\": " << p.current_xp << ",\n"
        << "  \"earned_xp\": " << p.earned_xp << ",\n"
        << "  \"level\": " << p.level << ",\n"
        << "  \"next_xp\": " << p.next_xp << ",\n"
        << "  \"skill_points\": " << p.skill_points << ",\n"
        << "  \"max_hp\": " << p.max_hp << ",\n"
        << "  \"current_hp\": " << p.current_hp << ",\n"
        << "  \"max_sp\": " << p.max_sp << ",\n"
        << "  \"current_sp\": " << p.current_sp << ",\n"
        << "  \"inventory\": [\n";

    for (std::size_t i = 0; i < p.items.size(); ++i)
    {
        const auto& item = p.items[i];

        os << "    {\"item_no\": " << item.item_no
            << ", \"amount\": " << item.quantity << "}";

        if (i + 1 < p.items.size())
            os << ",";

        os << "\n";
    }

    os << "  ]\n"
        << "}\n";
 
    write_text_file(player_progress_path(),os.str());
}

static void save_player_position(const MoveState& state) {
    std::ostringstream os;

    os << "{\n"
        << "  \"map\": " << state.map << ",\n"
        << "  \"x\": " << state.x << ",\n"
        << "  \"y\": " << state.y << ",\n"
        << "  \"direction\": " << state.direction << "\n"
        << "}\n";

    write_text_file(player_position_path(), os.str());

    log_line(str(
        "[PERSISTENZ] Position gespeichert: Karte ",
        state.map,
        ", Position ",
        state.x,
        ":",
        state.y,
        ", Richtung ",
        state.direction));
}

static MoveState load_player_position() {
    MoveState state;

    try {
        std::string raw = read_text_file(player_position_path());

        auto value = [&](const std::string& key) -> std::optional<int> {
            std::regex re("\\\"" + key + "\\\"\\s*:\\s*(-?[0-9]+)");
            std::smatch match;

            if (std::regex_search(raw, match, re))
                return std::stoi(match[1].str());

            return std::nullopt;
            };

        state.map = value("map").value_or(100);
        state.x = value("x").value_or(150);
        state.y = value("y").value_or(150);
        state.direction = value("direction").value_or(4);

        log_line(str(
            "[PERSISTENZ] Position geladen: Karte ",
            state.map,
            ", Position ",
            state.x,
            ":",
            state.y,
            ", Richtung ",
            state.direction));
    }
    catch (...) {
        log_line(
            "[PERSISTENZ] Keine gespeicherte Position gefunden; "
            "verwende Startposition 100:150:150.");
    }

    return state;
}

static std::pair<PlayerStatus,int> award_player_xp(const PlayerStatus& progress, int xp_gain) {
    // Add XP and derive level, next threshold and unspent points together.
    PlayerStatus u=progress;
    int gain=std::max(0,xp_gain);
    u.earned_xp=std::max(0,u.earned_xp)+gain;
    u.current_xp=std::max(0,u.current_xp)+gain;
    int levels=0;
    while (u.current_xp>=u.next_xp) {
        ++u.level; ++levels; ++u.skill_points;
        u.next_xp=std::max(u.next_xp+1,u.level*1000);
    }
    return {u,levels};
}

static void apply_compressed_move(const Bytes& payload, MoveState& state) {
    // Decode command 0x0412 exactly as the client routine at 0x5CE239.
    if (payload.size()<7) throw std::runtime_error("compressed move payload too short");
    std::uint8_t mask=payload[0];
    state.char_id=read_u32(payload,1);
    std::size_t pos=5;
    if (mask&0x01) { state.map=read_u16(payload,pos); pos+=2; }
    if (mask&0x02) { state.x=read_i16(payload,pos); state.y=read_i16(payload,pos+2); pos+=4; }
    else {
        if (pos+2>payload.size()) throw std::runtime_error("compressed move relative delta missing");
        auto dx=static_cast<std::int8_t>(payload[pos]); auto dy=static_cast<std::int8_t>(payload[pos+1]);
        state.x+=dx; state.y+=dy; pos+=2;
    }
    if (mask&0x04) { if (pos>=payload.size()) throw std::runtime_error("direction missing"); state.direction=payload[pos++]; }
    if (mask&0x08) { if (pos>=payload.size()) throw std::runtime_error("flags missing"); state.flags=payload[pos++]; }
    if (mask&0x10) { state.field_0c=read_u16(payload,pos); pos+=2; }
    if (mask&0x20) { state.field_0e=read_u16(payload,pos); pos+=2; }
    if (mask&0x40) { state.field_10=read_u32(payload,pos); pos+=4; }
    if (mask&0x80) { state.event_a=read_u16(payload,pos); state.event_b=read_u16(payload,pos+2); }
}

static std::optional<std::size_t>
compressed_move_event_offset(const Bytes& payload) {
    if (payload.size() < 7 || (payload[0] & 0x80) == 0)
        return std::nullopt;

    const std::uint8_t mask = payload[0];
    std::size_t pos = 5; // Maske + character_id

    pos += (mask & 0x01) ? 2 : 0; // Karte
    pos += (mask & 0x02) ? 4 : 2; // absolut x/y oder relativ dx/dy
    pos += (mask & 0x04) ? 1 : 0; // Richtung
    pos += (mask & 0x08) ? 1 : 0; // Flags
    pos += (mask & 0x10) ? 2 : 0;
    pos += (mask & 0x20) ? 2 : 0;
    pos += (mask & 0x40) ? 4 : 0;

    if (pos + 4 > payload.size())
        return std::nullopt;

    return pos;
}

static void patch_xml(const fs::path& path) {
    fs::path backup=path; backup += ".original";
    if (!fs::is_regular_file(path)) throw std::runtime_error("Nicht gefunden: "+path.string());
    if (!fs::exists(backup)) {
        fs::copy_file(path,backup);
        log_line(str("Sicherung erstellt: ",backup.filename().string()));
    }
    std::string raw=read_text_file(path);
    std::regex re(R"((\bip\s*=\s*["'])[^"']+(["']))",std::regex::icase);
    std::size_t count=0;
    std::string patched;
    std::size_t last=0;
    for (std::sregex_iterator it(raw.begin(),raw.end(),re), end; it!=end; ++it) {
        const auto& m=*it;
        patched.append(raw,last,static_cast<std::size_t>(m.position())-last);
        patched += m[1].str();
        patched += "127.0.0.1";
        patched += m[2].str();
        last=static_cast<std::size_t>(m.position()+m.length());
        ++count;
    }
    patched.append(raw,last,std::string::npos);
    write_text_file(path,patched);
    log_line(str(count," Serveradressen in ",path.filename().string()," auf 127.0.0.1 gesetzt."));
}

static void restore_xml(const fs::path& path) {
    fs::path backup=path; backup += ".original";
    if (!fs::is_regular_file(backup)) throw std::runtime_error("Keine Sicherung gefunden: "+backup.string());
    fs::copy_file(backup,path,fs::copy_options::overwrite_existing);
    log_line(str("Original wiederhergestellt: ",path.string()));
}

static Bytes version_reply() {
    // Header: size, size, command. Payload used by CNet::OnVersion:
    // result (uint32), seed (uint32), type (uint16).
    Bytes p(10); write_u32(p,0,0); write_u32(p,4,VERSION_SEED); write_u16(p,8,0); return make_packet(0x0010,p);
}
static Bytes login_reply() {
    // CNet::OnLogin treats 0..17 as explicit error cases and values >17 as success.
    Bytes p(4); write_u32(p,0,18); return make_packet(0x0100,p);
}

static Bytes clear_character_rename_permissions()
{
    Bytes p(8, 0);
    write_u32(p, 0x00, 0xFFFFFFFFu);
    write_u32(p, 0x04, 0xFFFFFFFFu);
    return make_packet(0x0260, p);
}

static Bytes character_list_reply(
    const std::optional<Bytes>& record = std::nullopt)
{
    Bytes p;

    if (!record) {
        p.resize(2);
        write_u16(p, 0, 0);
    }
    else {
        if (record->size() != CHARACTER_RECORD_SIZE)
            throw std::runtime_error(
                "character record must be exactly 0xE3 bytes");

        Bytes fixed = *record;

        write_u16(
            fixed,
            CHARACTER_RECORD_CGNO_OFFSET,
            PLAYER_CGNO);

        write_u16(
            fixed,
            CHARACTER_RECORD_APPEARANCE_OFFSET,
            PLAYER_APPEARANCE);

        p.resize(2 + fixed.size());
        write_u16(p, 0, 1);
        std::copy(fixed.begin(), fixed.end(), p.begin() + 2);
    }

    return make_packet(0x0220, p);
}

static Bytes character_record_from_create(const Bytes& packet)
{
    Bytes payload = slice(packet, 6);

    if (payload.size() > CHARACTER_RECORD_SIZE)
        throw std::runtime_error("create payload too large");

    payload.resize(CHARACTER_RECORD_SIZE, 0);

    write_u16(
        payload,
        CHARACTER_RECORD_CGNO_OFFSET,
        PLAYER_CGNO);

    write_u16(
        payload,
        CHARACTER_RECORD_APPEARANCE_OFFSET,
        PLAYER_APPEARANCE);

    return payload;
}

static Bytes character_create_reply()
{
    Bytes p(4);
    write_u32(p, 0, 1);   // Erfolg
    return make_packet(0x0200, p);
}

static Bytes character_enter_reply(const Bytes& name, const std::optional<PlayerStatus>& progress=std::nullopt) {
    // Build the client's own 253-byte dummy response for command 0x0230.
    Bytes p(0xFD, 0);
    write_u32(p, 0, 21);

    PlayerStatus pr = progress.value_or(PlayerStatus{});

    p[4] = static_cast<std::uint8_t>(
        clamp_value(pr.level, 1, 255));

    write_u32(p, 5, 4000);
    write_u32(p, 9, std::max(0, pr.current_xp));
    write_u32(p, 13, std::max(1, pr.next_xp));

    write_u16(p, 17, static_cast<std::uint16_t>(pr.current_hp));
    write_u16(p, 19, static_cast<std::uint16_t>(pr.max_hp));

    const std::array<std::pair<int,int>,11> values={{{21,150},{23,200},{25,260},{27,250},{29,270},{31,280},{33,100},{35,210},{37,220},{39,230},{41,240}}};
    for (auto [off,v]:values) write_u16(p,off,static_cast<std::uint16_t>(v));

    std::string safe;
    for (std::size_t i=0;i<name.size() && i<15 && name[i];++i)
        safe.push_back(static_cast<char>(name[i]));
    if (safe.empty()) safe="Adri";

    // Charaktermodell 02, übrige Appearance-Werte zunächst 0, wenn diese Zeile weggelassen wird, wird das Bild von Charakter 0 geladen, aktuell Charakter 2
    write_u16(p, 0x30, 0x0400);

    write_u32(p,54,0x041A);
    std::copy(safe.begin(),safe.end(),p.begin()+66);
    //p[0xF4] = 2 => Charaktername kann geändert werden Meldung erscheint 
    p[0xF4] = 1;
    return make_packet(0x0230,p);
}

static Bytes character_rename_reply(
    std::uint32_t character_id,
    bool success)
{
    Bytes p(8, 0);
    write_u32(p, 0x00, character_id);
    write_u32(p, 0x04, success ? 1u : 0u);
    return make_packet(0x0261, p);
}

static std::string character_name_from_payload(const Bytes& payload) {
    std::string name;
    for (std::size_t i=0;i<payload.size() && i<15 && payload[i];++i)
        name.push_back(static_cast<char>(payload[i]));
    return name.empty() ? "Adri" : name;
}

// The server already has one proven packet which carries the player's HP:
// the 0x0230 character-enter record.  The client uses the same record to
// populate its player-status fields, while 0x0B10/0x0BE0 only update those
// fields as part of the battle flow.  Reuse the exact 0x0230 layout for an
// unsolicited status refresh instead of inventing a new packet format.
static Bytes player_status_sync_reply(const PlayerStatus& progress, const std::string& name) {
    Bytes name_bytes(name.begin(),name.end());
    return character_enter_reply(name_bytes,progress);
}

static Bytes initial_data_reply() {
    // Exact 0x0900 dummy payload constructed by the client's test path.
    Bytes p(10); write_u16(p,0,1); write_u16(p,2,15); write_u16(p,4,0); write_u32(p,6,static_cast<std::uint32_t>(WORLD_TIME_SPEED));
    return make_packet(0x0900,p);
}

static Bytes pet_info_reply(
    std::uint32_t pet_id,
    std::uint16_t slot,
    const std::string& name,
    std::uint16_t cgno,
    int level,
    int current_hp = 25,
    int max_hp = 25,
    int current_xp = 0,
    int next_xp = 100)
{
    Bytes p(0x9C,0);
    write_u32(p,0x00,pet_id);
    write_u16(p,0x04,slot);
    copy_string(p,0x0C,name,31);
    write_u16(p,0x2E,cgno);
    write_u16(p,0x30,static_cast<std::uint16_t>(clamp_value(level,1,65535)));

    // Confirmed by the Chinese pet updater at 0x4CDB90:
    // record +0x09/+0x0D maps to pet data +0x34/+0x38.
    // The old V149 experiment wrote at +0x32/+0x36, corrupting adjacent
    // fields and producing the huge bogus XP values.
    write_u32(p,0x34,static_cast<std::uint32_t>(std::max(0,current_xp)));
    write_u32(p,0x38,static_cast<std::uint32_t>(std::max(1,next_xp)));

    // Proven client fields: +0x3C/+0x3E are a current/max pair.
    write_u16(p,0x3C,static_cast<std::uint16_t>(clamp_value(current_hp,0,65535)));
    write_u16(p,0x3E,static_cast<std::uint16_t>(clamp_value(max_hp,1,65535)));

    // Visible pet stats.  Retail growth is not decoded yet, but keeping stable
    // level-derived values is preferable to wiping them to zero on each sync.
    const int base_stat=10+std::max(1,level)*3;
    write_u16(p,0x40,static_cast<std::uint16_t>(clamp_value(base_stat,1,65535)));
    write_u16(p,0x42,static_cast<std::uint16_t>(clamp_value(base_stat+2,1,65535)));
    write_u16(p,0x44,static_cast<std::uint16_t>(clamp_value(base_stat+1,1,65535)));
    write_u16(p,0x46,static_cast<std::uint16_t>(clamp_value(base_stat,1,65535)));
    p[0x4A]=100;
    p[0x4B]=100;

    copy_string(p,0x62,name,31);
    p[0x82]=1;
    return make_packet(0x0462,p);
}

static Bytes test_pet_reply() {
    return pet_info_reply(TEST_PET_ID,0,ACTIVE_PET_NAME,ACTIVE_PET_CGNO,1);
}

// Reply to the client's SendPetDrop request (CMD 0x0460).
// Chinese client handler 0x00410DF0 is OnPetDropRet:
//   DWORD +0 = pet object ID
//   DWORD +4 = success flag (non-zero removes the pet locally)
static Bytes pet_drop_result_reply(
    std::uint32_t pet_id,
    bool success)
{
    Bytes p(8, 0);
    write_u32(p, 0x00, pet_id);
    write_u32(p, 0x04, success ? 1u : 0u);
    return make_packet(0x0468, p);
}


// Server -> client TCMD_PET_ACT / OnPetAct.
// The Chinese client receive handler logs five DWORDs as:
//   owner, pet, category, action, option
// This is NOT the same layout as the four-DWORD client -> server SendPetAct.
static Bytes pet_action_reply(
    std::uint32_t pet_id,
    std::uint32_t owner_id,
    std::uint32_t category,
    std::uint32_t action,
    std::uint32_t option)
{
    // OnPetAct looks up payload DWORD 0 as the object that receives the
    // action, so the PET must be first.  DWORD 1 is the owner/other actor.
    Bytes p(20, 0);
    write_u32(p, 0x00, pet_id);
    write_u32(p, 0x04, owner_id);
    write_u32(p, 0x08, category);
    write_u32(p, 0x0C, action);
    write_u32(p, 0x10, option);
    return make_packet(0x0463, p);
}

static std::optional<CapturedPetState> captured_pet_snapshot(
    const std::shared_ptr<Session>& session,
    std::uint32_t pet_id)
{
    std::lock_guard lock(session->state_mutex);
    auto it = std::find_if(
        session->captured_pets.begin(),
        session->captured_pets.end(),
        [&](const CapturedPetState& pet) { return pet.pet_id == pet_id; });
    if (it == session->captured_pets.end())
        return std::nullopt;
    return *it;
}

static Bytes captured_pet_object_reply(const CapturedPetState& pet)
{
    // 0x0401 object response = requested object ID + complete 0x9C pet record.
    Bytes info = slice(
        pet_info_reply(
            pet.pet_id,
            pet.slot,
            pet.name,
            pet.cgno,
            pet.level,
            pet.current_hp,
            pet.max_hp,
            pet.current_xp,
            pet.next_xp),
        6);

    Bytes p(4 + info.size(), 0);
    write_u32(p, 0x00, pet.pet_id);
    copy_into(p, 4, info);
    return make_packet(0x0401, p);
}

static std::optional<InventoryItemState> consume_inventory_item_for_pet(
    const std::shared_ptr<Session>& session,
    std::uint32_t object_id)
{
    std::lock_guard lock(session->state_mutex);
    auto it = std::find_if(
        session->inventory_items.begin(),
        session->inventory_items.end(),
        [&](const InventoryItemState& item) { return item.object_id == object_id; });

    if (it == session->inventory_items.end())
        return std::nullopt;

    InventoryItemState consumed = *it;

    // Consume exactly one unit from the selected stack.
    if (it->quantity > 1)
        --it->quantity;
    else
        session->inventory_items.erase(it);

    session->player_stats.items = session->inventory_items;

    return consumed;
}

static std::optional<InventoryItemState> inventory_item_snapshot_by_object_id(
    const std::shared_ptr<Session>& session,
    std::uint32_t object_id)
{
    std::lock_guard lock(session->state_mutex);
    auto it = std::find_if(
        session->inventory_items.begin(),
        session->inventory_items.end(),
        [&](const InventoryItemState& item) { return item.object_id == object_id; });

    if (it == session->inventory_items.end())
        return std::nullopt;

    return *it;
}


static Bytes item_have_reply(const std::vector<InventoryItemState>& items)
{
    // Chinese OnItemHave -> 0x4D2C80 consumes count * 0x12-byte records.
    // Verified directly in the 2010 client: the loop ends with add esi,0x12.
    //
    // Record layout recovered from the client:
    //   +0x00 DWORD object ID
    //   +0x04 WORD  ItemNo
    //   +0x06 WORD  equipment CGNO/state (only meaningful when equipped)
    //   +0x08 WORD  inventory/category code.  IMPORTANT: the Chinese client
    //                maps 0 to UI group 4 and skips it; normal items must use
    //                their real ItemInfo category (normally 1..18).
    //   +0x0A WORD  option flags; bit 0x10 means EQUIPPED
    //   +0x0C WORD  unknown
    //   +0x0E WORD  unknown
    //   +0x10 WORD  quantity / remaining count
    if (items.size() > 0x28)
        throw std::runtime_error("inventory item batch exceeds client limit");

    Bytes p(2 + items.size() * 0x12, 0);
    write_u16(p, 0x00, static_cast<std::uint16_t>(items.size()));

    for (std::size_t i = 0; i < items.size(); ++i) {
        const std::size_t off = 2 + i * 0x12;
        write_u32(p, off + 0x00, items[i].object_id);
        write_u16(p, off + 0x04, items[i].item_no);
        write_u16(p, off + 0x06, items[i].cgno);
        write_u16(p, off + 0x08, items[i].category);
        write_u16(p, off + 0x0A, items[i].option);
        write_u16(p, off + 0x0C, items[i].field_0c);
        write_u16(p, off + 0x0E, items[i].field_0e);
        write_u16(p, off + 0x10, std::max<std::uint16_t>(1, items[i].quantity));
    }

    return make_packet(0x04B0, p);
}

static Bytes item_info_reply(
    std::uint32_t object_id,
    std::uint16_t item_no)
{
    const auto& entry = item_catalog_entry(item_no);
    Bytes p(4 + 0x14A, 0);
    write_u32(p, 0, object_id);
    copy_into(p, 4, entry.wire_definition);
    return make_packet(0x0510, p);
}


static bool send_persisted_inventory(
    const std::shared_ptr<Session>& session)
{
    std::vector<InventoryItemState> items;

    {
        std::lock_guard lock(session->state_mutex);
        items = session->inventory_items;
    }

    if (items.empty())
        return true;

    std::set<std::uint16_t> sent_definitions;

    for (const auto& item : items)
    {
        if (!sent_definitions.insert(item.item_no).second)
            continue;

        Bytes definition = item_info_reply(0, item.item_no);

        if (!send_all(session, definition))
            return false;
    }

    std::this_thread::sleep_for(50ms);

    return send_all(session, item_have_reply(items));
}

static Bytes item_consumed_reply(std::uint32_t object_id)
{
    // The Chinese client's 0x04B2 handler reads exactly one object ID and
    // routes it through the same OnItemUse path used to decrement/remove the
    // corresponding client-side inventory object.  Merely removing it from
    // the server-side vector leaves the stale icon visible in the client.
    Bytes p(4, 0);
    write_u32(p, 0, object_id);
    return make_packet(0x04B2, p);
}


static std::uint32_t inventory_object_for_item_no(
    const std::shared_ptr<Session>& session,
    std::uint16_t item_no)
{
    std::lock_guard lock(session->state_mutex);
    auto it = std::find_if(
        session->inventory_items.begin(),
        session->inventory_items.end(),
        [&](const InventoryItemState& item) { return item.item_no == item_no; });
    return it == session->inventory_items.end() ? 0u : it->object_id;
}

static std::optional<std::uint16_t> inventory_item_no_for_object_id(
    const std::shared_ptr<Session>& session,
    std::uint32_t object_id)
{
    std::lock_guard lock(session->state_mutex);
    auto it = std::find_if(
        session->inventory_items.begin(),
        session->inventory_items.end(),
        [&](const InventoryItemState& item) { return item.object_id == object_id; });
    if (it == session->inventory_items.end())
        return std::nullopt;
    return it->item_no;
}

static bool award_food_item_drop(
    const std::shared_ptr<Session>& session,
    std::uint16_t item_no)
{
    if (random_int(0, 99) >= TEST_ITEM_DROP_CHANCE_PERCENT)
        return false;

    InventoryItemState item;
    bool new_stack = false;
    std::vector<InventoryItemState> inventory_snapshot;

    {
        std::lock_guard lock(session->state_mutex);

        auto it = std::find_if(
            session->inventory_items.begin(),
            session->inventory_items.end(),
            [&](const InventoryItemState& existing) {
                return existing.item_no == item_no;
            });

        if (it != session->inventory_items.end()) {
            if (it->quantity == std::numeric_limits<std::uint16_t>::max()) {
                log_line(str(
                    "[ITEM-DROP] Stack fuer ItemNo=", item_no,
                    " hat bereits UINT16_MAX erreicht; kein weiterer Drop."));
                return false;
            }

            ++it->quantity;
            item = *it;
        }
        else {
            if (session->inventory_items.size() >= 0x28) {
                log_line(str(
                    "[ITEM-DROP] Inventarlimit 40 erreicht und kein vorhandener "
                    "Stack fuer ItemNo=", item_no, "; kein Drop."));
                return false;
            }

            item.object_id = session->next_inventory_item_id++;
            item.item_no = item_no;
            item.cgno = 0;
            item.category = 0x13;
            item.option = 0x02;
            item.field_0c = 0;
            item.field_0e = 0;
            item.quantity = 1;

            session->inventory_items.push_back(item);
            new_stack = true;
        }

        inventory_snapshot = session->inventory_items;
        session->player_stats.items = inventory_snapshot;
    }

    bool info_sent = true;

    if (new_stack) {
        const auto& catalog_entry = item_catalog_entry(item.item_no);
        Bytes info_packet = item_info_reply(0u, item.item_no);
        info_sent = send_all(session, info_packet);

        log_line(str(
            info_sent ? "[ITEM-DROP] 0x0510 Definition gesendet: ItemNo="
                      : "[ITEM-DROP] 0x0510 Definition SENDEN FEHLGESCHLAGEN: ItemNo=",
            item.item_no,
            ", Bild=", catalog_entry.picture_no,
            ", Kategorie=", catalog_entry.category,
            ", FoodValue=", catalog_entry.food_value,
            ", Paket=", hexline(info_packet)));
    }

    // Same ObjectID + updated quantity => update the existing client stack.
    Bytes packet = item_have_reply({item});
    const bool sent = send_all(session, packet);

    log_line(str(
        sent ? (new_stack
                    ? "[ITEM-DROP] Neuer Stack: object_id=0x"
                    : "[ITEM-DROP] Stack erhoeht: object_id=0x")
             : "[ITEM-DROP] SENDEN FEHLGESCHLAGEN: object_id=0x",
        [&] {
            std::ostringstream os;
            os << std::hex << std::uppercase << item.object_id;
            return os.str();
        }(),
        ", ItemNo=", item.item_no,
        ", Menge=", item.quantity,
        ", belegte Slots=", inventory_snapshot.size(),
        ", Paket=", hexline(packet)));

    return info_sent && sent;
}

static bool send_captured_pet_list(const std::shared_ptr<Session>& session) {
    std::vector<CapturedPetState> pets;
    {
        std::lock_guard lock(session->state_mutex);
        pets = session->captured_pets;
    }

    if (pets.empty()) {
        log_line("[PERSISTENZ] Keine gespeicherten Pets an den Client zu senden.");
        return true;
    }

    log_line(str(
        "[PERSISTENZ] Sende ", pets.size(),
        " gespeicherte Pets erneut an den Client."));

    for (const auto& pet : pets) {
        Bytes packet = pet_info_reply(
            pet.pet_id,
            pet.slot,
            pet.name,
            pet.cgno,
            pet.level,
            pet.current_hp,
            pet.max_hp,
            pet.current_xp,
            pet.next_xp);

        if (!send_all(session, packet))
            return false;

        log_line(str(
            "[GESENDET] GESPEICHERTES PET 0x0462, Slot=",
            pet.slot,
            ", Pet-ID=0x",
            [&] {
                std::ostringstream os;
                os << std::hex << std::uppercase << pet.pet_id;
                return os.str();
            }(),
            ", Name=", pet.name,
            ", CGNO=", pet.cgno,
            ", Level=", pet.level));

        std::this_thread::sleep_for(35ms);
    }

    return true;
}
static Bytes test_pet_object_reply() {
    // 0x0401 needs a separate object ID followed by the complete 0x9c record.
    Bytes info=slice(test_pet_reply(),6), p(4+info.size()); write_u32(p,0,TEST_PET_ID); copy_into(p,4,info); return make_packet(0x0401,p);
}

static std::string describe_pet_action(const Bytes& packet) {
    Bytes p=slice(packet,6); if (p.size()<16) return str("ungueltige Nutzlast (",p.size()," Bytes)");
    return str("pet_id=",read_u32(p,0),", action=",read_u32(p,4),", value=",read_u32(p,8),", character_id=",read_u32(p,12));
}
static std::string describe_move(const Bytes& packet) {
    Bytes p=slice(packet,6); if (p.size()<12) return str("ungueltige Nutzlast (",p.size()," Bytes)");
    std::ostringstream os; os << "char_id="<<read_u32(p,0)<<", sequence="<<read_u16(p,4)<<", x="<<read_i16(p,6)<<", y="<<read_i16(p,8)<<", direction="<<unsigned(p[10])<<", flags=0x"<<std::hex<<std::uppercase<<std::setw(2)<<std::setfill('0')<<unsigned(p[11]); return os.str();
}

static Bytes position_reply(int map_id,int x,int y,int direction=4,std::uint32_t object_id=21,std::uint16_t graphic_no=PLAYER_CGNO) {
    // Build the server-to-client 0x0410 map/position state.
    x=clamp_value(x,-32768,32767); y=clamp_value(y,-32768,32767);
    Bytes p(24,0); write_u32(p,0,object_id); write_u16(p,4,static_cast<std::uint16_t>(map_id));
    write_i16(p,6,static_cast<std::int16_t>(x)); write_i16(p,8,static_cast<std::int16_t>(y)); p[10]=static_cast<std::uint8_t>(direction);
    write_u16(p,12,graphic_no); write_u16(p,18,static_cast<std::uint16_t>(x)); write_u16(p,20,static_cast<std::uint16_t>(y));
    return make_packet(0x0410,p);
}
static Bytes test_pet_position_reply(int map_id,int x,int y) { return position_reply(map_id,x,y,4,TEST_PET_ID,ACTIVE_PET_CGNO); }
static std::pair<int,int> close_trailing_position(int old_x,int old_y,int new_x,int new_y) {
    int dx=new_x-old_x, dy=new_y-old_y; int sx=(dx>0)-(dx<0), sy=(dy>0)-(dy<0); return {new_x-sx,new_y-sy};
}
static Bytes initial_position_reply() { return position_reply(100,150,150); }

static std::uint32_t battle_packet_id(std::uint32_t actor_id)
{
    // Keep every battle packet on exactly the same compact-ID mapping as
    // BattleInit and 0x0BD1.
    return battle_slot_from_actor_id(actor_id);
}

static Bytes battle_test_reply(
    const PlayerStatus& player_stats,
    int map_id=12000,
    const std::vector<ActorConfig>& enemies=ENEMIES,
    const std::vector<ActorConfig>& pets=PETS,
    std::vector<std::uint32_t> pet_object_ids={})
{
    // Build a multi-enemy battletest for the Chinese 2010 client.
    // The receive table registers 0x0B10 at 0x0040E1D0. That handler forwards
    // the payload and its length unchanged to BattleInit at 0x00428720. The
    // developer test at 0x0041DCA0 in the Chinese 2010 executable constructs
    // 0x65-byte records. The German client accepts that packet but only indexes
    // the player: its older record is two bytes shorter.
    constexpr std::size_t record_size=0x65;

    if (pet_object_ids.size() != pets.size()) {
        pet_object_ids.clear();
        pet_object_ids.reserve(pets.size());
        for (std::size_t i = 0; i < pets.size(); ++i)
            pet_object_ids.push_back(
                PET_BATTLE_ACTOR_BASE + static_cast<std::uint32_t>(i));
    }

    Bytes player(record_size, 0);  std::vector<Bytes> pet_records(pets.size(), Bytes(record_size, 0));
    std::vector<Bytes> enemy_records(enemies.size(),Bytes(record_size,0));
    std::vector<Bytes*> records; records.push_back(&player);
    for (auto& e:enemy_records) records.push_back(&e);
    for (auto& p : pet_records) records.push_back(&p);


    Bytes payload(12+records.size()*record_size,0);
    int battle_x=BATTLE_ANCHOR_X+BATTLE_MAP_OFFSET_X;
    int battle_y=BATTLE_ANCHOR_Y+BATTLE_MAP_OFFSET_Y;
    write_u16(payload,0,static_cast<std::uint16_t>(map_id));
    write_i16(payload,2,0); write_i16(payload,4,static_cast<std::int16_t>(battle_x)); write_i16(payload,6,static_cast<std::int16_t>(battle_y));
    payload[8]=1; payload[9]=1; payload[10]=0; payload[11]=static_cast<std::uint8_t>(records.size());
    for (auto* r:records) { (*r)[27]=10; (*r)[28]=1; }

    write_u32(player,0,21); 
    write_u32(player, 19, player_stats.max_hp);
    write_u32(player, 23, player_stats.current_hp);
    player[33]=50; player[34]=50; player[37]=2; copy_string(player,39,player_stats.name,31); write_u32(player,0x4B,21);
    write_u16(player,0x51,static_cast<std::uint16_t>(map_id));
    write_u16(player,0x53,static_cast<std::uint16_t>(23+BATTLE_MAP_OFFSET_X));
    write_u16(player,0x55,static_cast<std::uint16_t>(36+BATTLE_MAP_OFFSET_Y));
    write_u16(player, 0x57, 7); write_u16(player, 0x59, PLAYER_CGNO);


    for (std::size_t i = 0; i < enemies.size(); ++i) {
        const auto& cfg = enemies[i];
        auto& r = enemy_records[i];

        std::uint32_t enemy_id =
            0x60000015u + static_cast<std::uint32_t>(i);

        write_u32(r, 0, enemy_id);
        std::uint8_t battle_slot =
            1 + static_cast<std::uint8_t>(i);

        write_u32(r, 0, enemy_id);
        write_u32(r, 4, battle_slot_from_actor_id(enemy_id));
        log_line(str(
            "[BATTLEINIT ENEMY V145] actor=0x",
            [&] { std::ostringstream os; os << std::hex << std::uppercase << enemy_id; return os.str(); }(),
            ", compact=0x",
            [&] { std::ostringstream os; os << std::hex << std::uppercase
                                            << battle_slot_from_actor_id(enemy_id); return os.str(); }()));
        r[28] = static_cast<std::uint8_t>(
            clamp_value(cfg.level, 1, 255));

        const int max_hp = cfg.max_hp > 0 ? cfg.max_hp : std::max(1, cfg.hp);
        const int current_hp = clamp_value(cfg.hp, 0, max_hp);
        write_u32(r,19,max_hp); write_u32(r,23,current_hp);
        r[35] = 60; r[36] = 40; r[37] = 10;
        copy_string(r,39,cfg.name,31); write_u32(r,0x4B,enemy_id);
        write_u16(r,0x51,static_cast<std::uint16_t>(map_id));
        write_u16(r,0x53,static_cast<std::uint16_t>(23+BATTLE_MAP_OFFSET_X+ENEMY_BATTLE_X_SHIFT+static_cast<int>(i) * 4));
        write_u16(r,0x55,static_cast<std::uint16_t>(20+BATTLE_MAP_OFFSET_Y));
        write_u16(r,0x57,3); write_u16(r,0x59,cfg.cgno);
    }


    for (std::size_t i = 0; i < pets.size(); ++i) {
        auto& r = pet_records[i];
        const auto& cfg = pets[i];

        // IMPORTANT: The battle actor must use the SAME object ID as the
        // persistent pet in the normal 0x0462 pet list.  The previous v118
        // changed PET_BATTLE_ACTOR_BASE/logging, but accidentally left this
        // actual BattleInit field hard-coded at 0x20000015+i.
        const std::uint32_t battle_pet_id = pet_object_ids[i];
        const std::uint32_t compact_pet_id =
            0x01000000u + (static_cast<std::uint32_t>(i) << 8);

        write_u32(r, 0x00, battle_pet_id);

        std::uint8_t battle_slot =
            1 + static_cast<std::uint8_t>(i);

        write_u32(r, 0x00, battle_pet_id);


        write_u32(r, 0x04, compact_pet_id);

        const int pet_max_hp =
            cfg.max_hp > 0 ? cfg.max_hp : std::max(1, cfg.hp);
        const int pet_current_hp =
            clamp_value(cfg.hp, 0, pet_max_hp);
        write_u32(r, 19, pet_max_hp);
        write_u32(r, 23, pet_current_hp);

        r[27] = 10;
        r[28] = static_cast<std::uint8_t>(
            clamp_value(cfg.level, 1, 255));
        r[33] = 70;
        r[36] = 30;

        // Chinese 2010 developer BattleInit (0x0041DCA0):
        // record[37] is NOT the pet level. The developer test uses categorical
        // values here: player=2, enemy=10, own pet=0. Keep the pet value
        // byte-for-byte compatible with that original BattleInit record.
        r[37] = 0;

        copy_string(r, 39, cfg.name, 31);

        write_u32(r, 0x4D, battle_pet_id);

        write_u16(
            r,
            0x51,
            static_cast<std::uint16_t>(map_id));

        write_u16(
            r,
            0x53,
            static_cast<std::uint16_t>(
                23 + BATTLE_MAP_OFFSET_X + ALLY_PET_BATTLE_X_SHIFT +
                static_cast<int>(i) * 3));

        write_u16(
            r,
            0x55,
            static_cast<std::uint16_t>(
                33 + BATTLE_MAP_OFFSET_Y));

        write_u16(r, 0x57, 7);
        write_u16(r, 0x59, cfg.cgno);

        log_line(str(
            "[BATTLEINIT PET] index=", i,
            ", actor=0x", [&] { std::ostringstream os; os << std::hex << std::uppercase << battle_pet_id; return os.str(); }(),
            ", compact=0x", [&] { std::ostringstream os; os << std::hex << std::uppercase << std::setw(8) << std::setfill('0') << compact_pet_id; return os.str(); }(),
            ", HP=", pet_current_hp, "/", pet_max_hp,
            ", level=", cfg.level,
            ", role/control byte37=", static_cast<unsigned>(r[37]),
            ", CGNO=", cfg.cgno));
    }

    for (std::size_t i=0;i<records.size();++i) copy_into(payload,12+i*record_size,*records[i]);
    return make_packet(0x0B10,payload);
}

static Bytes battle_order_reply(
    std::uint32_t actor_id,
    std::uint8_t action = 0,
    std::uint32_t target_id = 0x60000015)
{
    // Observed Chinese-client 0x0B20 packets are 64 bytes on the wire
    // (58-byte payload).  The first four DWORDs are, in order:
    //   +00 actor object ID
    //   +04 actor battle-order ID (0 for player, 0x01000000 for pet 0)
    //   +08 action
    //   +0C additional order field
    // followed by target object ID and target battle-order ID.
    // The +0C value 0x05000000 is observed for a normal attack; for the
    // synthetic 'wait/activate actor' packet we keep it zero.
    Bytes p(0x3A, 0);

    write_u32(p, 0x00, actor_id);
    write_u32(p, 0x04, battle_packet_id(actor_id));
    write_u32(p, 0x08, static_cast<std::uint32_t>(action));

    if (action == 3)
        write_u32(p, 0x0C, 0x05000000u);

    write_u32(p, 0x10, target_id);
    write_u32(p, 0x14, battle_packet_id(target_id));

    return make_packet(0x0B20, p);
}
static Bytes battle_action_reply(std::uint32_t actor_id,std::uint32_t target_id=0x60000015) {
    Bytes r(0x4B,0); write_u32(r,0,actor_id); r[8]=0x6E; write_u16(r,0x10,0x00CF); write_u32(r,0x32,target_id); r[0x36]=1; r[0x40]=0x37; r[0x41]=0x1E; r[0x43]=0x0F;
    Bytes p={0,1}; p.insert(p.end(),r.begin(),r.end()); return make_packet(0x0B30,p);
}
static Bytes battle_simple_action_record(std::uint32_t actor_id,std::uint8_t action,std::optional<std::uint32_t> target_id=std::nullopt) {
    if (action!=3 && action!=8 && action!=0x99) throw std::runtime_error("unsupported simple battle action");
    std::uint32_t target=target_id.value_or(actor_id); Bytes r(0x4B,0); write_u32(r,0,actor_id); r[8]=action;
    if (action==3) { write_u32(r,0x32,actor_id); write_u32(r,0x36,target); }
    else write_u32(r,0x32,target);
    if (action==0x99) r[0x3A]=0x5A;
    return r;
}

static Bytes battle_simple_action_reply(std::uint32_t actor_id,std::uint8_t action,std::optional<std::uint32_t> target_id=std::nullopt) {
    Bytes r=battle_simple_action_record(actor_id,action,target_id);
    Bytes p={0,1}; p.insert(p.end(),r.begin(),r.end()); return make_packet(0x0B30,p);
}

static Bytes battle_enemy_simple_action_reply(
    std::uint32_t actor_id,
    std::uint32_t battle_id,
    std::uint8_t action)
{
    Bytes r(0x4B, 0);

    write_u32(r, 0x00, actor_id);
    write_u32(r, 0x04, battle_id);

    r[0x08] = action;

    write_u32(r, 0x32, actor_id);
    write_u32(r, 0x36, battle_id);

    if (action == 0x99) {
        r[0x3A] = 0x5A;
    }

    Bytes p = { 0, 1 };
    p.insert(p.end(), r.begin(), r.end());

    return make_packet(0x0B30, p);
}
static Bytes battle_defend_reply(
    std::uint32_t actor_id,
    std::uint32_t battle_id)
{
    return battle_enemy_simple_action_reply(
        actor_id,
        battle_id,
        0x08);
}

static Bytes battle_attack_exchange_record(
    std::uint32_t actor_object_id,
    std::uint32_t actor_battle_id,
    std::uint32_t target_object_id,
    std::uint32_t target_battle_id,
    int damage = 10,
    bool lethal = false,
    bool target_defending = false,
    bool critical = false,
    bool miss = false,
    bool UltimateKO = false)
{
    Bytes attack(0x4B, 0);

    write_u32(attack, 0x00, actor_object_id);

    // Small BattleInit actor index.
    write_u32(attack, 0x04, actor_battle_id);

    attack[0x08] = 3;

    write_u32(attack, 0x32, target_object_id);

    // Small BattleInit passive/target index.
    write_u32(attack, 0x36, target_battle_id);

    damage = std::max(
        0,
        std::min(0x7FFFFFFF, damage));

    write_i32(attack, 0x3B, -damage);

    // Result/effect byte at +0x3A.  Earlier V96 tests confirmed 0x54
    // triggers the client's critical-hit effect.  Do not combine it with
    // defend or lethal K.O. handling; those keep their proven paths.
    //0x55 = miss

    if (miss)
        attack[0x3A] = 0x55;
    else
    {
        if (critical && !target_defending)
            attack[0x3A] = 0x54;
        else
            attack[0x3A] = (target_defending && !lethal) ? 0x08 : 0x00;

    }

    if(UltimateKO)
        write_u16(attack, 0x44, 0x0040);
    else
    // Normal K.O. finalisation after the normal hit animation.
        write_u16(attack, 0x44, lethal ? 0x0020 : 0x0000);

    return attack;
}

static Bytes battle_action_batch_reply(const std::vector<Bytes>& actions)
{
    if (actions.empty() || actions.size() > 255)
        throw std::runtime_error("invalid battle action count");

    Bytes payload;
    payload.reserve(2 + actions.size() * 0x4B);
    payload.push_back(0);
    payload.push_back(static_cast<std::uint8_t>(actions.size()));

    for (const auto& action : actions) {
        if (action.size() != 0x4B)
            throw std::runtime_error("battle action record must be 0x4B bytes");

        payload.insert(payload.end(), action.begin(), action.end());
    }

    return make_packet(0x0B30, payload);
}

static Bytes battle_attack_exchange_reply(
    std::uint32_t actor_object_id,
    std::uint32_t actor_battle_id,
    std::uint32_t target_object_id,
    std::uint32_t target_battle_id,
    int damage = 10,
    bool lethal = false,
    bool target_defending = false,
    bool critical = false,
    bool miss = false,
    bool UltimateKO = false)
{
    // Normaler 0x0B30-Angriff bleibt BAF_NONE:
    //   payload[0] = 0
    //   payload[1] = Anzahl 0x4B-Action-Records
    //
    // Der fruehere DeadChara-Test gehoert nicht in diesen Wrapper. Er hat
    // das Payload-Layout verschoben und beim Client u.a. CGNO6 verursacht.
    //
    // Wichtig: lethal wird hier an den 0x4B-Record durchgereicht, damit der
    // aktuelle Pas/CND-Test in battle_attack_exchange_record() tatsaechlich
    // ausgefuehrt wird.
    return battle_action_batch_reply({
        battle_attack_exchange_record(
            actor_object_id,
            actor_battle_id,
            target_object_id,
            target_battle_id,
            damage,
            lethal,
            target_defending,
            critical,
            miss,
            UltimateKO)
    });
}

static Bytes battle_combo_reply(
    const std::vector<Bytes>& attacks)
{
    Bytes payload;

    // 0x0B30 Battle Action subtype:
    // BAF_SIM_ATK = 2
    payload.push_back(2);

    // Noch niemand separat als "DeadChara" vorgemerkt.
    payload.push_back(0);

    // Anzahl gleichzeitig beteiligter Angriffsrecords.
    payload.push_back(
        static_cast<std::uint8_t>(attacks.size()));

    for (const auto& attack : attacks) {
        if (attack.size() != 0x4B)
            throw std::runtime_error(
                "Combo action must be 0x4B bytes");

        payload.insert(
            payload.end(),
            attack.begin(),
            attack.end());
    }

    return make_packet(0x0B30, payload);
}

static std::vector<Bytes> living_enemy_attack_records(
    const std::shared_ptr<Session>& session,
    int damage = 5)
{
    std::vector<Bytes> actions;

    std::lock_guard lock(session->state_mutex);

    for (const auto& enemy : session->battle_enemies) {
        if (enemy.hp <= 0)
            continue;

        actions.push_back(
            battle_attack_exchange_record(
                enemy.actor_id,
                battle_slot_from_actor_id(enemy.actor_id),
                21,
                0,
                damage,
                false));
    }

    return actions;
}


static Bytes battle_end_reply(std::uint8_t end_flag, int map_id, int x, int y, int direction = 4) {
    Bytes pos = slice(position_reply(map_id, x, y, direction, 21, 0x7532), 6); Bytes p; p.push_back(end_flag); p.insert(p.end(), pos.begin(), pos.end()); p.push_back(0); p.push_back(0); return make_packet(0x0BE0, p);
}

static void finish_battle_defeat(
    const std::shared_ptr<Session>& session)
{
    std::this_thread::sleep_for(1500ms);

    PlayerStatus progress;
    MoveState position;

    {

        // Respawn in the Den.
        session->move_state.map = DEN_ENTRY_TARGET.map;
        session->move_state.x = DEN_ENTRY_TARGET.x;
        session->move_state.y = DEN_ENTRY_TARGET.y;
        session->move_state.direction = DEN_ENTRY_TARGET.direction;

        // For now: revive fully in the Den.
        session->player_stats.current_hp =
            session->player_stats.max_hp;

        session->battle_active = false;
        session->battle_order_phase_started = false;
        session->player_sleeping = false;
        session->encounter_block_until =
            std::chrono::steady_clock::now() + 2000ms;
        // A battle exit must never leave the random encounter counter ready
        // to fire on a client-side world resync packet.
        session->encounter_steps = std::max(session->encounter_steps, 32);
        session->battle_enemies.clear();
        session->encounter_pet.reset();
        session->battle_turn_order.clear();
        session->battle_pet_actor_ids.clear();
        session->battle_turn_index = 0;

        progress = session->player_stats;
        position = session->move_state;
    }

    save_player_progress(progress);
    save_player_position(position);

    Bytes end = battle_end_reply(
        0x04,
        position.map,
        position.x,
        position.y,
        position.direction);

    send_all(session, end);

    std::string character_name;
    {
        std::lock_guard lock(session->state_mutex);
        character_name = session->character_name;
    }
    std::this_thread::sleep_for(75ms);
    send_all(session, player_status_sync_reply(progress, character_name));

    log_line("[KAMPF] Spieler besiegt -> Respawn im Den.");
}

static Bytes battle_knockout_finalize_reply(
    std::uint32_t defeated_object_id,
    std::uint32_t defeated_battle_id)
{
    // Diagnostic test for the Chinese client's dedicated Act=0x9A path.
    // The old helper only filled record+0 and Act, so the dispatcher could not
    // resolve a proper BattleActor/passive target.  This version supplies the
    // same object as both acting and passive actor deliberately: the goal of
    // this test is to see whether 0x9A is the actor's native defeated/KO
    // finalization animation after a normal HP-to-zero hit.
    Bytes r(0x4B, 0);
    write_u32(r, 0x00, defeated_object_id);
    write_u32(r, 0x04, defeated_battle_id);
    r[0x08] = 0x9A;
    write_u32(r, 0x32, defeated_object_id);
    write_u32(r, 0x36, defeated_battle_id);
    r[0x3A] = 0;
    write_u16(r, 0x44, 0);

    return battle_action_batch_reply({r});
}

static Bytes battle_capture_reply(
    std::uint32_t target_battle_id,
    bool success,
    std::uint8_t turn = 0)
{
    Bytes capture(0x13, 0);

    // Player Battle ID.
    write_u32(capture, 0x04, 0);

    // Normal capture action.
    capture[0x08] = 0x58;

    // Target Battle ID.
    write_u32(capture, 0x0D, target_battle_id);

    // Capture result/state.
    capture[0x11] = success ? 0x5A : 0x00;

    capture[0x12] = turn;

    Bytes payload;
    payload.push_back(3); // BAF_CAPTURE

    payload.insert(
        payload.end(),
        capture.begin(),
        capture.end());

    return make_packet(0x0B30, payload);
}

static Bytes battle_order_phase_request_reply()
{
    // Chinese 2010 client:
    // The battle-manager TCMD_BATTLE_SYNC_CMD handler ignores the payload
    // contents, but the network/dispatch path still expects a non-empty,
    // structurally valid request.  Use the already proven 8-byte form:
    //   DWORD actor/object id = player (21)
    //   DWORD compact battle id = player (0)
    // 0x0BD1 starts/restarts the complete order-selection phase from actor 0;
    // it is never used to step from player -> pet inside the same phase.
    Bytes p(8, 0);
    write_u32(p, 0, PLAYER_BATTLE_ACTOR_ID);
    write_u32(p, 4, battle_slot_from_actor_id(PLAYER_BATTLE_ACTOR_ID));
    return make_packet(0x0BD1, p);
}

static Bytes battle_character_update(std::uint32_t actor_id,int level,int current_xp,int next_xp) {
    Bytes full=slice(character_enter_reply(Bytes{'A','d','r','i'}),6), u(0x3D,0);
    std::copy(full.begin(),full.begin()+4,u.begin());
    std::copy(full.begin()+8,full.begin()+8+(0x3D-4),u.begin()+4);
    write_u32(u,0,actor_id); u[4]=static_cast<std::uint8_t>(clamp_value(level,1,255)); write_u32(u,9,std::max(0,current_xp)); write_u32(u,0x0D,std::max(1,next_xp)); return u;
}



static Bytes battle_pet_update(const CapturedPetState& pet) {
    // The client updater at 0x4CDB90 maps this 0x3D record directly into the
    // persistent pet structure: +04 level, +09/+0D progression, +11/+15 HP,
    // +19 condition and +22/+24/+26 visible stats.
    Bytes u(0x3D,0);
    write_u32(u,0x00,pet.pet_id);
    u[0x04]=static_cast<std::uint8_t>(clamp_value(pet.level,1,255));
    write_u32(u,0x09,static_cast<std::uint32_t>(std::max(0,pet.current_xp)));
    write_u32(u,0x0D,static_cast<std::uint32_t>(std::max(1,pet.next_xp)));
    write_u16(u,0x11,static_cast<std::uint16_t>(clamp_value(pet.current_hp,0,65535)));
    write_u16(u,0x15,static_cast<std::uint16_t>(clamp_value(pet.max_hp,1,65535)));
    u[0x19]=100;
    const int base_stat=10+std::max(1,pet.level)*3;
    write_u16(u,0x22,static_cast<std::uint16_t>(clamp_value(base_stat,1,65535)));
    write_u16(u,0x24,static_cast<std::uint16_t>(clamp_value(base_stat+2,1,65535)));
    write_u16(u,0x26,static_cast<std::uint16_t>(clamp_value(base_stat+1,1,65535)));
    return u;
}

static Bytes battle_victory_reply(
    std::uint32_t actor_id,
    int xp_gain,
    const PlayerStatus& progress,
    const std::vector<CapturedPetState>& pet_updates,
    const std::vector<std::uint32_t>& level_up_actor_ids,
    int map_id,
    int x,
    int y,
    int direction=4)
{
    // Battle-end has a fixed 0x92-byte header followed by CharaCnt 0x3D-byte
    // character-update records. LevelCnt identifies the actors whose result
    // data is processed; CharaCnt must match the appended record count.
    const std::size_t update_count =
        std::min<std::size_t>(10, 1 + pet_updates.size());
    const std::size_t level_count =
        std::min<std::size_t>(10, level_up_actor_ids.size());

    Bytes result(0x92 + update_count * 0x3D, 0);
    result[0] = static_cast<std::uint8_t>(level_count); // LevelCnt

    // LevelCnt is independent from CharaCnt.  Only actors that actually
    // crossed a level boundary belong in this list; all participating actors
    // still receive their XP/status update records below.
    for (std::size_t i = 0; i < level_count; ++i)
        write_u32(result, 1 + i * 4, level_up_actor_ids[i]);

    std::vector<Bytes> updates;
    updates.reserve(update_count);

    updates.push_back(battle_character_update(
        actor_id, progress.level, progress.current_xp, progress.next_xp));

    for (std::size_t i = 0; i < pet_updates.size() && updates.size() < update_count; ++i) {
        const auto& pet = pet_updates[i];
        updates.push_back(battle_pet_update(pet));
    }

    write_u32(result, 0x29, std::max(0, xp_gain));
    Bytes pos = slice(position_reply(map_id,x,y,direction,actor_id,0x7532),6);
    copy_into(result,0x31,pos);

    result[0x5A] = static_cast<std::uint8_t>(updates.size()); // CharaCnt
    result[0x91] = updates.empty() ? 0 : 1;

    for (std::size_t i = 0; i < updates.size(); ++i)
        copy_into(result, 0x92 + i * 0x3D, updates[i]);

    Bytes p;
    p.push_back(0x20);
    p.insert(p.end(),result.begin(),result.end());
    p.push_back(0);
    p.push_back(0);
    return make_packet(0x0BE0,p);
}


static bool send_pending_captured_pet(const std::shared_ptr<Session>& session) {
    std::optional<CapturedPetState> captured;

    {
        std::lock_guard lock(session->state_mutex);
        captured = session->pending_captured_pet;
        session->pending_captured_pet.reset();
    }

    if (!captured) return false;

    Bytes pet = pet_info_reply(
        captured->pet_id,
        captured->slot,
        captured->name,
        captured->cgno,
        captured->level,
        captured->current_hp,
        captured->max_hp);

    if (!send_all(session,pet)) return false;

    log_line(str(
        "[GESENDET] GEFANGENES PET 0x0462, Slot=",
        captured->slot,
        ", Pet-ID=0x",
        [&] {
            std::ostringstream os;
            os << std::hex << std::uppercase << captured->pet_id;
            return os.str();
        }(),
        ", Name=",
        captured->name,
        ", CGNO=",
        captured->cgno,
        ", Level=",
        captured->level,
        ": ",
        hexline(pet)));

    return true;
}

struct InitiativeBattleAction {
    PlannedBattleAction order;
    int level = 1;
    int speed = 1;
    int tie_break = 0;
    bool enemy = false;
};

static int battle_actor_level_locked(
    const Session& session,
    std::uint32_t actor_id)
{
    if (actor_id == PLAYER_BATTLE_ACTOR_ID)
        return std::max(1, session.player_stats.level);

    if ((actor_id & 0xF0000000u) == 0x20000000u) {
        auto pet_it = std::find_if(
            session.captured_pets.begin(),
            session.captured_pets.end(),
            [&](const CapturedPetState& pet) {
                return pet.pet_id == actor_id;
            });

        if (pet_it != session.captured_pets.end())
            return std::max(1, pet_it->level);

        return 1;
    }

    if ((actor_id & 0xF0000000u) == 0x60000000u) {
        auto enemy_it = std::find_if(
            session.battle_enemies.begin(),
            session.battle_enemies.end(),
            [&](const BattleEnemyState& enemy) {
                return enemy.actor_id == actor_id;
            });

        if (enemy_it != session.battle_enemies.end())
            return std::max(1, enemy_it->level);
    }

    return 1;
}

static int battle_speed_from_level(int level)
{
    // Temporary server-side agility model until the exact original SA2
    // agility field/formula is identified. Higher level is intentionally
    // faster, while equal speed values are resolved by a random tie-break.
    level = std::max(1, level);
    return 40 + level * 5;
}

static int battle_damage_for_level(int level)
{
    // First non-constant damage model:
    //   Lv3 -> 7..9
    //   Lv5 -> 9..11
    //   Lv7 -> 11..13
    //
    // Keep this deliberately simple so it can later be replaced by the
    // original attack/defence formula without touching the turn system.
    level = std::max(1, level);
    return 4 + level + random_int(0, 2);
}

static std::string battle_action_name(std::uint32_t action)
{
    auto it = BATTLE_ACTION_NAMES.find(static_cast<int>(action));
    if (it != BATTLE_ACTION_NAMES.end())
        return it->second;

    return str("ACTION_", action);
}

static bool execute_planned_battle_round(
    const std::shared_ptr<Session>& session)
{
    std::vector<InitiativeBattleAction> actions;

    {
        std::lock_guard lock(session->state_mutex);

        // Defence lasts for exactly the round in which it was selected.
        // Clear ALL old defence before any action of the new round can resolve.
        // This avoids the old behaviour where a slow actor remained protected
        // during the next round until its own next action began.
        const bool had_old_defenders =
            !session->battle_defending_actors.empty();
        session->battle_defending_actors.clear();
        session->player_stats.defending = false;

        if (had_old_defenders)
            log_line("[KAMPF] Alte Verteidigungszustaende zu Rundenbeginn geloescht.");

        session->battle_roster_changed_this_round = false;

        // Player and pet orders are already committed at this point.
        for (std::uint32_t actor_id : session->battle_turn_order) {
            auto it = std::find_if(
                session->planned_battle_actions.begin(),
                session->planned_battle_actions.end(),
                [&](const PlannedBattleAction& a) {
                    return a.actor_id == actor_id;
                });

            if (it == session->planned_battle_actions.end())
                continue;

            const int level =
                battle_actor_level_locked(*session, actor_id);

            actions.push_back({
                *it,
                level,
                battle_speed_from_level(level),
                random_int(0, 1000000),
                false
            });
        }

        // Enemy AI also chooses its action BEFORE execution. All actors are
        // then resolved together by initiative instead of "our side first,
        // enemies afterwards".
        const std::size_t living_enemy_count =
            static_cast<std::size_t>(std::count_if(
                session->battle_enemies.begin(),
                session->battle_enemies.end(),
                [](const BattleEnemyState& enemy) {
                    return enemy.hp > 0;
                }));

        std::vector<std::uint32_t> living_player_side_targets;
        if (session->player_stats.current_hp > 0)
            living_player_side_targets.push_back(PLAYER_BATTLE_ACTOR_ID);

        for (std::uint32_t actor_id : session->battle_turn_order) {
            if (actor_id == PLAYER_BATTLE_ACTOR_ID)
                continue;

            auto pet_it = std::find_if(
                session->captured_pets.begin(),
                session->captured_pets.end(),
                [&](const CapturedPetState& pet) {
                    return pet.pet_id == actor_id;
                });

            if (pet_it != session->captured_pets.end() && pet_it->current_hp > 0)
                living_player_side_targets.push_back(actor_id);
        }

        for (const auto& enemy : session->battle_enemies) {
            if (enemy.hp <= 0)
                continue;

            // V144: use one explicit 0..99 roll for the REAL enemy AI path.
            // Previous versions also contain a later 0..99 block for action==150;
            // normal enemies do not reach that block because their action is
            // already chosen here. Keep the flee probability obvious and logged.
            const int roll = random_int(0, 99);
            static constexpr int ENEMY_FLEE_PERCENT = 20;
            static constexpr int ENEMY_ATTACK_PERCENT = 60;

            std::uint32_t action = 0;
            std::uint32_t target = enemy.actor_id;

            if (roll < ENEMY_FLEE_PERCENT) {
                action = 0x99;
                target = enemy.actor_id;
            }
            else if (roll < ENEMY_FLEE_PERCENT + ENEMY_ATTACK_PERCENT &&
                     !living_player_side_targets.empty()) {
                action = 3; // attack
                target = living_player_side_targets[
                    static_cast<std::size_t>(random_int(
                        0, static_cast<int>(living_player_side_targets.size() - 1)))];
            }
            else {
                action = 8; // defend
                target = enemy.actor_id;
            }

            log_line(str(
                "[GEGNER-AI V145] actor=0x",
                [&] { std::ostringstream os; os << std::hex << std::uppercase << enemy.actor_id; return os.str(); }(),
                ", roll=", roll,
                ", Aktion=", battle_action_name(action)));

            const int level = std::max(1, enemy.level);

            actions.push_back({
                PlannedBattleAction{
                    enemy.actor_id,
                    action,
                    target
                },
                level,
                battle_speed_from_level(level),
                random_int(0, 1000000),
                true
            });
        }
    }

    std::stable_sort(
        actions.begin(),
        actions.end(),
        [](const InitiativeBattleAction& a,
           const InitiativeBattleAction& b) {
            if (a.speed != b.speed)
                return a.speed > b.speed;
            return a.tie_break > b.tie_break;
        });

    {
        std::ostringstream os;
        os << "[INITIATIVE] Reihenfolge: ";

        for (std::size_t i = 0; i < actions.size(); ++i) {
            if (i) os << " -> ";

            const auto& entry = actions[i];
            os << "0x" << std::hex << std::uppercase
               << entry.order.actor_id
               << std::dec
               << "(Lv" << entry.level
               << ", SPD" << entry.speed
               << ", " << battle_action_name(entry.order.action)
               << ")";
        }

        log_line(os.str());
    }

    for (const auto& queued : actions) {

        const auto& planned = queued.order;
        const std::uint32_t actor_id = planned.actor_id;
        std::uint32_t action = planned.action;
        std::uint32_t target = planned.target_id;

        if (action == 150) {

            const bool is_enemy =
                (actor_id & 0xF0000000u) == 0x60000000u;

            const bool is_pet =
                (actor_id & 0xF0000000u) == 0x20000000u;

            std::vector<std::uint32_t> living_targets;

            {
                std::lock_guard lock(session->state_mutex);

                if (is_enemy) {
                    // Gegner darf Spieler + eigene Pets angreifen.

                    if (session->player_stats.current_hp > 0)
                        living_targets.push_back(
                            PLAYER_BATTLE_ACTOR_ID);

                    for (const auto& pet : session->captured_pets) {
                        if (pet.current_hp > 0)
                            living_targets.push_back(
                                pet.pet_id);
                    }
                }
                else if (is_pet) {
                    // Eigenes Pet darf lebende Gegner angreifen.

                    for (const auto& enemy :
                        session->battle_enemies) {

                        if (enemy.hp > 0)
                            living_targets.push_back(
                                enemy.actor_id);
                    }
                }
            }

            if (living_targets.empty()) {
                action = 0; // warten
            }
            else {
                const int roll = random_int(0, 99);

                if (is_enemy) {
                    if (roll < 70) {
                        action = 3;
                        // zufälliges Ziel
                    }
                    else if (roll < 90) {
                        action = 8;
                        target = actor_id;
                    }
                    else {
                        // V142: restore the enemy flee choice.  The action itself
                        // uses the older per-member flee Battle-ID below; do NOT
                        // change the shared enemy BattleInit group/facing.
                        action = 0x99;
                        target = actor_id;
                    }
                }
                else {
                    // eigene Pet-AI
                    if (roll < 80) {
                        action = 3;
                        // Gegner wählen
                    }
                    else {
                        action = 8;
                        target = actor_id;
                    }
                }
            }
        }

        // ----------------------------------------------------
        // ENEMY ACTION
        // ----------------------------------------------------
        if (queued.enemy) {
            bool enemy_still_alive = false;

            {
                std::lock_guard lock(session->state_mutex);
                enemy_still_alive = std::any_of(
                    session->battle_enemies.begin(),
                    session->battle_enemies.end(),
                    [&](const BattleEnemyState& enemy) {
                        return enemy.actor_id == actor_id && enemy.hp > 0;
                    });
            }

            // A faster actor may already have knocked this enemy out.
            if (!enemy_still_alive) {
                log_line(str(
                    "[INITIATIVE] Gegner 0x",
                    [&] {
                        std::ostringstream os;
                        os << std::hex << std::uppercase << actor_id;
                        return os.str();
                    }(),
                    " ist vor seinem Zug K.O.; Aktion entfaellt."));
                continue;
            }

            if (action == 3) {
                int real_damage =
                    battle_damage_for_level(queued.level);

                bool target_defending = false;
                bool lethal = false;
                bool player_dead = false;
                bool critical = false;
                bool miss = !(bool(random_int(0, MISS_HI)));
                bool UltimateKO = false;

                std::lock_guard lock(session->state_mutex);

                target_defending =
                    session->battle_defending_actors.count(target) != 0;

                if (miss)
                {
                    real_damage = 0;
                }
                else
                {

                    if (target_defending)
                        real_damage = std::max(1, real_damage / 2);

                    critical = !target_defending && !lethal &&
                        random_int(1, 100) <= CRITICAL_HIT_CHANCE_PERCENT;

                    if (critical && !target_defending)
                        real_damage *= 1.5;
                }

           

                if (target == PLAYER_BATTLE_ACTOR_ID) {
                    PlayerStatus saved_progress;

                    {
                        int remaining = std::max(0, session->player_stats.current_hp - real_damage);

                        if (session->player_stats.current_hp == session->player_stats.max_hp && remaining == 0)
                            UltimateKO = true;

                        session->player_stats.current_hp = remaining;

                        lethal = session->player_stats.current_hp == 0;
                        player_dead = lethal;

                        saved_progress = session->player_stats;
                    }

                    save_player_progress(saved_progress);

                }
                else {
                    auto pet_it = std::find_if(
                        session->captured_pets.begin(),
                        session->captured_pets.end(),
                        [&](const CapturedPetState& pet) {
                            return pet.pet_id == target;
                        });

                    if (pet_it != session->captured_pets.end()) {
                        const int old_hp = pet_it->current_hp;
                        pet_it->current_hp =
                            std::max(0, pet_it->current_hp - real_damage);

                        if(old_hp == pet_it->max_hp && pet_it-> current_hp == 0)
                            UltimateKO = true;

                        lethal = old_hp > 0 && pet_it->current_hp == 0;

                        if (lethal) {
                            // Pet K.O. is NOT player defeat.  Remove only this pet
                            // from future order phases; keep its BattleInit mapping
                            // so the lethal reaction can still address it correctly.
                            session->battle_defending_actors.erase(target);
                            session->battle_turn_order.erase(
                                std::remove(
                                    session->battle_turn_order.begin(),
                                    session->battle_turn_order.end(),
                                    target),
                                session->battle_turn_order.end());
                            session->battle_roster_changed_this_round = true;
                        }
                    }
                }

                Bytes attack = battle_attack_exchange_reply(
                    actor_id,
                    battle_slot_from_actor_id(*session, actor_id),
                    target,
                    battle_slot_from_actor_id(*session, target),
                    real_damage,
                    lethal,
                    target_defending,
                    critical,
                    miss,
                    UltimateKO);

                send_all(session, attack);

                log_line(str(
                    "[AUSGEFUEHRT] GEGNER-ANGRIFF actor=0x",
                    [&] {
                        std::ostringstream os;
                        os << std::hex << std::uppercase << actor_id;
                        return os.str();
                    }(),
                        ", Lv=", queued.level,
                        ", Schaden=", real_damage,
                        target_defending ? " [VERTEIDIGT]" : "",
                        critical ? " [KRITISCH]" : ""));

                std::this_thread::sleep_for(1500ms);

                if (player_dead) {
                    finish_battle_defeat(session);
                    return false;
                }

                
            }
            else if (action == 8) {
                {
                    std::lock_guard lock(session->state_mutex);
                    session->battle_defending_actors.insert(actor_id);
                }

                Bytes packet = battle_enemy_simple_action_reply(
                    actor_id,
                    battle_slot_from_actor_id(*session, actor_id),
                    0x08);

                send_all(session, packet);

                log_line(str(
                    "[AUSGEFUEHRT] GEGNER-VERTEIDIGEN actor=0x",
                    [&] {
                        std::ostringstream os;
                        os << std::hex << std::uppercase << actor_id;
                        return os.str();
                    }(),
                    ", SPD=", queued.speed,
                    "; Defend-State ist AB JETZT aktiv."));

                std::this_thread::sleep_for(1200ms);
            }
            else if (action == 0) {
                // Actual WAIT.  V136 accidentally routed this branch into 0x99.
                log_line(str(
                    "[AUSGEFUEHRT] GEGNER-WARTEN actor=0x",
                    [&] {
                        std::ostringstream os;
                        os << std::hex << std::uppercase << actor_id;
                        return os.str();
                    }()));
            }
            else if (action == 0x99) {
                // V142: Old versions that visually removed only one enemy used
                // 0x01000001 / 0x01000101 / ... for the flee action record.
                // This is intentionally different from the current BattleInit
                // compact ID; changing BattleInit itself would split the enemy
                // team and break facing again.
                const std::uint32_t flee_battle_id =
                    enemy_single_flee_battle_id(actor_id);

                Bytes packet = battle_enemy_simple_action_reply(
                    actor_id,
                    flee_battle_id,
                    0x99);

                send_all(session, packet);

                bool no_enemies_left = false;
                {
                    std::lock_guard lock(session->state_mutex);
                    auto& enemies = session->battle_enemies;
                    enemies.erase(
                        std::remove_if(
                            enemies.begin(),
                            enemies.end(),
                            [&](const BattleEnemyState& enemy) {
                                return enemy.actor_id == actor_id;
                            }),
                        enemies.end());

                    session->battle_defending_actors.erase(actor_id);
                    session->battle_roster_changed_this_round = true;

                    no_enemies_left = std::none_of(
                        enemies.begin(),
                        enemies.end(),
                        [](const BattleEnemyState& enemy) {
                            return enemy.hp > 0;
                        });
                }

                log_line(str(
                    "[AUSGEFUEHRT] GEGNER-FLUCHT actor=0x",
                    [&] { std::ostringstream os; os << std::hex << std::uppercase << actor_id; return os.str(); }(),
                    ", BattleInit-ID=0x",
                    [&] { std::ostringstream os; os << std::hex << std::uppercase
                                                   << battle_slot_from_actor_id(*session, actor_id); return os.str(); }(),
                    ", Flee-ID=0x",
                    [&] { std::ostringstream os; os << std::hex << std::uppercase
                                                   << flee_battle_id; return os.str(); }()));

                std::this_thread::sleep_for(1200ms);

                if (no_enemies_left)
                    return true;
            }

            continue;
        }

        // A pet that was knocked out by a faster enemy earlier in this same
        // committed round must not execute its already queued order afterwards.
        if ((actor_id & 0xF0000000u) == 0x20000000u) {
            bool pet_still_alive = false;
            {
                std::lock_guard lock(session->state_mutex);
                auto pet_it = std::find_if(
                    session->captured_pets.begin(),
                    session->captured_pets.end(),
                    [&](const CapturedPetState& pet) { return pet.pet_id == actor_id; });
                pet_still_alive =
                    pet_it != session->captured_pets.end() && pet_it->current_hp > 0;
            }

            if (!pet_still_alive) {
                log_line(str(
                    "[INITIATIVE] Eigenes Pet 0x",
                    [&] { std::ostringstream os; os << std::hex << std::uppercase << actor_id; return os.str(); }(),
                    " ist vor seinem Zug K.O.; Aktion entfaellt."));
                continue;
            }
        }

        // ----------------------------------------------------
        // ANGRIFF
        // ----------------------------------------------------

        if (action == 3) {

            int damage = battle_damage_for_level(queued.level);
            int remaining = 0;
            int enemy_max = 0;
            bool lethal = false;
            bool target_found = false;
            bool all_dead = false;
            bool target_defending = false;
            bool critical = false;
            std::uint32_t actual_target = target;
            bool retargeted = false;
            bool miss = false;
            bool UltimateKO = false;

            {
                std::lock_guard lock(session->state_mutex);

                auto enemy_it = std::find_if(
                    session->battle_enemies.begin(),
                    session->battle_enemies.end(),
                    [&](const BattleEnemyState& enemy) {
                        return enemy.actor_id == actual_target && enemy.hp > 0;
                    });

                // If an earlier actor in the SAME committed round already
                // knocked the chosen target out, do not send another normal
                // attack against an actor the client now considers dead.
                // Retarget to the first living enemy instead.
                if (enemy_it == session->battle_enemies.end()) {
                    enemy_it = std::find_if(
                        session->battle_enemies.begin(),
                        session->battle_enemies.end(),
                        [](const BattleEnemyState& enemy) {
                            return enemy.hp > 0;
                        });

                    if (enemy_it != session->battle_enemies.end()) {
                        actual_target = enemy_it->actor_id;
                        retargeted = actual_target != target;
                    }
                }

                if (enemy_it != session->battle_enemies.end()) {

                    target_found = true;
                    enemy_max = enemy_it->max_hp;

                    target_defending =
                        session->battle_defending_actors.count(actual_target) != 0;

                    if (target_defending)
                        damage = std::max(1, damage / 2);
  
                    miss = !(bool(random_int(0, MISS_HI)));

                    if (miss)
                    {
                        damage = 0;
                        lethal = false;
                    }

                    remaining = std::max(0, enemy_it->hp - damage);
                    lethal = enemy_it->hp > 0 && remaining == 0;

                    if (enemy_it->hp == enemy_it->max_hp && remaining == 0)
                        UltimateKO = true;

                    if (lethal)
                        session->battle_roster_changed_this_round = true;

                    enemy_it->hp = remaining;

                    all_dead = std::all_of(
                        session->battle_enemies.begin(),
                        session->battle_enemies.end(),
                        [](const BattleEnemyState& enemy) {
                            return enemy.hp <= 0;
                        });
                }
            }

            if (!target_found) {
                log_line(str(
                    "[KAMPF] Kein lebendes Angriffsziel mehr fuer actor=0x",
                    [&] {
                        std::ostringstream os;
                        os << std::hex << std::uppercase << actor_id;
                        return os.str();
                    }(),
                    "; Aktion entfaellt."));

                continue;
            }

            if (retargeted) {
                log_line(str(
                    "[KAMPF] Urspruengliches Ziel 0x",
                    [&] { std::ostringstream os; os << std::hex << std::uppercase << target; return os.str(); }(),
                    " ist bereits K.O.; actor=0x",
                    [&] { std::ostringstream os; os << std::hex << std::uppercase << actor_id; return os.str(); }(),
                    " greift stattdessen 0x",
                    [&] { std::ostringstream os; os << std::hex << std::uppercase << actual_target; return os.str(); }()));
            }

            critical = !target_defending && !lethal &&
                random_int(1, 100) <= CRITICAL_HIT_CHANCE_PERCENT;

            if (critical && !target_defending)
                damage *= 1.5;

            Bytes attack = battle_attack_exchange_reply(
                actor_id,
                battle_slot_from_actor_id(*session, actor_id),
                actual_target,
                battle_slot_from_actor_id(*session, actual_target),
                damage,
                lethal,
                target_defending,
                critical,
                miss,
                UltimateKO);

            send_all(session, attack);

            log_line(str(
                "[AUSGEFUEHRT] ANGRIFF actor=0x",
                [&] {
                    std::ostringstream os;
                    os << std::hex << std::uppercase << actor_id;
                    return os.str();
                }(),
                    " -> target=0x",
                    [&] {
                    std::ostringstream os;
                    os << std::hex << std::uppercase << actual_target;
                    return os.str();
                    }(),
                        ", Lv=",
                        queued.level,
                        ", Schaden=",
                        damage,
                        ", HP=",
                        remaining,
                        "/",
                        enemy_max,
                        target_defending ? " [VERTEIDIGT]" : "",
                        critical ? " [KRITISCH]" : ""));

            // Bei lethal Hits steckt CND=0x0020 bereits im NORMALEN
            // Angriffsrecord (Pas=0).  Kein zweites 0x9A-/Remove-Paket senden;
            // der Client soll nach seiner normalen Trefferanimation selbst
            // in den 0x58E5D0-Terminalcallback wechseln.
            if (lethal) {
                log_line(str(
                    "[K.O.-TEST] Normaler Trefferpfad: Pas=0, CND=0x0020 fuer target=0x",
                    [&] {
                        std::ostringstream os;
                        os << std::hex << std::uppercase << actual_target;
                        return os.str();
                    }()));
            }

            std::this_thread::sleep_for(1500ms);

            if (all_dead)
                return true;
        }

        // ----------------------------------------------------
        // VERTEIDIGEN
        // ----------------------------------------------------

        else if (action == 8) {

            {
                std::lock_guard lock(session->state_mutex);
                session->battle_defending_actors.insert(actor_id);
                if (actor_id == PLAYER_BATTLE_ACTOR_ID)
                    session->player_stats.defending = true;
            }

            // Use the fully addressed form for player AND pets.  The old
            // battle_simple_action_reply omitted the compact BattleInit ID.
            if (!planned.wire_order.empty()) {
                send_all(session, planned.wire_order);

                log_line(str(
                    "[GESENDET] VERTEIDIGUNGS-ORDER-ECHO 0x0B20 actor=0x",
                    [&] {
                        std::ostringstream os;
                        os << std::hex << std::uppercase << actor_id;
                        return os.str();
                    }(),
                        ": ", hexline(planned.wire_order)));
            }

            Bytes defend = battle_defend_reply(
                actor_id,
                battle_slot_from_actor_id(*session, actor_id));

            send_all(session, defend);

            log_line(str(
                "[AUSGEFUEHRT] VERTEIDIGEN actor=0x",
                [&] {
                    std::ostringstream os;
                    os << std::hex << std::uppercase << actor_id;
                    return os.str();
                }(),
                "; Defend-State fuer den Rest dieser Runde aktiv."));

            std::this_thread::sleep_for(1200ms);
        }

        // ----------------------------------------------------
        // FLUCHT
        // ----------------------------------------------------
        else if (action == 88) {
            BattleEnemyState captured_enemy{};
            bool target_found = false;
            std::uint32_t target_battle_id = 0;

            {
                std::lock_guard lock(session->state_mutex);

                auto enemy_it = std::find_if(
                    session->battle_enemies.begin(),
                    session->battle_enemies.end(),
                    [&](const BattleEnemyState& enemy) {
                        return enemy.actor_id == target;
                    });

                if (enemy_it != session->battle_enemies.end()) {
                    captured_enemy = *enemy_it;
                    target_found = true;

                    target_battle_id =
                        battle_slot_from_actor_id(*session, target);
                }
            }

            if (!target_found) {
                log_line(str(
                    "[FANGEN] Unbekanntes Ziel: actor_id=0x",
                    [&] {
                        std::ostringstream os;
                        os << std::hex << std::uppercase << target;
                        return os.str();
                    }()));

                continue;
            }

            // Fangchance wie bisher
            bool success =
                !(bool(random_int(
                    0,
                    session->battle_enemies.size())));

            Bytes capture = battle_capture_reply(
                target_battle_id,
                success,
                0);

            send_all(session, capture);

            log_line(str(
                "[AUSGEFUEHRT] FANGVERSUCH actor=0x",
                [&] {
                    std::ostringstream os;
                    os << std::hex << std::uppercase << actor_id;
                    return os.str();
                }(),
                    ", Ziel=",
                    captured_enemy.name,
                    ", CGNO=",
                    captured_enemy.cgno,
                    ", Erfolg=",
                    success ? "ja" : "nein",
                    ": ",
                    hexline(capture)));

            // Zeit für die Fang-Animation
            std::this_thread::sleep_for(2000ms);

            if (success) {
                bool all_dead = false;
                std::vector<CapturedPetState> captured_pets_snapshot;

                {
                    std::lock_guard lock(session->state_mutex);

                    auto& enemies = session->battle_enemies;

                    CapturedPetState pet{};

                    pet.pet_id = session->next_captured_pet_id++;
                    // Slots are compact client-side indices. Never preserve holes.
                    compact_captured_pet_slots(session->captured_pets);
                    pet.slot = static_cast<std::uint16_t>(session->captured_pets.size());
                    session->next_captured_pet_slot = static_cast<std::uint16_t>(
                        std::min<std::size_t>(65535, session->captured_pets.size() + 1));
                    pet.cgno = captured_enemy.cgno;
                    pet.level = std::max(1, captured_enemy.level);
                    pet.current_xp = 0;
                    pet.next_xp = pet_next_xp_for_level(pet.level);

                    pet.max_hp = 30 + pet.level * 10;
                    pet.current_hp = pet.max_hp;

                    pet.name = captured_enemy.name;

                    session->captured_pets.push_back(pet);
                    session->pending_captured_pet = pet;
                    captured_pets_snapshot = session->captured_pets;
                    session->battle_roster_changed_this_round = true;

                    enemies.erase(
                        std::remove_if(
                            enemies.begin(),
                            enemies.end(),
                            [&](const BattleEnemyState& enemy) {
                                return enemy.actor_id == target;
                            }),
                        enemies.end());

                    all_dead = std::all_of(
                        enemies.begin(),
                        enemies.end(),
                        [](const BattleEnemyState& enemy) {
                            return enemy.hp <= 0;
                        });
                }

                try {
                    save_captured_pets_state(captured_pets_snapshot);
                }
                catch (const std::exception& e) {
                    log_line(str(
                        "[WARNUNG] Gefangenes Pet konnte nicht gespeichert werden: ",
                        e.what()));
                }

                log_line(str(
                    "[FANGEN] ",
                    captured_enemy.name,
                    " dauerhaft gespeichert und aus Kampf entfernt; alle Gegner besiegt=",
                    all_dead ? "ja" : "nein"));

                // Falls der letzte Gegner gefangen wurde,
                // ist die Runde bzw. der Kampf gewonnen.
                if (all_dead)
                    return true;
            }
        }
        else if (action == 0x99) {

            Bytes flee = battle_enemy_simple_action_reply(
                actor_id,
                battle_slot_from_actor_id(*session, actor_id),
                0x99);

            send_all(session, flee);

            log_line(str(
                "[AUSGEFUEHRT] FLUCHT actor=0x",
                [&] {
                    std::ostringstream os;
                    os << std::hex << std::uppercase << actor_id;
                    return os.str();
                }()));

            // Spieler flieht → Kampf sofort beenden.
            if (actor_id == PLAYER_BATTLE_ACTOR_ID) {

                MoveState ms;

                {
                    std::lock_guard lock(session->state_mutex);

                    ms = session->move_state;

                    session->battle_active = false;
                    session->battle_order_phase_started = false;
                    session->player_sleeping = false;
                    session->encounter_block_until =
                        std::chrono::steady_clock::now() + 2000ms;
                    session->encounter_steps = std::max(session->encounter_steps, 32);
                    session->encounter_pet.reset();
                    session->battle_enemies.clear();
                    session->planned_battle_actions.clear();
                    session->battle_turn_order.clear();
                    session->battle_pet_actor_ids.clear();
                    session->battle_turn_index = 0;
                }

                Bytes end = battle_end_reply(
                    0x04,
                    ms.map,
                    ms.x,
                    ms.y);

                send_all(session, end);

                return false;
            }
        }

        // ----------------------------------------------------
        // NOCH UNBEKANNTE PET-SPEZIALAKTION
        // ----------------------------------------------------
        else if ((actor_id & 0xF0000000u) == 0x20000000u &&
                 action != 0 && action != 3 && action != 8 &&
                 action != 88 && action != 0x99 && action != 150) {
            log_line(str(
                "[PET-SPEZIAL-DIAG] Ausfuehrung noch nicht rekonstruiert: actor=0x",
                [&] { std::ostringstream os; os << std::hex << std::uppercase << actor_id; return os.str(); }(),
                ", action=", action,
                ", target=0x",
                [&] { std::ostringstream os; os << std::hex << std::uppercase << target; return os.str(); }()));
        }

        // ----------------------------------------------------
        // WARTEN
        // ----------------------------------------------------

        else if (action == 0) {
            log_line(str(
                "[AUSGEFUEHRT] WARTEN actor=0x",
                [&] {
                    std::ostringstream os;
                    os << std::hex << std::uppercase << actor_id;
                    return os.str();
                }()));
        }
    }

    return false;
}

static void finish_battle_turn(
    const std::shared_ptr<Session>& session,
    std::uint32_t actor_id,
    bool all_dead)
{
    if (!all_dead) {
        // All battle actions are sent serially before this function is called.
        if (send_pending_captured_pet(session)) {
            std::this_thread::sleep_for(150ms);
        }

        bool roster_changed = false;
        {
            std::lock_guard lock(session->state_mutex);

            session->planned_battle_actions.clear();
            session->battle_turn_index = 0;
            roster_changed = session->battle_roster_changed_this_round;
            session->battle_roster_changed_this_round = false;
        }

        // v121 proved that a K.O./roster change does NOT start the next
        // selection phase by itself: without 0x0BD1 the client simply waits.
        // Therefore every still-running battle round needs exactly one new
        // phase request here, regardless of whether somebody was knocked out.
        Bytes next = battle_order_phase_request_reply();
        send_all(session, next);

        {
            std::lock_guard lock(session->state_mutex);
            session->battle_order_phase_started = true;
        }

        log_line(str(
            roster_changed
                ? "[GESENDET] NEUE AUSWAHLPHASE 0x0BD1 (nach K.O./Roster-Aenderung): "
                : "[GESENDET] NEUE AUSWAHLPHASE 0x0BD1 (normale Folgerunde): ",
            hexline(next)));

        return;
    }

    MoveState ms;
    PlayerStatus old_progress;
    int xp_gain = 0;
    std::vector<BattleEnemyState> defeated_enemies;

    {
        std::lock_guard lock(session->state_mutex);

        ms = session->move_state;
        old_progress = session->player_stats;

        for (const auto& enemy : session->battle_enemies) {
            xp_gain += enemy.level * 10;

            if (enemy.hp <= 0)
                defeated_enemies.push_back(enemy);
        }
    }

    const std::size_t defeated_enemy_count = defeated_enemies.size();

    auto [new_progress, levels] =
        award_player_xp(old_progress, xp_gain);

    std::vector<CapturedPetState> pets_after_xp;
    std::vector<CapturedPetState> participating_pet_updates;
    std::vector<std::uint32_t> level_up_actor_ids;
    std::vector<std::string> pet_level_logs;

    if (levels > 0)
        level_up_actor_ids.push_back(actor_id);

    {
        std::lock_guard lock(session->state_mutex);
        for (auto& pet : session->captured_pets) {
            const bool participated =
                std::find(
                    session->battle_pet_actor_ids.begin(),
                    session->battle_pet_actor_ids.end(),
                    pet.pet_id) != session->battle_pet_actor_ids.end();
            if (!participated || pet.current_hp <= 0)
                continue;

            const int old_level = pet.level;
            const int gained_levels = award_pet_xp(pet, xp_gain);
            participating_pet_updates.push_back(pet);

            if (gained_levels > 0) {
                level_up_actor_ids.push_back(pet.pet_id);
                pet_level_logs.push_back(str(
                    pet.name, " -> Lv", pet.level,
                    " (+", gained_levels, "), XP ",
                    pet.current_xp, "/", pet.next_xp));
            }
            else {
                pet_level_logs.push_back(str(
                    pet.name, " Lv", old_level,
                    " XP ", pet.current_xp, "/", pet.next_xp));
            }
        }
        pets_after_xp = session->captured_pets;
    }

    try {
        save_captured_pets_state(pets_after_xp);
    }
    catch (const std::exception& e) {
        log_line(str("[WARNUNG] Pet-XP konnte nicht gespeichert werden: ", e.what()));
    }

    Bytes end = battle_victory_reply(
        actor_id,
        xp_gain,
        new_progress,
        participating_pet_updates,
        level_up_actor_ids,
        ms.map,
        ms.x,
        ms.y,
        ms.direction);

    send_all(session, end);

    log_line(str(
        "[PET-XP V180 0x0BE0] LevelCnt=",
        level_up_actor_ids.size(),
        ", CharaCnt=", 1 + participating_pet_updates.size(),
        ", Pets=", participating_pet_updates.size(),
        ", XP-Gewinn=", xp_gain));

    std::this_thread::sleep_for(1500ms);
    send_pending_captured_pet(session);

    {
        std::lock_guard lock(session->state_mutex);

        session->player_stats = new_progress;
        session->battle_active = false;
        session->battle_order_phase_started = false;
        session->player_sleeping = false;
        session->encounter_block_until =
            std::chrono::steady_clock::now() + 2000ms;
        session->encounter_steps = std::max(session->encounter_steps, 32);
        session->battle_enemies.clear();
        session->encounter_pet.reset();
        session->battle_turn_order.clear();
        session->battle_pet_actor_ids.clear();
        session->battle_turn_index = 0;
    }

    save_player_progress(new_progress);

    // Do not immediately re-send 0x0462 here: the full record replacement
    // would overwrite the progression/stats just applied by the battle result.

    std::this_thread::sleep_for(100ms);

    // Exactly one matching meat item per defeated enemy.
    std::size_t successful_drops = 0;
    std::size_t unsupported_drops = 0;

    for (std::size_t i = 0; i < defeated_enemies.size(); ++i) {
        const auto& enemy = defeated_enemies[i];
        const auto meat_item_no = meat_item_no_for_enemy_cgno(enemy.cgno);

        if (!meat_item_no) {
            ++unsupported_drops;
            log_line(str(
                "[ITEM-DROP] Kein bestaetigtes Fleisch fuer Gegner ",
                enemy.name,
                " (CGNO=", enemy.cgno, ")."));
        }
        else {
            log_line(str(
                "[ITEM-DROP] ", enemy.name,
                " (CGNO=", enemy.cgno,
                ") -> Fleisch ItemNo=", *meat_item_no));

            if (award_food_item_drop(session, *meat_item_no))
                ++successful_drops;
        }

        if (i + 1 < defeated_enemies.size())
            std::this_thread::sleep_for(50ms);
    }

    log_line(str(
        "[ITEM-DROP] Besiegte Gegner=", defeated_enemy_count,
        ", erfolgreich=", successful_drops,
        ", ohne bestaetigtes Fleisch=", unsupported_drops));

    // Refresh the normal character/status record after every battle, not only
    // after a level-up.  Battle actions update the battle HUD immediately, but
    // the character window otherwise keeps the last 0x0230 HP value.
    std::string character_name;
    {
        std::lock_guard lock(session->state_mutex);
        character_name = session->character_name;
    }
    Bytes player_status = player_status_sync_reply(new_progress, character_name);
    send_all(session, player_status);

    save_player_progress(session->player_stats);

    log_line(str(
        "[PLAYER-HP-SYNC V153] HP=", new_progress.current_hp,
        "/", new_progress.max_hp));

    if (levels > 0) {
        log_line(str(
            "[LEVEL-UP] Spieler +", levels,
            " Level, Skillpunkte=", new_progress.skill_points));
    }

    for (const auto& line : pet_level_logs)
        log_line(str("[PET-XP] ", line));

    log_line(str(
        "[GESENDET] KAMPFENDE SIEG 0x0BE0, XP=+",
        xp_gain,
        ", Level=",
        new_progress.level,
        ", Pet-XP-Updates=", participating_pet_updates.size(),
        ", Skillpunkte=", new_progress.skill_points));
}

static void activate_cheat_session(const std::shared_ptr<Session>& session,const std::string& reason) {
    std::lock_guard lock(active_session_mutex);
    auto current=active_cheat_session.lock();
    if (current==session) return;
    active_cheat_session=session;
    log_line(str("[CHEAT-ZIEL] Aktive Weltsitzung: Port ",session->port,", Client ",session->peer," (",reason,")"));
}

static bool maybe_start_random_encounter(
    const std::shared_ptr<Session>& session,
    int walked_fields,
    bool force = false)
{
    if (!force && walked_fields <= 0) return false;

    std::lock_guard lock(session->state_mutex);
    if (session->battle_active) return false;

    const auto now = std::chrono::steady_clock::now();
    if (now < session->encounter_block_until) {
        if (force || walked_fields > 0)
            log_line("[BEGEGNUNG] Nachkampf-Resync ignoriert; Encounter-Sperre noch aktiv.");
        return false;
    }

    auto map_it = ENCOUNTER_MAP_REGIONS.find(session->move_state.map);
    if (map_it == ENCOUNTER_MAP_REGIONS.end()) return false;

    auto battle_pets_it = ENCOUNTER_REGIONS.find(map_it->second);
    if (battle_pets_it == ENCOUNTER_REGIONS.end() || battle_pets_it->second.empty()) return false;

    if (!force) {
        session->encounter_steps -= std::min(walked_fields, 16);
        if (session->encounter_steps > 0) return false;
    }

    int max_num_of_enemies = 3;
    std::vector<ActorConfig> enemy_pets_config;
    std::vector<ActorConfig> captured_pets_config;
    std::vector<std::uint32_t> captured_pet_object_ids;

    int i_max = random_int(1, max_num_of_enemies);
    for (int i = 1; i <= i_max; i++)
    {
        size_t pet_index= static_cast<std::size_t>(random_int(0, static_cast<int>(battle_pets_it->second.size() - 1)));
        EncounterPet pet = battle_pets_it->second[pet_index];
        ActorConfig enemy_config;
        std::cout
        << "Region pets: " << battle_pets_it->second.size()
        << ", pet_index: " << pet_index
        << ", name: " << pet.name
        << ", cgno: " << pet.cgno
        << std::endl;
        enemy_config.cgno = pet.cgno;
        enemy_config.name = pet.name;
        enemy_config.level = random_int(3, 8);
        enemy_config.hp = std::max(10, enemy_config.level * 10);
        enemy_pets_config.push_back(enemy_config);
    }

    for (std::size_t captured_index = 0;
         captured_index < session->captured_pets.size();
         ++captured_index)
    {
        const CapturedPetState& captured_pet =
            session->captured_pets[captured_index];

        ActorConfig pet_config;
        pet_config.cgno = captured_pet.cgno;
        pet_config.name = captured_pet.name;
        pet_config.level = captured_pet.level;
        pet_config.hp = captured_pet.current_hp;
        pet_config.max_hp = captured_pet.max_hp;
        captured_pets_config.push_back(pet_config);
        captured_pet_object_ids.push_back(captured_pet.pet_id);

        log_line(str(
            "[BATTLE-PET-ID] Pet-Liste index=", captured_index,
            ", slot=", captured_pet.slot,
            ", object_id=0x",
            [&] { std::ostringstream os; os << std::hex << std::uppercase
                                            << captured_pet.pet_id; return os.str(); }(),
            ", compact_member=", captured_index,
            ", HP=", captured_pet.current_hp, "/", captured_pet.max_hp));
    }

    EncounterPet pet;
    pet.cgno = enemy_pets_config[i_max-1].cgno;
    pet.name = enemy_pets_config[i_max-1].name;
    pet.family = enemy_pets_config[i_max-1].cgno;
    int battle_map=session->encounter_battle_map;
    Bytes packet=battle_test_reply(
        session->player_stats,
        battle_map,
        enemy_pets_config,
        captured_pets_config,
        captured_pet_object_ids);
    initialize_battle_turn_order_locked(
        *session,
        captured_pet_object_ids);

    session->battle_active = true;
    session->player_sleeping = false;

    session->battle_enemy_hp =
        enemy_pets_config[i_max - 1].hp;

    session->battle_enemy_max_hp =
        enemy_pets_config[i_max - 1].hp;

    session->battle_enemy_level =
        enemy_pets_config[i_max - 1].level;

    session->battle_enemies.clear();

    for (std::size_t i = 0;
        i < enemy_pets_config.size();
        ++i) {

        const auto& cfg = enemy_pets_config[i];

        session->battle_enemies.push_back({
            0x60000015u + static_cast<std::uint32_t>(i),
            static_cast<std::uint8_t>(
                ENEMY_SEPARATE_FLEE_GROUPS ? (1 + i) : 1),
            static_cast<std::uint8_t>(
                ENEMY_SEPARATE_FLEE_GROUPS ? 0 : i),
            cfg.hp,
            cfg.hp,
            cfg.level,
            cfg.cgno,
            cfg.name
            });
    }

    session->encounter_steps = random_int(48, 64);
    session->encounter_pet = pet;

    // ERST JETZT BattleInit senden
    if (!send_all(session, packet))
        return false;
}

static bool process_sleep_tick(const std::shared_ptr<Session>& session)
{
    PlayerStatus progress;
    int old_hp = 0;
    int old_sp = 0;
    bool try_encounter = false;

    {
        std::lock_guard lock(session->state_mutex);

        if (!session->player_sleeping || session->battle_active)
            return false;

        const auto now = std::chrono::steady_clock::now();
        if (now < session->next_sleep_tick)
            return false;

        session->next_sleep_tick = now + SLEEP_TICK_INTERVAL;

        old_hp = session->player_stats.current_hp;
        old_sp = session->player_stats.current_sp;

        session->player_stats.current_hp = std::min(
            session->player_stats.max_hp,
            session->player_stats.current_hp + SLEEP_HP_REGEN);

        session->player_stats.current_sp = std::min(
            session->player_stats.max_sp,
            session->player_stats.current_sp + SLEEP_SP_REGEN);

        progress = session->player_stats;
        try_encounter = random_int(1, 20) <= SLEEP_ENCOUNTER_CHANCE_PERCENT;
    }

    save_player_progress(progress);

    log_line(str(
        "[SCHLAF] +",
        progress.current_hp - old_hp,
        " HP (",
        progress.current_hp,
        "/",
        progress.max_hp,
        "), +",
        progress.current_sp - old_sp,
        " SP (",
        progress.current_sp,
        "/",
        progress.max_sp,
        ")"));

    // Persisted server state alone is not enough: outside battle the client
    // otherwise keeps displaying the HP value from the last 0x0230/0x0B10
    // update. Send the already-proven character record immediately after a
    // regeneration tick so the world UI sees the new HP as well.
    std::string character_name;
    {
        std::lock_guard lock(session->state_mutex);
        character_name = session->character_name;
    }

    Bytes status = player_status_sync_reply(progress, character_name);
    if (send_all(session, status)) {
        log_line(str(
            "[SYNC] PLAYER STATUS 0x0230, HP=",
            progress.current_hp,
            "/",
            progress.max_hp,
            ", SP=",
            progress.current_sp,
            "/",
            progress.max_sp,
            ": ",
            hexline(status)));
    }

    if (!try_encounter)
        return false;

    // Unlike normal movement this is an encounter caused by sleeping, so
    // deliberately bypass the movement/encounter-step counter.
    if (maybe_start_random_encounter(session, 0, true)) {
        std::lock_guard lock(session->state_mutex);
        session->player_sleeping = false;
        log_line("[SCHLAF] Ueberfall! Schlafen beendet, Kampf gestartet.");
        return true;
    }

    // No encounter table exists for this map, so continue sleeping.
    return false;
}

static int wait_for_socket_readable(SocketHandle socket, int timeout_ms)
{
    fd_set read_fds;
    FD_ZERO(&read_fds);
    FD_SET(socket, &read_fds);

    timeval timeout{};
    timeout.tv_sec = timeout_ms / 1000;
    timeout.tv_usec = (timeout_ms % 1000) * 1000;

#ifdef _WIN32
    return select(0, &read_fds, nullptr, nullptr, &timeout);
#else
    return select(socket + 1, &read_fds, nullptr, nullptr, &timeout);
#endif
}

#ifdef _WIN32
static bool key_down(int vk) { return (GetAsyncKeyState(vk)&0x8000)!=0; }
#endif

static void arrow_key_cheat() {
#ifndef _WIN32
    log_line("[CHEAT] Globale Pfeiltasten sind nur unter Windows aktiv.");
    return;
#else
    struct KeyMove { int dx,dy,direction; const char* label; };
    const std::map<int,KeyMove> keys = {
        {VK_UP,{1,-1,6,"HOCH"}}, {VK_DOWN,{-1,1,2,"RUNTER"}},
        {VK_LEFT,{-1,-1,4,"LINKS"}}, {VK_RIGHT,{1,1,0,"RECHTS"}}
    };
    std::map<int,std::chrono::steady_clock::time_point> pressed_at;
    const std::map<int,std::tuple<int,int,int>> map_starts = {
        {'0',{100,150,150}}, {'1',{1,237,877}}, {'2',{2,1000,715}},
        {'3',{3,550,500}}, {'4',{4,200,150}}
    };
    std::map<int,bool> map_key_down; for (auto& [k,v]:map_starts) map_key_down[k]=false;
    std::map<int,bool> region_key_down; for (int i=0;i<(int)ENCOUNTER_REGION_NAMES.size();++i) region_key_down['1'+i]=false;
    std::map<int,bool> cycle_key_down{{VK_PRIOR,false},{VK_NEXT,false}};
    bool battle_key_down=false, encounter_battle_key_down=false, battle_start_key_down=false;
    std::vector<int> battle_maps; for (int id:EXPLORATION_MAPS) if (id>=15000 && id<=15999) battle_maps.push_back(id);

    log_line("[CHEAT] Pfeiltasten bewegen global; Umschalt+Pfeil = 5 Felder.");
    log_line("[KARTENTEST] Strg+0 = Halbol; Strg+1 bis Strg+4 = Aussenkarten.");
    log_line("[KARTENTEST] Strg+Bild hoch/runter = vorhandene Gebietskarten durchschalten.");
    log_line("[KAMPFKARTEN] Strg+B = 15xxx-Karten als Weltkarte ansehen.");
    log_line("[KAMPFKARTEN] Strg+Umschalt+B = Arena fuer den naechsten Kampf waehlen.");
    log_line("[KAMPFTEST] Strg+K = Kampf auf der ausgewaehlten Arena starten.");
    log_line("[BEGEGNUNGEN] Strg+Alt+1..8 ordnet die aktuelle Karte zu: 1 Badawal, 2 Glacier, 3 Namda, 4 Nazuth, 5 Notte, 6 Sanau, 7 Suna., 8 North Macca");

    while (running.load()) {
        std::this_thread::sleep_for(35ms);
        std::shared_ptr<Session> session;
        { std::lock_guard lock(active_session_mutex); session=active_cheat_session.lock(); }
        if (!session || session->closing.load()) continue;
        bool ctrl=key_down(VK_CONTROL), alt=key_down(VK_MENU), shift=key_down(VK_SHIFT);

        for (int i=0;i<(int)ENCOUNTER_REGION_NAMES.size();++i) {
            int key='1'+i; bool down=ctrl&&alt&&key_down(key);
            if (!down) { region_key_down[key]=false; continue; }
            if (region_key_down[key]) continue; region_key_down[key]=true;
            std::lock_guard state_lock(session->state_mutex);
            int map_id=session->move_state.map; const std::string& region=ENCOUNTER_REGION_NAMES[i];
            if (!ENCOUNTER_REGIONS.count(region)) { log_line(str("[BEGEGNUNGEN] Region ",region," fehlt im Katalog.")); continue; }
            ENCOUNTER_MAP_REGIONS[map_id]=region;
            try { save_encounter_map_regions(); session->encounter_steps=random_int(8,15); log_line(str("[BEGEGNUNGEN] Karte ",map_id," dauerhaft -> ",region,"; erster Testkampf nach etwa 8-15 Feldern.")); }
            catch (const std::exception& e) { log_line(str("[WARNUNG] Karten-Zuordnung nicht gespeichert: ",e.what())); }
        }

        bool battle_start_down=ctrl&&key_down('K');
        if (!battle_start_down) battle_start_key_down=false;
        else if (!battle_start_key_down) {
            battle_start_key_down=true;
            int target_map;
            {
                std::lock_guard state_lock(session->state_mutex);
                target_map=session->encounter_battle_map;
                session->battle_active=true;
                session->battle_enemy_hp=100;
                session->battle_enemy_max_hp=100;
                session->battle_enemy_level=1;
            }
            // The old Python hotkey still called the removed enemy_hp keyword.
            // Use the current multi-enemy BattleInit signature here as well.
            initialize_battle_turn_order(
                session,
                PETS.size());

            {
                std::lock_guard lock(session->state_mutex);

                session->planned_battle_actions.clear();
                session->battle_active = true;
            }

            Bytes packet = battle_test_reply(
                session->player_stats,
                target_map,
                ENEMIES);

            if (send_all(session, packet)) {
                log_line(str("[KAMPFTEST GESENDET] CMD = 0x0B10, Karte = ",target_map,", Nutzlast = ",packet.size()-6," Bytes: ",hexline(packet)));
            }
            else log_line("[KAMPFTEST] Verbindung beendet.");
        }

        bool encounter_battle_down=ctrl&&shift&&key_down('B');
        if (!encounter_battle_down) encounter_battle_key_down=false;
        else if (!encounter_battle_key_down && !battle_maps.empty()) {
            encounter_battle_key_down=true;
            std::lock_guard state_lock(session->state_mutex);
            int current=session->encounter_battle_map, selected=battle_maps.front();
            auto it=std::find(battle_maps.begin(),battle_maps.end(),current);
            if (it!=battle_maps.end()) selected=battle_maps[(std::distance(battle_maps.begin(),it)+1)%battle_maps.size()];
            session->encounter_battle_map=selected;
            log_line(str("[KAMPFARENA AUSGEWAEHLT] Karte ",selected,"; Strg+K testet sie sofort, der naechste Zufallskampf verwendet sie ebenfalls."));
        }

        bool battle_down=ctrl&&!shift&&key_down('B');
        if (!battle_down) battle_key_down=false;
        else if (!battle_key_down && !battle_maps.empty()) {
            battle_key_down=true;
            int target_map,target_x,target_y; std::string source;
            {
                std::lock_guard state_lock(session->state_mutex);
                auto& st=session->move_state; session->map_positions[st.map]={st.x,st.y};
                auto it=std::find(battle_maps.begin(),battle_maps.end(),st.map);
                target_map=(it==battle_maps.end())?battle_maps.front():battle_maps[(std::distance(battle_maps.begin(),it)+1)%battle_maps.size()];
                auto pos=session->map_positions.find(target_map);
                if (pos!=session->map_positions.end()) { target_x=pos->second.first; target_y=pos->second.second; source="gespeichert"; }
                else std::tie(target_x,target_y,source)=default_map_position(target_map);
                st.map=target_map; st.x=target_x; st.y=target_y; st.direction=4;
            }
            if (send_all(session,position_reply(target_map,target_x,target_y,4))) log_line(str("[KAMPFKARTE] Karte ",target_map,", Position ",target_x,":",target_y," (",source,")"));
        }

        for (const auto& [key,target]:map_starts) {
            bool down=ctrl&&!alt&&key_down(key);
            if (!down) { map_key_down[key]=false; continue; }
            if (map_key_down[key]) continue; map_key_down[key]=true;
            int target_map=std::get<0>(target), target_x, target_y;
            {
                std::lock_guard state_lock(session->state_mutex);
                auto& st=session->move_state; session->map_positions[st.map]={st.x,st.y};
                auto it=session->map_positions.find(target_map);
                if (it!=session->map_positions.end()) { target_x=it->second.first; target_y=it->second.second; }
                else { target_x=std::get<1>(target); target_y=std::get<2>(target); }
                st.map=target_map; st.x=target_x; st.y=target_y; st.direction=4;
            }
            if (send_all(session,position_reply(target_map,target_x,target_y,4))) log_line(str("[KARTENTEST] Karte ",target_map,", Position ",target_x,":",target_y));
        }

        for (auto [key,delta]:std::array<std::pair<int,int>,2>{{{VK_PRIOR,-1},{VK_NEXT,1}}}) {
            bool down=ctrl&&key_down(key); if (!down) { cycle_key_down[key]=false; continue; }
            if (cycle_key_down[key] || EXPLORATION_MAPS.empty()) continue; cycle_key_down[key]=true;
            int target_map,target_x,target_y,width,height; std::string source;
            {
                std::lock_guard state_lock(session->state_mutex); auto& st=session->move_state; session->map_positions[st.map]={st.x,st.y};
                auto it=std::find(EXPLORATION_MAPS.begin(),EXPLORATION_MAPS.end(),st.map);
                if (it!=EXPLORATION_MAPS.end()) {
                    int idx=static_cast<int>(std::distance(EXPLORATION_MAPS.begin(),it)); int n=static_cast<int>(EXPLORATION_MAPS.size()); target_map=EXPLORATION_MAPS[(idx+delta+n)%n];
                } else target_map=delta>0?EXPLORATION_MAPS.front():EXPLORATION_MAPS.back();
                std::tie(width,height)=EXPLORATION_MAP_SIZES[target_map];
                auto pos=session->map_positions.find(target_map);
                if (pos!=session->map_positions.end()) { target_x=pos->second.first; target_y=pos->second.second; source="gespeichert"; }
                else std::tie(target_x,target_y,source)=default_map_position(target_map);
                st.map=target_map; st.x=target_x; st.y=target_y; st.direction=4;
            }
            if (send_all(session,position_reply(target_map,target_x,target_y,4))) log_line(str("[KARTENTEST] Karte ",target_map," (",width,"x",height,"), Position ",target_x,":",target_y," (",source,")"));
        }

        auto now=std::chrono::steady_clock::now();
        for (const auto& [key,mv]:keys) {
            bool down=key_down(key); if (!down) { pressed_at.erase(key); continue; }
            auto it=pressed_at.find(key); if (it!=pressed_at.end() && now-it->second<90ms) continue; pressed_at[key]=now;
            int step=key_down(VK_SHIFT)?5:1; int map,x,y;
            {
                std::lock_guard state_lock(session->state_mutex); auto& st=session->move_state;
                st.x=clamp_value(st.x+mv.dx*step,-32768,32767); st.y=clamp_value(st.y+mv.dy*step,-32768,32767); st.direction=mv.direction;
                map=st.map; x=st.x; y=st.y;
            }
            if (send_all(session,position_reply(map,x,y,mv.direction))) log_line(str("[CHEAT ",mv.label,"] Karte ",map,", Position ",x,":",y," (Schritt ",step,")"));
        }
    }
#endif
}


static void client_thread(const SocketHandle & socket,int port,const fs::path& log_dir,const std::string& peer) {

    bool character_entered = false;
    auto session=std::make_shared<Session>(); session->socket=socket; session->port=port; session->peer=peer;
    session->player_stats=load_player_progress();
    session->inventory_items.clear();

    for (auto item : session->player_stats.items)
    {
        auto existing = std::find_if(
            session->inventory_items.begin(),
            session->inventory_items.end(),
            [&](const InventoryItemState& stack) {
                return stack.item_no == item.item_no;
            });

        if (existing != session->inventory_items.end()) {
            const unsigned int merged =
                static_cast<unsigned int>(existing->quantity) +
                static_cast<unsigned int>(item.quantity);

            existing->quantity = static_cast<std::uint16_t>(
                std::min<unsigned int>(
                    merged,
                    std::numeric_limits<std::uint16_t>::max()));
            continue;
        }

        if (session->inventory_items.size() >= 0x28)
            break;

        item.object_id = session->next_inventory_item_id++;
        session->inventory_items.push_back(item);
    }

    session->player_stats.items = session->inventory_items;

    log_line(str(
        "[INVENTAR] ",
        session->inventory_items.size(),
        " gespeicherte Items geladen."));
    session->move_state = load_player_position();
    restore_captured_pets(*session);
    session->encounter_steps=random_int(18,32);
    session->encounter_battle_map=12000;
    for (int id:EXPLORATION_MAPS) if (id>=15000 && id<=15999) { session->encounter_battle_map=id; break; }

    fs::path out=log_dir/(stamp()+"_port"+std::to_string(port)+".bin");
    log_line(str("\n[VERBUNDEN] ",peer," -> Port ",port));
    Bytes pending;
    int current_map = session->move_state.map;
    WarpTarget return_target{100,150,150,4};
    auto last_warp_at=std::chrono::steady_clock::time_point{};
    int last_warp_event_id = -1;
    bool awaiting_map_sync = false;
    bool captured_pet_list_sent = false;
    bool inventory_sent = false;
    std::optional<Bytes> last_pet_action_packet;
    std::optional<int> pet_spawned_map,pet_x,pet_y;

    try {
        std::array<std::uint8_t,65536> buffer{};
        while (running.load() && !session->closing.load()) {



            // The old code performed the sleep check immediately before a blocking
            // recv(). If the client sent no packets while sleeping, recv() blocked
            // forever and the once-per-second regeneration never ran.
            if (process_sleep_tick(session))
                continue;

            // Wake the loop periodically even when the client sends nothing.
            // This is what makes the sleep timer actually tick.
            int ready = wait_for_socket_readable(socket, 100);
            if (ready < 0)
                break;
            if (ready == 0)
                continue;

#ifdef _WIN32
            int n=recv(socket,reinterpret_cast<char*>(buffer.data()),static_cast<int>(buffer.size()),0);
#else
            ssize_t n=recv(socket,buffer.data(),buffer.size(),0);
#endif
            if (n<=0) break;
            {
                std::ofstream f(out,std::ios::binary|std::ios::app);
                f.write(reinterpret_cast<const char*>(buffer.data()),n);
            }
            Bytes data(buffer.begin(),buffer.begin()+n);
            log_line(str("[EMPFANGEN Port ",port,"] ",n," Bytes: ",hexline(data)));
            pending.insert(pending.end(),data.begin(),data.end());

            while (pending.size()>=6) {
                std::uint16_t size1=read_u16(pending,0), size2=read_u16(pending,2), command=read_u16(pending,4);
                if (size1!=size2 || size1<6) { log_line("[WARNUNG] Unbekannter Paketheader; automatische Antwort ausgesetzt."); pending.clear(); break; }
                if (pending.size()<size1) break;
                Bytes packet(pending.begin(),pending.begin()+size1); pending.erase(pending.begin(),pending.begin()+size1);
                { std::ostringstream os; os<<"[PAKET] CMD=0x"<<std::hex<<std::uppercase<<std::setw(4)<<std::setfill('0')<<command<<std::dec<<", Groesse="<<size1; log_line(os.str()); }

                if (command==0x0010) {
                    Bytes reply=version_reply(); send_all(session,reply); log_line(str("[GESENDET] VERSION OK, seed=0x00000000, type=0: ",hexline(reply)));
                } else if (command==0x0100) {
                    Bytes reply=login_reply(); send_all(session,reply); log_line(str("[GESENDET] LOGIN OK, result=18: ",hexline(reply)));
                } else if (command==0x0220) {
                    //send_all(session, clear_character_rename_permissions());

                    Bytes reply = character_list_reply(created_character_record);

                    send_all(session, reply);
                    
                    if (created_character_record) {
                        const std::uint32_t key =
                            read_u32(*created_character_record, 0x02);

                        std::ostringstream os;
                        os << "[CHAR-RENAME-KEY] record+0x02 = 0x"
                            << std::hex << std::uppercase << key;
                        log_line(os.str());
                    }

                    if (created_character_record) {
                        session->player_stats.name =
                            read_string(*created_character_record, 0x02, 15);
                    }

                    log_line(str(created_character_record?"[GESENDET] CHARLIST mit 1 Charakter: ":"[GESENDET] CHARLIST leer, count=0: ",hexline(reply)));
                } else if (command==0x0200) {
                    created_character_record=character_record_from_create(packet); save_character_state(*created_character_record);
                    log_line(str("[V",PROGRAM_VERSION,"] Charaktereintrag vorbereitet: ",created_character_record->size()," Bytes"));
                    Bytes reply=character_create_reply(); send_all(session,reply); log_line(str("[GESENDET] CHARCREATE OK, result=1: ",hexline(reply)));
                    std::this_thread::sleep_for(250ms); reply=character_list_reply(created_character_record); send_all(session,reply); log_line(str("[GESENDET] CHARLIST nach Erstellung, count=1: ",hexline(reply)));
                } else if (command==0x0230) {

                    character_entered = true;

                    activate_cheat_session(session,"Charakter betreten");
                    Bytes character_payload = slice(packet,6);
                    {
                        std::lock_guard lock(session->state_mutex);
                        session->character_name = character_name_from_payload(character_payload);
                    }
                    Bytes reply=character_enter_reply(character_payload,session->player_stats); send_all(session,reply);
                    log_line(str("[GESENDET] CHAR ENTER mit persistentem Stand: Level=",session->player_stats.level,", XP=",session->player_stats.current_xp,"/",session->player_stats.next_xp,", 253 Bytes: ",hexline(reply)));
                    MoveState position;

                    {
                        std::lock_guard lock(session->state_mutex);
                        position = session->move_state;
                    }

                    std::this_thread::sleep_for(50ms);

                    reply = position_reply(
                        position.map,
                        position.x,
                        position.y,
                        position.direction);

                    send_all(session, reply);

                    log_line(str(
                        "[GESENDET] GESPEICHERTE POSITION 0x0410: Karte ",
                        position.map,
                        ", Position ",
                        position.x,
                        ":",
                        position.y,
                        ", Richtung ",
                        position.direction,
                        ": ",
                        hexline(reply)));

                    // Do not send 0x0462 pet records yet.  The Chinese client is
                    // still completing its world-entry handshake here.  The known
                    // working sequence is 0x0230 -> initial 0x0410 -> client 0x0900
                    // -> server 0x0900 -> pet list.
                }
                else if (command == 0x0260) {
                    Bytes payload = slice(packet, 6);

                    std::uint32_t character_id = read_u32(payload, 0);
                    std::uint16_t name_len = read_u16(payload, 4);

                    std::string new_name;
                    for (std::size_t i = 0; i < name_len && 6 + i < payload.size(); ++i) {
                        if (payload[6 + i] == 0)
                            break;
                        new_name.push_back(static_cast<char>(payload[6 + i]));
                    }

                    log_line(str(
                        "[CHAR-RENAME] ID=", character_id,
                        ", Neuer Name='", new_name, "'"));

                    Bytes reply = character_rename_reply(character_id, true);
                    send_all(session, reply);
                }
                else if (command==0x0410) {
                    activate_cheat_session(session,"Bewegung 0x0410");
                    log_line(str("[BEWEGUNG] ",describe_move(packet)));
                    int old_map,old_x,old_y,new_map,new_x,new_y,dir;
                    {
                        std::lock_guard lock(session->state_mutex);
                        if (session->battle_active) { log_line("[KAMPF] Weltbewegung 0x0410 waehrend BattleInit ignoriert; Arena/Kamera bleibt unveraendert."); continue; }
                        old_map=session->move_state.map; old_x=session->move_state.x; old_y=session->move_state.y;
                        session->player_sleeping = false;
                        if (packet.size()>=18) {
                            session->move_state.map=read_u16(packet,10); session->move_state.x=read_i16(packet,12); session->move_state.y=read_i16(packet,14);
                            session->move_state.direction=packet[16]; session->move_state.flags=packet[17];
                            if (session->move_state.map!=current_map) { current_map=session->move_state.map; log_line(str("[KARTE] Client meldet Karte ",current_map,"; Serverstatus angepasst.")); }
                        }
                        new_map=session->move_state.map; new_x=session->move_state.x; new_y=session->move_state.y; dir=session->move_state.direction;
                    }
                    send_all(session,packet); log_line(str("[GESENDET] MOVE ECHO 0x0410: ",hexline(packet)));
                    if (pet_spawned_map && *pet_spawned_map==current_map && old_map==current_map && (!pet_x || !pet_y || *pet_x!=old_x || *pet_y!=old_y)) {
                        auto pos=close_trailing_position(old_x,old_y,new_x,new_y); pet_x=pos.first; pet_y=pos.second; Bytes reply=test_pet_position_reply(current_map,*pet_x,*pet_y); send_all(session,reply); log_line(str("[PET-FOLGE] Bbaros -> ",*pet_x,":",*pet_y));
                    }
                    int walked=old_map==new_map?std::max(std::abs(new_x-old_x),std::abs(new_y-old_y)):0;
                    if (maybe_start_random_encounter(session,walked)) continue;
                } else if (command==0x0510) {
                    Bytes payload=slice(packet,6);
                    if (payload.size()<2) {
                        log_line("[WARNUNG] ITEM-INFO 0x0510 ohne Nutzdaten.");
                    } else if (payload.size()==2) {
                        // Type-only request: WORD ItemNo.  Do not attach an
                        // arbitrary inventory object ID to this reply.
                        const std::uint16_t item_no=read_u16(payload,0);
                        const auto& entry=item_catalog_entry(item_no);
                        Bytes reply=item_info_reply(0u,item_no);
                        send_all(session,reply);
                        log_line(str("[ITEM-INFO V162 0x0510/TYP] ItemNo=",item_no,
                            ", object_id=0x0, Bild=",entry.picture_no,
                            ", Kategorie=",entry.category,
                            ", Anfrage=",hexline(payload),
                            ", Antwort=",hexline(reply)));
                    } else {
                        // Object request: DWORD ObjectID.  Resolve ItemNo from
                        // the exact inventory object instead of interpreting
                        // the low WORD of the object ID as an ItemNo.
                        const std::uint32_t object_id=read_u32(payload,0);
                        const auto item_no=inventory_item_no_for_object_id(session,object_id);
                        if (!item_no) {
                            log_line(str("[WARNUNG] ITEM-INFO V162 0x0510/OBJEKT fuer unbekannte ObjectID=0x",
                                [&]{std::ostringstream os; os<<std::hex<<std::uppercase<<object_id; return os.str();}(),
                                ", Payload=",hexline(payload)));
                        } else {
                            const auto& entry=item_catalog_entry(*item_no);
                            Bytes reply=item_info_reply(object_id,*item_no);
                            send_all(session,reply);
                            log_line(str("[ITEM-INFO V162 0x0510/OBJEKT] object_id=0x",
                                [&]{std::ostringstream os; os<<std::hex<<std::uppercase<<object_id; return os.str();}(),
                                ", ItemNo=",*item_no,
                                ", Bild=",entry.picture_no,
                                ", Kategorie=",entry.category,
                                ", Anfrage=",hexline(payload),
                                ", Antwort=",hexline(reply)));
                        }
                    }
                } else if (command==0x0463) {
                    Bytes payload = slice(packet, 6);
                    log_line(str("[PET-AKTION V179] ", describe_pet_action(packet)));
                    last_pet_action_packet = packet;

                    if (payload.size() < 16) {
                        log_line("[WARNUNG] PET-AKTION 0x0463 hat weniger als 16 Nutzdatenbytes.");
                    } else {
                        const std::uint32_t pet_id   = read_u32(payload, 0x00);
                        const std::uint32_t action   = read_u32(payload, 0x04);
                        const std::uint32_t option   = read_u32(payload, 0x08);
                        const std::uint32_t owner_id = read_u32(payload, 0x0C);

                        if (action == 8) {
                            // Verified from SendPetAct: option is the selected item object ID.
                            auto pet = captured_pet_snapshot(session, pet_id);
                            auto consumed = consume_inventory_item_for_pet(session, option);

                            if (!pet) {
                                log_line(str(
                                    "[PET-FUETTERN V171] Unbekannte Pet-ID 0x",
                                    [&]{std::ostringstream os; os<<std::hex<<std::uppercase<<pet_id; return os.str();}()));
                            } else if (!consumed) {
                                log_line(str(
                                    "[PET-FUETTERN V171] Item-ObjectID 0x",
                                    [&]{std::ostringstream os; os<<std::hex<<std::uppercase<<option; return os.str();}(),
                                    " ist serverseitig nicht im Inventar."));
                            } else {
                                // V179: all three category-1 feeding reactions are now
                                // identified.  Select the result server-side from the
                                // pet family and the consumed item.
                                const std::uint32_t result_category = 1;
                                const std::uint32_t result_action =
                                    feeding_reaction_action(pet->cgno, consumed->item_no);
                                const std::uint32_t result_option = 0;
                                const char* reaction_name =
                                    result_action == 15 ? "GLUECKLICH_GEGESSEN" :
                                    result_action == 12 ? "WUETEND_NICHT_GEGESSEN" :
                                                          "MAG_ES_NICHT";

                                Bytes reply = pet_action_reply(
                                    pet_id,
                                    owner_id,
                                    result_category,
                                    result_action,
                                    result_option);
                                send_all(session, reply);

                                // The Chinese 0x04B2 handler removes the inventory
                                // object unconditionally; it does NOT decrement a stack.
                                // Therefore refresh the same object via 0x04B0 while a
                                // quantity remains, and send 0x04B2 only for the last unit.
                                const auto remaining_stack =
                                    inventory_item_snapshot_by_object_id(session, option);

                                Bytes inventory_reply;
                                if (remaining_stack) {
                                    inventory_reply = item_have_reply({ *remaining_stack });
                                } else {
                                    inventory_reply = item_consumed_reply(option);
                                }
                                send_all(session, inventory_reply);

                                log_line(str(
                                    "[PET-FUETTERN V180] Pet=0x",
                                    [&]{std::ostringstream os; os<<std::hex<<std::uppercase<<pet_id; return os.str();}(),
                                    ", PetCGNO=", pet->cgno,
                                    ", ItemObject=0x",
                                    [&]{std::ostringstream os; os<<std::hex<<std::uppercase<<option; return os.str();}(),
                                    ", ItemNo=", consumed->item_no,
                                    ", AntwortOwner=0x",
                                    [&]{std::ostringstream os; os<<std::hex<<std::uppercase<<owner_id; return os.str();}(),
                                    ", cat=", result_category,
                                    ", act=", result_action,
                                    ", opt=", result_option,
                                    ", Reaktion=", reaction_name,
                                    ", RactosFamilie=", is_ractos_family(pet->cgno) ? "ja" : "nein",
                                    ", Pflanzenfutter=", is_test_plant_food(consumed->item_no) ? "ja" : "nein",
                                    ", Reaktionspaket=", hexline(reply),
                                    ", InventarUpdate=", hexline(inventory_reply)));

                                PlayerStatus saved_progress;

                                {
                                    std::lock_guard lock(session->state_mutex);
                                    saved_progress = session->player_stats;
                                }

                                save_player_progress(saved_progress);
                            }
                        } else {
                            // Preserve a structurally valid server reply for other pet actions.
                            Bytes reply = pet_action_reply(pet_id, owner_id, 0, action, option);
                            send_all(session, reply);
                            log_line(str(
                                "[GESENDET] PET-AKTION V179 0x0463 (5-DWORD): ",
                                hexline(reply)));
                        }
                    }
                } else if (command==0x0401) {
                    std::optional<std::uint32_t> requested; if (packet.size()>=10) requested=read_u32(packet,6);
                    if (requested) { std::ostringstream os; os<<"[OBJEKT-ANFRAGE] ID=0x"<<std::hex<<std::setw(8)<<std::setfill('0')<<*requested; log_line(os.str()); }
                    else log_line("[OBJEKT-ANFRAGE] ungueltiges Paket");
                    if (requested) {
                        if (auto pet = captured_pet_snapshot(session, *requested)) {
                            Bytes reply = captured_pet_object_reply(*pet);
                            send_all(session, reply);
                            log_line(str(
                                "[GESENDET] GEFANGENES PET 0x0401, ID=0x",
                                [&]{std::ostringstream os; os<<std::hex<<std::uppercase<<pet->pet_id; return os.str();}(),
                                ", Name=", pet->name,
                                ", HP=", pet->current_hp, "/", pet->max_hp,
                                ", Level=", pet->level,
                                ": ", hexline(reply)));
                            continue;
                        }
                    }

                    if (requested && *requested==TEST_PET_ID) {
                        if (!pet_spawned_map || *pet_spawned_map!=current_map) {
                            Bytes reply=test_pet_object_reply(); send_all(session,reply); log_line(str("[GESENDET] PET-DATENSATZ 0x0401, ID=0x20000001: ",hexline(reply)));
                            int mx,my,mm; { std::lock_guard lock(session->state_mutex); mm=session->move_state.map; mx=session->move_state.x; my=session->move_state.y; }
                            pet_x=std::max(-32768,mx-1); pet_y=my; std::this_thread::sleep_for(50ms); reply=test_pet_position_reply(mm,*pet_x,*pet_y); send_all(session,reply); pet_spawned_map=current_map;
                            log_line(str("[GESENDET] PET-SPAWN 0x0410: Karte ",mm,", Position ",*pet_x,":",*pet_y,": ",hexline(reply)));
                        } else log_line("[PET-ANFRAGE GEDROSSELT] Bbaros existiert bereits auf dieser Karte; keine erneute Antwort/Aktionsschleife.");
                    }
                } else if (command==0x0412) {

                    activate_cheat_session(session,"Weltpfad 0x0412");

                    // IMPORTANT: discard battle-time world/status packets BEFORE
                    // looking at byte 13.  Previously a battle packet whose byte
                    // 13 happened to be 0x0F could leave player_sleeping=true;
                    // process_sleep_tick() would then force a new encounter as
                    // soon as the previous battle ended, even while standing still.
                    {
                        std::lock_guard lock(session->state_mutex);
                        if (session->battle_active) {
                            session->player_sleeping = false;
                            log_line("[KAMPF] Weltpfad 0x0412 waehrend BattleInit komplett ignoriert; kein Schlaf-/Encounter-Status uebernommen.");
                            continue;
                        }
                    }

                    if (packet.size() <= 13) {
                        log_line("[WARNUNG] 0x0412 ist zu kurz, um das Aktions-Flag bei Byte 13 zu lesen.");
                        continue;
                    }

                    std::uint8_t flags = packet[13];

                    {
                        std::lock_guard lock(session->state_mutex);

                        if (flags == 0x0F)
                        {
                            session->player_sleeping = true;
                            session->next_sleep_tick =
                                std::chrono::steady_clock::now() + SLEEP_TICK_INTERVAL;
                            log_line("[SCHLAF] Schlaf-Aktion erkannt (Byte 13 = 0x0F).");
                        }
                        else
                        {
                            session->player_sleeping = false;
                        }
                    }
                    log_line(str("[PFAD] komprimiertes 0x0412, ",size1," Bytes: ",hexline(packet)));
                    Bytes payload=slice(packet,6);
                    int old_map,old_x,old_y;
                    { std::lock_guard lock(session->state_mutex); old_map=session->move_state.map; old_x=session->move_state.x; old_y=session->move_state.y; }
                    try {
                        bool map_sync_without_absolute=awaiting_map_sync && !payload.empty() && (payload[0]&0x01) && !(payload[0]&0x02);
                        int nm,nx,ny;
                        {
                            std::lock_guard lock(session->state_mutex); apply_compressed_move(payload,session->move_state);
                            if (map_sync_without_absolute) { session->move_state.x=old_x; session->move_state.y=old_y; log_line("[KARTEN-SYNC] Relative Ladeverschiebung nicht als Bewegung uebernommen."); }
                            if (awaiting_map_sync && !payload.empty() && (payload[0]&0x01)) awaiting_map_sync=false;
                            current_map=session->move_state.map; nm=session->move_state.map; nx=session->move_state.x; ny=session->move_state.y;
                        }
                        log_line(str("[PFAD DEKODIERT] Karte ",current_map,", Position ",nx,":",ny,", Maske=0x", [&]{std::ostringstream o;o<<std::hex<<std::uppercase<<std::setw(2)<<std::setfill('0')<<(payload.empty()?0:unsigned(payload[0]));return o.str();}()));
                        if (pet_spawned_map && *pet_spawned_map==current_map && old_map==current_map && (!pet_x || !pet_y || *pet_x!=old_x || *pet_y!=old_y) && (nx!=old_x || ny!=old_y)) {
                            auto pos=close_trailing_position(old_x,old_y,nx,ny); pet_x=pos.first; pet_y=pos.second; Bytes reply=test_pet_position_reply(current_map,*pet_x,*pet_y); send_all(session,reply); log_line(str("[PET-FOLGE] Bbaros -> ",*pet_x,":",*pet_y));
                        }
                        int walked=old_map==nm?std::max(std::abs(nx-old_x),std::abs(ny-old_y)):0;
                        const bool event_or_status_packet =
                            !payload.empty() && (payload[0] & 0x80) != 0;

                        if (walked > 0) {
                            int steps_left = 0;
                            {
                                std::lock_guard lock(session->state_mutex);
                                steps_left = session->encounter_steps;
                            }
                            log_line(str("[BEGEGNUNG] 0x0412 Distanz=", walked,
                                         ", Restschritte vor Abzug=", steps_left,
                                         event_or_status_packet ? " [STATUS/EVENT -> kein Abzug]" : ""));
                        }

                        if (!event_or_status_packet &&
                            maybe_start_random_encounter(session, walked))
                            continue;
                    } catch (const std::exception& e) { log_line(str("[WARNUNG] 0x0412 konnte nicht dekodiert werden: ",e.what())); }

                    const auto event_offset =
                        compressed_move_event_offset(payload);

                    if (event_offset && *event_offset+4<=payload.size()) {
                        int event_id=read_u16(payload,*event_offset), guard=read_u16(payload,*event_offset+2);
                        if (guard!=0) { log_line(str("[KEIN WARP] 0x0412-Statuspaket, event_guard=",guard)); continue; }
                        log_line(str("[WARP-ANFRAGE] Karte ",current_map,", Event-ID ",event_id));
                        std::optional<WarpTarget> target;
                        if (current_map == 1) {
                            if (auto it = NORTH_MACCA_EXITS.find(event_id); it != NORTH_MACCA_EXITS.end()) target = it->second;
                        }
                        else if (current_map == 1000) {
                            if (auto it = BADAWAL_EXITS0.find(event_id); it != BADAWAL_EXITS0.end()) target = it->second;
                        }
                        else if (current_map == 1001) {
                            if (auto it = BADAWAL_EXITS1.find(event_id); it != BADAWAL_EXITS1.end()) target = it->second;
                        }
                        else if (current_map == 1002) {
                            if (auto it = BADAWAL_EXITS2.find(event_id); it != BADAWAL_EXITS2.end()) target = it->second;
                        }
                        else if (current_map == 1003) {
                            if (auto it = BADAWAL_EXITS3.find(event_id); it != BADAWAL_EXITS3.end()) target = it->second;
                        }
                        else if (current_map == 1004) {
                            if (auto it = BADAWAL_EXITS4.find(event_id); it != BADAWAL_EXITS4.end()) target = it->second;
                        }
                        else if (current_map==100) {
                            if (auto it=HALBOL_INTERIORS.find(event_id); it!=HALBOL_INTERIORS.end()) target=it->second;
                            else if (auto it2=HALBOL_OUTDOOR_EXITS.find(event_id); it2!=HALBOL_OUTDOOR_EXITS.end()) target=it2->second;
                            if (old_map==100 && old_x>=0&&old_x<4096&&old_y>=0&&old_y<4096) { return_target={100,old_x,old_y,4}; log_line(str("[RUECKKEHR GEMERKT] Event ",event_id,": letzte begehbare Position ",old_x,":",old_y)); }
                            else { return_target={100,150,150,4}; log_line(str("[WARNUNG] Rueckkehrposition ",old_x,":",old_y," unplausibel; verwende sicheren Dorfstart.")); }
                        } else if (current_map==10006 && (((old_x>=34&&old_x<=37)&&(old_y>=13&&old_y<=22)) || event_id==DEN_PORTAL_EVENT)) {
                            target=DEN_ENTRY_TARGET; log_line(str("[DEN-RANDZONE] Oestlicher schwarzer Durchgang: Karte 10006 -> Karte 10007 bei 12:12 (Position davor ",old_x,":",old_y,", Event ",event_id,")"));
                        } else if (current_map==10007) { target=DEN_RETURN_TARGET; log_line("[DEN-RUECKKEHR] Karte 10007 -> Karte 10006 bei 34:16"); }
                        else if (INTERIOR_MAPS.count(current_map)) {
                            if (current_map==10006) {
                                std::string region=(old_x<=3)?"Dorfportal 180/181":(old_y>=34)?"Dorfportal 182/183":(old_x>=34)?"Gehege Karte 50000":"unbekannter Ausgang";
                                log_line(str("[INNENAUSGANG] Karte 10006: ",region,", Position ",old_x,":",old_y,", Event ",event_id));
                            }
                            target=return_target; log_line(str("[RUECKKEHR] Zum zuletzt benutzten Dorfportal: ",return_target.x,":",return_target.y));
                        } else if (current_map==1 && HALBOL_WORLD_RETURN_EVENTS.count(event_id)) { target=return_target; log_line(str("[DORFRUECKKEHR ERKANNT] Welt-Event ",event_id,": Karte 100 bei ",return_target.x,":",return_target.y)); }
                        if (!target && current_map==100) { target=return_target; log_line("[WARP] Unbekanntes Dorf-Event; Charakter vor die Tuer zurueckgesetzt."); }
                        else if (!target && INTERIOR_MAPS.count(current_map)) { target=return_target; log_line("[WARP] Neues Innenraum-Event; vorlaeufiges Ziel Karte 100."); }
                        auto now=std::chrono::steady_clock::now();
                        if (!target) log_line("[WARP] Noch kein Ziel fuer diese Karte/Event-ID bekannt.");
                        else if (last_warp_at.time_since_epoch().count() != 0 &&
                            now - last_warp_at < 750ms &&
                            event_id == last_warp_event_id)
                        {
                            log_line(
                                "[WARP] Doppelte Anfrage desselben Events "
                                "innerhalb 750 ms ignoriert.");
                        }
                        else {
                            Bytes reply=position_reply(target->map,target->x,target->y,target->direction); send_all(session,reply); current_map=target->map; pet_spawned_map.reset(); pet_x.reset(); pet_y.reset();
                            { std::lock_guard lock(session->state_mutex); session->move_state.map=target->map; session->move_state.x=target->x; session->move_state.y=target->y; session->move_state.direction=target->direction; }
                            awaiting_map_sync=true; last_warp_at=now; log_line(str("[V",PROGRAM_VERSION," WARP] Karte ",target->map,", Position ",target->x,":",target->y)); log_line(str("[GESENDET] MAP/POSITION 0x0410: ",hexline(reply)));

                            last_warp_at = now;
                            last_warp_event_id = event_id;
                        }
                    } else if (size1==25 && payload.size()>=13 && payload[0]==0x8F) {
                        int confirmed=read_u16(payload,5), x=read_i16(payload,7), y=read_i16(payload,9); current_map=confirmed; log_line(str("[KARTENBESTAETIGUNG] Karte ",confirmed,", Position ",x,":",y));
                    }
                }
                else if (command == 0x0461) {
                    // Observed client Pet-Reorder packet:
                    //   WORD  +0 = number of pets
                    //   repeated count times:
                    //     DWORD = persistent pet object ID
                    //     DWORD = new compact slot/index
                    //   WORD trailing = 0 (observed)
                    // Example for 3 pets:
                    //   03 00 | 06 00 00 20 00 00 00 00 |
                    //           07 00 00 20 01 00 00 00 |
                    //           05 00 00 20 02 00 00 00 | 00 00
                    Bytes payload = slice(packet, 6);

                    bool reordered = false;
                    bool persist_ok = true;
                    std::string reject_reason;
                    std::vector<CapturedPetState> before;
                    std::vector<CapturedPetState> after;

                    if (payload.size() < 4) {
                        reject_reason = "Payload zu kurz";
                    }
                    else {
                        const std::size_t count = read_u16(payload, 0);
                        const std::size_t expected_size = 2 + count * 8 + 2;

                        if (payload.size() != expected_size) {
                            reject_reason = str(
                                "unerwartete Payloadgroesse ", payload.size(),
                                " (erwartet ", expected_size, ")");
                        }
                        else {
                            std::vector<std::pair<std::uint32_t, std::uint32_t>> requested;
                            requested.reserve(count);
                            std::set<std::uint32_t> seen_ids;
                            std::set<std::uint32_t> seen_slots;

                            for (std::size_t i = 0; i < count; ++i) {
                                const std::size_t off = 2 + i * 8;
                                const std::uint32_t pet_id = read_u32(payload, off);
                                const std::uint32_t slot = read_u32(payload, off + 4);

                                if (!seen_ids.insert(pet_id).second) {
                                    reject_reason = str("doppelte Pet-ID 0x", [&] {
                                        std::ostringstream os;
                                        os << std::hex << std::uppercase << pet_id;
                                        return os.str();
                                    }());
                                    break;
                                }
                                if (!seen_slots.insert(slot).second) {
                                    reject_reason = str("doppelter Slot ", slot);
                                    break;
                                }
                                if (slot >= count) {
                                    reject_reason = str("Slot ", slot, " ausserhalb 0..", count ? count - 1 : 0);
                                    break;
                                }

                                requested.emplace_back(pet_id, slot);
                            }

                            if (reject_reason.empty()) {
                                std::lock_guard lock(session->state_mutex);
                                before = session->captured_pets;

                                // The reorder packet is a complete snapshot of the
                                // client's pet strip. Requiring every current pet once
                                // prevents a malformed/partial packet from silently
                                // deleting or duplicating server-side slots.
                                if (count != session->captured_pets.size()) {
                                    reject_reason = str(
                                        "Client meldet ", count,
                                        " Pets, Server hat ", session->captured_pets.size());
                                }
                                else {
                                    for (const auto& [pet_id, slot32] : requested) {
                                        auto it = std::find_if(
                                            session->captured_pets.begin(),
                                            session->captured_pets.end(),
                                            [&](const CapturedPetState& pet) {
                                                return pet.pet_id == pet_id;
                                            });

                                        if (it == session->captured_pets.end()) {
                                            reject_reason = str("unbekannte Pet-ID 0x", [&] {
                                                std::ostringstream os;
                                                os << std::hex << std::uppercase << pet_id;
                                                return os.str();
                                            }());
                                            break;
                                        }

                                        it->slot = static_cast<std::uint16_t>(slot32);
                                    }

                                    if (reject_reason.empty()) {
                                        // Keep vector order identical to the client strip.
                                        // BattleInit iterates this vector, so the same order
                                        // automatically becomes player -> pet slot 0 -> 1 -> 2.
                                        std::stable_sort(
                                            session->captured_pets.begin(),
                                            session->captured_pets.end(),
                                            [](const CapturedPetState& a,
                                               const CapturedPetState& b) {
                                                return a.slot < b.slot;
                                            });

                                        session->next_captured_pet_slot =
                                            static_cast<std::uint16_t>(std::min<std::size_t>(
                                                65535, session->captured_pets.size()));

                                        if (session->pending_captured_pet) {
                                            auto it = std::find_if(
                                                session->captured_pets.begin(),
                                                session->captured_pets.end(),
                                                [&](const CapturedPetState& pet) {
                                                    return pet.pet_id == session->pending_captured_pet->pet_id;
                                                });
                                            if (it != session->captured_pets.end())
                                                session->pending_captured_pet = *it;
                                        }

                                        after = session->captured_pets;
                                        reordered = true;
                                    }
                                }
                            }
                        }
                    }

                    if (reordered) {
                        try {
                            save_captured_pets_state(after);
                        }
                        catch (const std::exception& e) {
                            persist_ok = false;
                            std::lock_guard lock(session->state_mutex);
                            session->captured_pets = before;
                            session->next_captured_pet_slot =
                                static_cast<std::uint16_t>(std::min<std::size_t>(
                                    65535, session->captured_pets.size()));
                            log_line(str(
                                "[PET-REIHENFOLGE 0x0461] Speichern fehlgeschlagen; "
                                "Reihenfolge rueckgaengig gemacht: ", e.what()));
                        }
                    }

                    if (reordered && persist_ok) {
                        std::ostringstream os;
                        os << "[PET-REIHENFOLGE 0x0461] Uebernommen: ";
                        for (std::size_t i = 0; i < after.size(); ++i) {
                            if (i) os << " -> ";
                            os << "Slot " << after[i].slot
                               << "=0x" << std::hex << std::uppercase
                               << after[i].pet_id << std::dec
                               << "(" << after[i].name << ")";
                        }
                        log_line(os.str());
                        log_line(
                            "[PET-REIHENFOLGE 0x0461] Kein ACK gesendet; "
                            "der Client hat die UI bereits lokal umsortiert. "
                            "Naechster BattleInit verwendet diese Reihenfolge.");
                    }
                    else if (!reject_reason.empty()) {
                        log_line(str(
                            "[WARNUNG] PET-REIHENFOLGE 0x0461 verworfen: ",
                            reject_reason,
                            "; Payload=", hexline(payload)));
                    }
                }
                else if (command == 0x0460) {
                    // Client SendPetDrop. Observed payload is 6 bytes:
                    //   DWORD +0 = pet object ID
                    //   WORD  +4 = currently 0 (not needed for the release itself)
                    Bytes payload = slice(packet, 6);

                    std::uint32_t pet_id =
                        payload.size() >= 4 ? read_u32(payload, 0) : 0;

                    bool removed = false;
                    bool persist_ok = true;
                    std::string pet_name;
                    std::vector<CapturedPetState> before;
                    std::vector<CapturedPetState> after;

                    if (pet_id != 0) {
                        {
                            std::lock_guard lock(session->state_mutex);

                            // Releasing a pet while it participates in BattleInit
                            // would invalidate the current battle roster. Reject it
                            // instead of corrupting the active round.
                            if (!session->battle_active) {
                                before = session->captured_pets;

                                auto it = std::find_if(
                                    session->captured_pets.begin(),
                                    session->captured_pets.end(),
                                    [&](const CapturedPetState& pet) {
                                        return pet.pet_id == pet_id;
                                    });

                                if (it != session->captured_pets.end()) {
                                    pet_name = it->name;
                                    session->captured_pets.erase(it);

                                    if (session->pending_captured_pet &&
                                        session->pending_captured_pet->pet_id == pet_id)
                                    {
                                        session->pending_captured_pet.reset();
                                    }

                                    // Closing a gap is mandatory: the client uses
                                    // slot as a compact array index in several UI views.
                                    compact_captured_pet_slots(session->captured_pets);
                                    session->next_captured_pet_slot =
                                        static_cast<std::uint16_t>(std::min<std::size_t>(
                                            65535, session->captured_pets.size()));

                                    after = session->captured_pets;
                                    removed = true;
                                }
                            }
                        }

                        if (removed) {
                            try {
                                save_captured_pets_state(after);
                            }
                            catch (const std::exception& e) {
                                persist_ok = false;

                                // Keep memory and persistent storage consistent.
                                std::lock_guard lock(session->state_mutex);
                                session->captured_pets = before;

                                log_line(str(
                                    "[PET FREILASSEN] Speichern fehlgeschlagen; "
                                    "Freilassen rueckgaengig gemacht: ",
                                    e.what()));
                            }
                        }
                    }

                    const bool success = removed && persist_ok;
                    Bytes reply = pet_drop_result_reply(pet_id, success);
                    send_all(session, reply);

                    // OnPetDropRet updates the main pet collection/count, but the
                    // Chinese client's horizontal pet portrait bar can keep stale
                    // slot images. Re-send the surviving compact 0x0462 records so
                    // every remaining pet is explicitly rebound to slot 0..N-1.
                    // This deliberately happens only after the successful drop ACK.
                    if (success) {
                        std::this_thread::sleep_for(100ms);
                        if (send_captured_pet_list(session)) {
                            log_line(
                                "[PET FREILASSEN] Verbleibende Pet-Liste nach 0x0468 "
                                "neu synchronisiert (kompakte Slots 0..N-1).");
                        }
                        else {
                            log_line(
                                "[WARNUNG] Pet-Liste nach dem Freilassen konnte "
                                "nicht vollstaendig neu synchronisiert werden.");
                        }
                    }

                    log_line(str(
                        "[PET FREILASSEN] pet_id=0x",
                        [&] {
                            std::ostringstream os;
                            os << std::hex << std::uppercase << pet_id;
                            return os.str();
                        }(),
                        pet_name.empty() ? "" : str(", Name=", pet_name),
                        success ? " -> OK" : " -> ABGELEHNT/NICHT GEFUNDEN",
                        "; 0x0468: ",
                        hexline(reply)));
                }
                else if (command == 0x0415) {
                    MoveState position;

                    {
                        std::lock_guard lock(session->state_mutex);
                        position = session->move_state;
                    }

                    save_player_position(position);

                    log_line(str(
                        "[LOGOUT 0x0415] Position gespeichert: Karte ",
                        position.map,
                        ", Position ",
                        position.x,
                        ":",
                        position.y,
                        ", Richtung ",
                        position.direction,
                        "; Payload: ",
                        hexline(slice(packet, 6))));
                }
                else if (command == 0x0B01) {
                    {
                        std::lock_guard lock(session->state_mutex);
                        session->battle_active = true;
                    }

                    Bytes payload = slice(packet, 6);
                    if (payload.size() >= 14) {
                        std::uint32_t actor_id = read_u32(payload, 0);
                        int battle_map = read_u16(payload, 4);
                        int bx = read_i16(payload, 6);
                        int by = read_i16(payload, 8);
                        unsigned direction = payload[10];
                        unsigned flags = payload[11];
                        unsigned graphic = read_u16(payload, 12);

                        set_battle_current_actor(session, actor_id);

                        std::ostringstream os;
                        os << "[KAMPF-POSITION 0x0B01] actor_id=" << actor_id
                           << ", Karte=" << battle_map
                           << ", Position=" << bx << ':' << by
                           << ", Richtung=" << direction
                           << ", Flags=0x" << std::hex << std::uppercase
                           << std::setw(2) << std::setfill('0') << flags
                           << std::dec << ", CGNO=" << graphic;
                        log_line(os.str());
                    }
                    else {
                        log_line("[KAMPF-POSITION 0x0B01] Zu kurze Nutzlast.");
                    }

                    // BattleInit already opens the very first local order phase.
                    // Do NOT send 0x0BD1 here: doing so queues a second complete
                    // selection phase, which is why the first round had to be
                    // selected twice once the pet IDs were finally correct.
                    {
                        std::lock_guard lock(session->state_mutex);
                        session->battle_order_phase_started = true;
                        session->battle_turn_index = 0;
                    }
                    log_line(
                        "[KAMPF] 0x0B01/BattleInit: erste Auswahlphase laeuft "
                        "bereits lokal; KEIN initiales 0x0BD1.");
                } else if (command==0x0B20) {
                    // Chinese 2010 client sends one 0x0B20 for EACH controllable
                    // actor (player, pet 0, pet 1, ...), and only AFTER all local
                    // selections are complete does it send a single 0x0B90.
                    // Therefore 0x0B20 itself is the actual per-actor order and
                    // must be stored immediately.  Do not keep only one pending
                    // packet and do not echo it here.
                    Bytes payload=slice(packet,6);
                    std::uint32_t actor_object_id=payload.size()>=4?read_u32(payload,0):0;
                    std::uint32_t battle_actor_id=payload.size()>=8?read_u32(payload,4):0;
                    std::uint32_t action=payload.size()>=12?read_u32(payload,8):0;
                    std::uint32_t target_object_id=payload.size()>=20?read_u32(payload,16):0;
                    std::uint32_t battle_target_id=payload.size()>=24?read_u32(payload,20):0;
                    const std::uint32_t order_field_0c=payload.size()>=16?read_u32(payload,12):0;
                    const std::uint8_t order_option=payload.size()>0x0F?payload[0x0F]:0;

                    auto action_it=BATTLE_ACTION_NAMES.find(static_cast<int>(action));
                    std::string action_name=action_it!=BATTLE_ACTION_NAMES.end()?action_it->second:"UNBEKANNT";

                    store_battle_action(
                        session,
                        actor_object_id,
                        action,
                        target_object_id,
                        packet);

                    std::size_t selected_count=0;
                    std::size_t expected_count=0;
                    {
                        std::lock_guard lock(session->state_mutex);
                        selected_count=session->planned_battle_actions.size();
                        expected_count=session->battle_turn_order.size();
                    }

                    std::ostringstream os;
                    os<<"[KAMPFAUSWAHL 0x0B20] actor=0x"<<std::hex<<std::uppercase
                      <<std::setw(8)<<std::setfill('0')<<actor_object_id
                      <<", battle_actor=0x"<<std::setw(8)<<battle_actor_id
                      <<", action="<<std::dec<<action<<" ("<<action_name<<")"
                      <<", target=0x"<<std::hex<<std::uppercase
                      <<std::setw(8)<<target_object_id
                      <<", battle_target=0x"<<std::setw(8)<<battle_target_id
                      <<", field0C=0x"<<std::setw(8)<<order_field_0c
                      <<", option0F=0x"<<std::setw(2)<<static_cast<unsigned>(order_option)
                      <<std::dec<<"; gespeichert "<<selected_count<<"/"<<expected_count
                      <<" Orders; keine Antwort bis 0x0B90.";
                    log_line(os.str());

                    if ((actor_object_id & 0xF0000000u) == 0x20000000u &&
                        action != 0 && action != 3 && action != 8 &&
                        action != 88 && action != 0x99 && action != 150) {
                        log_line(str(
                            "[PET-SPEZIAL-DIAG] action=", action,
                            ", option0F=0x", [&]{ std::ostringstream h; h<<std::hex<<std::uppercase<<(unsigned)order_option; return h.str(); }(),
                            ", field0C=0x", [&]{ std::ostringstream h; h<<std::hex<<std::uppercase<<order_field_0c; return h.str(); }(),
                            ", RAW=", hexline(payload)));
                    }
                }
                else if (command == 0x0B90) {
                    // 0x0B90 is sent ONCE after the client has collected the
                    // player and all pet orders.  Treat it as the commit/end of
                    // the complete local order-selection phase, not as a per-actor
                    // acknowledgement.
                    Bytes payload = slice(packet, 6);

                    std::uint32_t enter_actor_id =
                        payload.size() >= 4 ? read_u32(payload, 0) : 0;
                    std::uint32_t enter_battle_id =
                        payload.size() >= 8 ? read_u32(payload, 4) : 0;

                    log_line(str(
                        "[KAMPFBEFEHL 0x0B90] PHASEN-COMMIT actor_id=0x",
                        [&] {
                            std::ostringstream os;
                            os << std::hex << std::uppercase << enter_actor_id;
                            return os.str();
                        }(),
                        ", battle_id=0x",
                        [&] {
                            std::ostringstream os;
                            os << std::hex << std::uppercase
                               << std::setw(8) << std::setfill('0')
                               << enter_battle_id;
                            return os.str();
                        }()));

                    if (!all_battle_actions_selected(session)) {
                        std::size_t selected_count = 0;
                        std::size_t expected_count = 0;

                        {
                            std::lock_guard lock(session->state_mutex);
                            selected_count = session->planned_battle_actions.size();
                            expected_count = session->battle_turn_order.size();
                        }

                        const auto missing =
                            fill_missing_battle_actions_with_wait(session);

                        std::ostringstream missing_text;
                        for (std::size_t i = 0; i < missing.size(); ++i) {
                            if (i) missing_text << ", ";
                            missing_text << "0x" << std::hex << std::uppercase
                                         << missing[i];
                        }

                        log_line(str(
                            "[KAMPFRUNDE] 0x0B90 erhalten mit ",
                            selected_count, "/", expected_count,
                            " expliziten Orders. Fehlende Actors: ",
                            missing_text.str().empty() ? "keine" : missing_text.str(),
                            ". Fehlende Orders werden als WARTEN ausgefuehrt."));
                    }
                    else {
                        log_line(
                            "[KAMPFRUNDE] Alle Player/Pet-Orders liegen vor; 0x0B90 committed die Runde.");
                    }

                    log_line(
                        "[KAMPFRUNDE] Fuehre committed Runde jetzt aus.");

                    bool all_dead = execute_planned_battle_round(session);

                    // execute_planned_battle_round now resolves player, pets
                    // AND enemies in one initiative-sorted queue.
                    bool battle_still_active = false;
                    {
                        std::lock_guard lock(session->state_mutex);
                        battle_still_active = session->battle_active;
                    }

                    // Player defeat finalises the battle inside the initiative
                    // executor; do not accidentally start another phase/victory.
                    if (battle_still_active) {
                        finish_battle_turn(
                            session,
                            PLAYER_BATTLE_ACTOR_ID,
                            all_dead);
                    }
                }
                else if (command==0x0900) {
                    activate_cheat_session(session,"Weltdaten 0x0900");
                    Bytes reply=initial_data_reply();
                    send_all(session,reply);
                    log_line(str("[GESENDET] INITIAL DATA 0x0900: ",hexline(reply)));

                    // V135: V134 proved that the crash is caused by persisted pet
                    // restoration. Slots are now repaired to a compact 0..N-1 range
                    // before any 0x0462 record is emitted. Send only after 0x0900.
                    if (!captured_pet_list_sent) {
                        captured_pet_list_sent = true;
                        std::this_thread::sleep_for(100ms);
                        if (!send_captured_pet_list(session))
                            log_line("[WARNUNG] Reparierte Pet-Liste konnte nicht vollstaendig gesendet werden.");
                        else
                            log_line("[V135] Reparierte Pet-Liste nach 0x0900 gesendet.");
                    }

                    if (!inventory_sent)
                    {
                        inventory_sent = true;

                        std::this_thread::sleep_for(50ms);

                        if (send_persisted_inventory(session))
                        {
                            log_line(str(
                                "[INVENTAR] ",
                                session->inventory_items.size(),
                                " gespeicherte Items an den Client gesendet."));
                        }
                        else
                        {
                            log_line(
                                "[WARNUNG] Gespeichertes Inventar konnte nicht gesendet werden.");
                        }
                    }

                } else {
                    std::ostringstream os; os<<"[UNBEKANNTER CLIENTBEFEHL] CMD=0x"<<std::hex<<std::uppercase<<std::setw(4)<<std::setfill('0')<<command<<std::dec<<", Groesse="<<packet.size()<<", Nutzlast="<<hexline(slice(packet,6)); log_line(os.str());
                }
            }
        }
    } catch (const std::exception& e) { log_line(str("[FEHLER Port ",port,"] ",e.what())); }

    // --------------------------------------------------------
// Position immer beim Ende der Spielsitzung speichern.
//
// Das greift auch bei:
// - Alt+F4
// - Client-Absturz
// - Verbindungsabbruch
// - Schliessen waehrend eines Kampfes
//
// Nur Sessions speichern, in denen der Charakter
// tatsaechlich die Spielwelt betreten hat.
// --------------------------------------------------------

    if (character_entered) {
        try {
            MoveState position;

            {
                std::lock_guard lock(session->state_mutex);
                position = session->move_state;
            }

            save_player_position(position);

            log_line(str(
                "[SESSION-ENDE] Letzte Spielerposition gespeichert: Karte ",
                position.map,
                ", Position ",
                position.x,
                ":",
                position.y,
                ", Richtung ",
                position.direction));
        }
        catch (const std::exception& e) {
            log_line(str(
                "[WARNUNG] Position beim Session-Ende konnte nicht gespeichert werden: ",
                e.what()));
        }
    }

    session->closing = true;

    {
        std::lock_guard lock(active_session_mutex);

        auto a = active_cheat_session.lock();

        if (a == session)
            active_cheat_session.reset();
    }

    close_socket(socket);

    log_line(str(
        "[GETRENNT] Port ",
        port,
        "; Rohdaten: ",
        fs::exists(out) ? out.string() : "keine"));

    session->closing=true;
    {
        std::lock_guard lock(active_session_mutex); auto a=active_cheat_session.lock(); if (a==session) active_cheat_session.reset();
    }
    close_socket(socket);
    log_line(str("[GETRENNT] Port ",port,"; Rohdaten: ",fs::exists(out)?out.string():"keine"));
}

static std::string peer_to_string(const sockaddr_storage& ss) {
    char host[NI_MAXHOST]{},serv[NI_MAXSERV]{};
    if (getnameinfo(reinterpret_cast<const sockaddr*>(&ss),
                    ss.ss_family==AF_INET?sizeof(sockaddr_in):sizeof(sockaddr_in6),
                    host,sizeof(host),serv,sizeof(serv),NI_NUMERICHOST|NI_NUMERICSERV)==0)
        return str("('",host,"', ",serv,")");
    return "(?)";
}

static void listener_thread(int port,const fs::path& log_dir) {
    SocketHandle s=::socket(AF_INET,SOCK_STREAM,IPPROTO_TCP); if (s==INVALID_SOCKET_HANDLE) { log_line(str("[FEHLER] socket() Port ",port)); return; }
    int yes=1;
#ifdef _WIN32
    setsockopt(s,SOL_SOCKET,SO_REUSEADDR,reinterpret_cast<const char*>(&yes),sizeof(yes));
#else
    setsockopt(s,SOL_SOCKET,SO_REUSEADDR,&yes,sizeof(yes));
#endif
    sockaddr_in addr{}; addr.sin_family=AF_INET; addr.sin_addr.s_addr=htonl(INADDR_ANY); addr.sin_port=htons(static_cast<std::uint16_t>(port));
    if (bind(s,reinterpret_cast<sockaddr*>(&addr),sizeof(addr))!=0 || listen(s,SOMAXCONN)!=0) { log_line(str("[FEHLER] Konnte TCP-Port ",port," nicht binden.")); close_socket(s); return; }
    log_line(str("Warte auf TCP-Port ",port," ..."));
    while (running.load()) {
        sockaddr_storage peer{};
#ifdef _WIN32
        int len=sizeof(peer); SocketHandle c=accept(s,reinterpret_cast<sockaddr*>(&peer),&len);
#else
        socklen_t len=sizeof(peer); SocketHandle c=accept(s,reinterpret_cast<sockaddr*>(&peer),&len);
#endif
        if (c==INVALID_SOCKET_HANDLE) { if (!running.load()) break; continue; }
        std::thread(client_thread,c,port,log_dir,peer_to_string(peer)).detach();
    }
    close_socket(s);
}

#ifdef _WIN32
static bool relaunch_elevated_for_hotkeys(int argc,char** argv) {
    // Relaunch the server elevated so it can poll the elevated CN client.
    if (IsUserAdmin()) { log_line("[HOTKEYS] Server laeuft erhoeht; globale Tastaturabfrage ist freigegeben."); return false; }
    fs::path exe=executable_path();
    std::wstring params;
    for (int i=1;i<argc;++i) {
        if (!params.empty()) params.push_back(L' ');
        std::wstring w=fs::path(argv[i]).wstring(); params += L'"'+w+L'"';
    }
    auto result=reinterpret_cast<std::intptr_t>(ShellExecuteW(nullptr,L"runas",exe.c_str(),params.c_str(),fs::current_path().c_str(),SW_SHOWNORMAL));
    if (result<=32) { log_line(str("[WARNUNG] UAC-Neustart fehlgeschlagen (ShellExecute=",result,").")); log_line("[WARNUNG] Bitte PowerShell als Administrator starten; sonst funktionieren die globalen Hotkeys nicht."); return false; }
    log_line("[HOTKEYS] Server wird mit Administratorrechten neu gestartet."); return true;
}
#else
static bool relaunch_elevated_for_hotkeys(int,char**) { return false; }
#endif

struct Options {
    std::optional<fs::path> patch,restore,mapdata,item_bin;
    int time_speed=WORLD_TIME_SPEED,battle_x=BATTLE_ANCHOR_X,battle_y=BATTLE_ANCHOR_Y,map_off_x=BATTLE_MAP_OFFSET_X,map_off_y=BATTLE_MAP_OFFSET_Y;
};
static Options parse_args(int argc,char** argv) {
    Options o;
    for (int i=1;i<argc;++i) {
        std::string a=argv[i]; auto need=[&](){if (i+1>=argc) throw std::runtime_error("Fehlender Wert fuer "+a); return std::string(argv[++i]);};
        if (a=="--patch") o.patch=need(); else if (a=="--restore") o.restore=need(); else if (a=="--mapdata") o.mapdata=need(); else if (a=="--item-bin") o.item_bin=need();
        else if (a=="--time-speed") o.time_speed=std::stoi(need()); else if (a=="--battle-x") o.battle_x=std::stoi(need()); else if (a=="--battle-y") o.battle_y=std::stoi(need());
        else if (a=="--battle-map-offset-x") o.map_off_x=std::stoi(need()); else if (a=="--battle-map-offset-y") o.map_off_y=std::stoi(need());
        else if (a=="--help"||a=="-h") { std::cout<<"Usage: sa2_probe_server [--patch VERSION.XML|--restore VERSION.XML] [--mapdata DIR] [--item-bin FILE|DATA_DIR] [--time-speed N] [--battle-x N] [--battle-y N] [--battle-map-offset-x N] [--battle-map-offset-y N]\n"; std::exit(0); }
        else throw std::runtime_error("Unbekannte Option: "+a);
    }
    if (o.time_speed<1||o.time_speed>65535) throw std::runtime_error("--time-speed muss im Bereich 1..65535 liegen");
    if (o.battle_x<-32768||o.battle_x>32767||o.battle_y<-32768||o.battle_y>32767) throw std::runtime_error("--battle-x und --battle-y muessen im Bereich -32768..32767 liegen");
    if (o.map_off_x<-20||o.map_off_x>100||o.map_off_y<-20||o.map_off_y>100) throw std::runtime_error("Battle-Map-Offsets muessen im Bereich -20..100 liegen");
    return o;
}

int main(int argc,char** argv) {
    try {
        Options args=parse_args(argc,argv); ITEM_CATALOG_OVERRIDE_PATH=args.item_bin; WORLD_TIME_SPEED=args.time_speed; BATTLE_ANCHOR_X=args.battle_x; BATTLE_ANCHOR_Y=args.battle_y; BATTLE_MAP_OFFSET_X=args.map_off_x; BATTLE_MAP_OFFSET_Y=args.map_off_y;
        if (args.patch) { patch_xml(*args.patch); return 0; }
        if (args.restore) { restore_xml(*args.restore); return 0; }
        if (relaunch_elevated_for_hotkeys(argc,argv)) return 0;
#ifdef _WIN32
        WSADATA wsa{}; if (WSAStartup(MAKEWORD(2,2),&wsa)!=0) throw std::runtime_error("WSAStartup fehlgeschlagen");
#endif
        configure_map_catalog(args.mapdata); load_encounter_catalog(); load_item_catalog(); created_character_record = load_character_state();
        log_line(str("Stone Age 2 Probe-Server VERSION ",PROGRAM_VERSION));
        log_line("[BUILD] SERIAL_BATTLE_ACTIONS_V1 + CAPTURED_PET_TEAM_V1 + WORLD_STATUS_SYNC_V1 active");
        log_line("Erkennungsmerkmal: gedrosselter Pet-Spawn plus Server-Folgebewegung.\n");
        log_line(str("[KAMPFKAMERA] BattleInit-Anker ",BATTLE_ANCHOR_X,":",BATTLE_ANCHOR_Y));
        log_line(str("[KAMPFKARTE] Weltversatz ",BATTLE_MAP_OFFSET_X,":",BATTLE_MAP_OFFSET_Y));
        log_line(str("[WELTZEIT] Multiplikator ",WORLD_TIME_SPEED," (",WORLD_TIME_SPEED==0?"angehalten":"aktiv",")"));
        fs::path log_dir="sa2_probe_logs"; fs::create_directories(log_dir);
        std::vector<std::thread> listeners; for (int port:PORTS) listeners.emplace_back(listener_thread,port,log_dir);
        std::thread hotkeys(arrow_key_cheat);
        log_line("\nJetzt StoneAge2.exe direkt starten und einen Server auswählen."); log_line("Beenden mit Strg+C.");
        for (auto& t:listeners) t.join();
        running=false; if (hotkeys.joinable()) hotkeys.join();
#ifdef _WIN32
        WSACleanup();
#endif
    } catch (const std::exception& e) { std::cerr<<"Fehler: "<<e.what()<<"\n"; return 1; }
    return 0;
}
