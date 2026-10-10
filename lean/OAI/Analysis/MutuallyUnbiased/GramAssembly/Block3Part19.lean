import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Part18

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

def node608 : Integer.Sparse (Fin 2886) := [(1118, 536111232), (1119, -253599504), (1123, -253599504), (1125, -536111232), (1126, 253599504), (1129, 253599504), (1365, -1876389312), (1367, 1267997520), (1372, 507199008), (1438, 1340278080), (1439, -1014398016), (1468, -253599504), (1470, 536111232), (1472, -253599504), (1475, -507199008), (1498, 253599504), (1581, -2144444928), (1582, 760798512), (1585, 1267997520), (1619, 2144444928), (1620, -760798512), (1623, -1014398016), (1644, -253599504), (1647, -253599504), (1655, 253599504), (2107, 218618352), (2110, 2112371280), (2111, 430874064), (2113, 291491136), (2114, 318383568), (2116, 364363920), (2128, -162266688), (2133, -362361984), (2140, 12609536), (2144, -612232512), (2156, 387249600), (2161, -87603840), (2187, 287367680), (2193, -62716224), (2202, -437236704), (2205, -2112371280), (2206, -212255712), (2208, -218618352), (2211, 218618352), (2222, -449965824), (2230, -337474368), (2234, -899931648), (2253, -337474368), (2259, -899931648), (2269, -218618352), (2270, 212255712), (2273, 437236704), (2274, -787440192), (2281, -318383568), (2311, -212255712), (2317, -437236704), (2319, 449965824), (2321, 956177376), (2326, 956177376), (2329, -437236704), (2330, 524960128), (2336, -24887616), (2341, -68689536), (2346, 74994304), (2348, 112491456), (2514, 249870528), (2520, 68689536), (2633, 249870528), (2635, 137379072), (2656, 306116256), (2675, 74994304), (2677, 112491456), (2711, -24887616), (2713, -137379072), (2734, 31358112), (2740, 112491456), (2747, 149988608)]

theorem node608_check : node608 =
    Integer.Sparse.merge node604 node607 := by decide +kernel

theorem node608_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node608 x = ((((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_6 x + (((-1431032 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_7 x + ((5283323 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_8 x)) + ((((4687144 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_9 x + ((-5584492 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_10 x) + (((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_11 x + ((-1518183 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_12 x))) := by
  rw [node608_check, Integer.Sparse.eval_merge]
  rw [node604_eval, node607_eval]

def node609 : Integer.Sparse (Fin 2886) := [(846, -980369280), (848, -185839488), (855, -162609552), (954, 980369280), (956, 185839488), (964, 116149680), (1035, 46459872), (1049, 46459872), (1085, -46459872), (1118, 536111232), (1119, -253599504), (1123, -253599504), (1125, -536111232), (1126, 253599504), (1129, 253599504), (1365, -1876389312), (1367, 1267997520), (1372, 507199008), (1438, 1340278080), (1439, -1014398016), (1468, -253599504), (1470, 536111232), (1472, -253599504), (1475, -507199008), (1498, 253599504), (1581, -2144444928), (1582, 760798512), (1585, 1267997520), (1619, 2144444928), (1620, -760798512), (1623, -1014398016), (1644, -253599504), (1647, -253599504), (1655, 253599504), (2107, 872677296), (2110, 2112371280), (2111, 1084933008), (2112, -432688896), (2113, 1054559904), (2114, 318383568), (2116, 745898304), (2117, 432688896), (2127, 65785248), (2128, -244024176), (2133, -362361984), (2139, -65785248), (2140, -96400448), (2144, -693990000), (2155, -230248368), (2156, -348567792), (2161, -414633792), (2186, -263140992), (2187, -148672256), (2193, -798533616), (2202, -1254810384), (2205, -2112371280), (2206, -702799920), (2207, 432688896), (2208, -709162560), (2210, 2596133376), (2211, -108411120), (2221, 164463120), (2222, -122935872), (2229, 65785248), (2230, -92201904), (2234, -572901696), (2252, 263140992), (2253, -92201904), (2259, -572901696), (2267, -109009824), (2269, -586526508), (2270, 212255712), (2271, 1442296320), (2273, -53307504), (2274, -542167728), (2275, 1730755584), (2278, 109009824), (2280, 163514736), (2281, -318383568), (2282, -2307674112), (2283, -432688896), (2310, 218019648), (2311, -212255712), (2312, -1730755584), (2314, -1730755584), (2317, -396358020), (2319, 449965824), (2321, 915298632), (2326, 915298632), (2329, -328226880), (2330, 470455136), (2336, 220384848), (2341, 94825440), (2346, 20489312), (2348, 30733968), (2514, 168113040), (2520, 68689536), (2590, 327029952), (2626, 163514976), (2633, 168113040), (2635, 137379072), (2656, 183480024), (2675, 20489312), (2677, 30733968), (2711, 220384848), (2713, 189650880), (2734, 235751832), (2740, 30733968), (2747, 40978624)]

theorem node609_check : node609 =
    Integer.Sparse.merge node602 node608 := by decide +kernel

theorem node609_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node609 x = (((((-9014352 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_0 x + (((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_1 x + ((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_2 x)) + (((-685263 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_3 x + (((3406557 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_4 x + ((-3406562 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_5 x))) + ((((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_6 x + (((-1431032 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_7 x + ((5283323 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_8 x)) + ((((4687144 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_9 x + ((-5584492 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_10 x) + (((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_11 x + ((-1518183 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_12 x)))) := by
  rw [node609_check, Integer.Sparse.eval_merge]
  rw [node602_eval, node608_eval]

def node610 : Integer.Sparse (Fin 2886) := [(848, -231175584), (855, -346763376), (956, 231175584), (1035, 346763376), (1049, -231175584), (1085, 231175584), (2111, 3311005824), (2114, 2897130096), (2206, -3311005824), (2209, -2069378640), (2270, -827751456), (2281, -827751456), (2311, 827751456)]

theorem node610_check : node610 =
    Integer.Sparse.merge (Integer.Sparse.scale (802693) entry_23_14) (Integer.Sparse.scale (8622411) entry_23_15) := by decide +kernel

theorem node610_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node610 x = (((802693 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_14 x + ((8622411 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_15 x) := by
  rw [node610_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node611 : Integer.Sparse (Fin 2886) := [(848, -231175584), (855, -346763376), (956, 231175584), (1035, 346763376), (1049, -231175584), (1085, 231175584), (1792, 44447232), (1796, 38891328), (2023, -44447232), (2027, -27779520), (2048, -11111808), (2075, -11111808), (2086, 11111808), (2111, 3311005824), (2114, 2897130096), (2206, -3311005824), (2209, -2069378640), (2270, -827751456), (2281, -827751456), (2311, 827751456)]

theorem node611_check : node611 =
    Integer.Sparse.merge (Integer.Sparse.scale (115748) entry_23_13) node610 := by decide +kernel

theorem node611_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node611 x = (((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_13 x + (((802693 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_14 x + ((8622411 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_15 x)) := by
  rw [node611_check, Integer.Sparse.eval_merge]
  rw [node610_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node612 : Integer.Sparse (Fin 2886) := [(2127, 1709771328), (2129, 94375344), (2139, 1139847552), (2143, 251667584), (2155, -1709771328), (2157, 471876720), (2160, 755002752), (2186, -1139847552), (2191, 1006670336), (2195, 377501376), (2223, -377501376), (2229, -1139847552), (2233, -755002752), (2252, 1139847552), (2257, -755002752), (2276, -377501376), (2294, 125833792), (2305, 125833792), (2315, 188750688), (2340, -94375344), (2343, -377501376), (2350, 125833792), (2519, 94375344), (2595, -188750688), (2628, -377501376), (2658, 251667584), (2679, 125833792), (2715, -377501376), (2736, -125833792), (2738, -377501376), (2748, 188750688)]

theorem node612_check : node612 =
    Integer.Sparse.merge (Integer.Sparse.scale (3957804) entry_23_16) (Integer.Sparse.scale (3932306) entry_23_17) := by decide +kernel

theorem node612_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node612 x = (((3957804 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_16 x + ((3932306 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_17 x) := by
  rw [node612_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node613 : Integer.Sparse (Fin 2886) := [(853, 157413024), (859, -157413024), (962, -157413024), (966, -944478144), (1037, 944478144), (1041, 157413024), (1051, -629652096), (1052, -629652096), (1087, 629652096), (1089, 629652096), (2177, -1069828800), (2188, -534914400), (2245, 1069828800), (2254, 534914400)]

theorem node613_check : node613 =
    Integer.Sparse.merge (Integer.Sparse.scale (3279438) entry_23_18) (Integer.Sparse.scale (-2228810) entry_23_19) := by decide +kernel

theorem node613_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node613 x = (((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_18 x + ((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_19 x) := by
  rw [node613_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node614 : Integer.Sparse (Fin 2886) := [(853, 157413024), (859, -157413024), (962, -157413024), (966, -944478144), (1037, 944478144), (1041, 157413024), (1051, -629652096), (1052, -629652096), (1087, 629652096), (1089, 629652096), (2127, 1709771328), (2129, 94375344), (2139, 1139847552), (2143, 251667584), (2155, -1709771328), (2157, 471876720), (2160, 755002752), (2177, -1069828800), (2186, -1139847552), (2188, -534914400), (2191, 1006670336), (2195, 377501376), (2223, -377501376), (2229, -1139847552), (2233, -755002752), (2245, 1069828800), (2252, 1139847552), (2254, 534914400), (2257, -755002752), (2276, -377501376), (2294, 125833792), (2305, 125833792), (2315, 188750688), (2340, -94375344), (2343, -377501376), (2350, 125833792), (2519, 94375344), (2595, -188750688), (2628, -377501376), (2658, 251667584), (2679, 125833792), (2715, -377501376), (2736, -125833792), (2738, -377501376), (2748, 188750688)]

theorem node614_check : node614 =
    Integer.Sparse.merge node612 node613 := by decide +kernel

theorem node614_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node614 x = ((((3957804 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_16 x + ((3932306 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_17 x) + (((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_18 x + ((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_19 x)) := by
  rw [node614_check, Integer.Sparse.eval_merge]
  rw [node612_eval, node613_eval]

def node615 : Integer.Sparse (Fin 2886) := [(848, -231175584), (853, 157413024), (855, -346763376), (859, -157413024), (956, 231175584), (962, -157413024), (966, -944478144), (1035, 346763376), (1037, 944478144), (1041, 157413024), (1049, -231175584), (1051, -629652096), (1052, -629652096), (1085, 231175584), (1087, 629652096), (1089, 629652096), (1792, 44447232), (1796, 38891328), (2023, -44447232), (2027, -27779520), (2048, -11111808), (2075, -11111808), (2086, 11111808), (2111, 3311005824), (2114, 2897130096), (2127, 1709771328), (2129, 94375344), (2139, 1139847552), (2143, 251667584), (2155, -1709771328), (2157, 471876720), (2160, 755002752), (2177, -1069828800), (2186, -1139847552), (2188, -534914400), (2191, 1006670336), (2195, 377501376), (2206, -3311005824), (2209, -2069378640), (2223, -377501376), (2229, -1139847552), (2233, -755002752), (2245, 1069828800), (2252, 1139847552), (2254, 534914400), (2257, -755002752), (2270, -827751456), (2276, -377501376), (2281, -827751456), (2294, 125833792), (2305, 125833792), (2311, 827751456), (2315, 188750688), (2340, -94375344), (2343, -377501376), (2350, 125833792), (2519, 94375344), (2595, -188750688), (2628, -377501376), (2658, 251667584), (2679, 125833792), (2715, -377501376), (2736, -125833792), (2738, -377501376), (2748, 188750688)]

theorem node615_check : node615 =
    Integer.Sparse.merge node611 node614 := by decide +kernel

theorem node615_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node615 x = ((((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_13 x + (((802693 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_14 x + ((8622411 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_15 x)) + ((((3957804 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_16 x + ((3932306 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_17 x) + (((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_18 x + ((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_19 x))) := by
  rw [node615_check, Integer.Sparse.eval_merge]
  rw [node611_eval, node614_eval]

def node616 : Integer.Sparse (Fin 2886) := [(2128, 728688864), (2131, 1082393280), (2140, -1082393280), (2142, -728688864), (2156, -4704557568), (2159, -1634229936), (2187, -2893475424), (2190, -4350853152), (2222, 3975868704), (2230, 1082393280), (2232, 2518490976), (2253, 2893475424), (2256, 4329573120), (2272, 1436097696), (2288, 551836656), (2293, -1789802112), (2304, 21280032), (2313, -1436097696)]

theorem node616_check : node616 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3684421) entry_23_21) (Integer.Sparse.scale (-18865439) entry_23_22) := by decide +kernel

theorem node616_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node616 x = (((-3684421 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_21 x + ((-18865439 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_22 x) := by
  rw [node616_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node617 : Integer.Sparse (Fin 2886) := [(1661, -661515840), (1691, 661515840), (2128, 728688864), (2131, 1082393280), (2140, -1082393280), (2142, -728688864), (2156, -4704557568), (2159, -1634229936), (2187, -2893475424), (2190, -4350853152), (2222, 3975868704), (2230, 1082393280), (2232, 2518490976), (2253, 2893475424), (2256, 4329573120), (2272, 1436097696), (2288, 551836656), (2293, -1789802112), (2304, 21280032), (2313, -1436097696)]

theorem node617_check : node617 =
    Integer.Sparse.merge (Integer.Sparse.scale (918772) entry_23_20) node616 := by decide +kernel

theorem node617_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node617 x = (((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_20 x + (((-3684421 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_21 x + ((-18865439 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_22 x)) := by
  rw [node617_check, Integer.Sparse.eval_merge]
  rw [node616_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node618 : Integer.Sparse (Fin 2886) := [(1137, 339840), (1520, -339840), (2112, 2048395536), (2115, 6827985120), (2117, 1365597024), (2207, -2048395536), (2210, -5462388096), (2271, -3641592064), (2275, -2731194048), (2282, 910398016), (2312, 1365597024), (2314, 1365597024)]

theorem node618_check : node618 =
    Integer.Sparse.merge (Integer.Sparse.scale (14224969) entry_23_23) (Integer.Sparse.scale (472) entry_23_24) := by decide +kernel

theorem node618_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node618 x = (((14224969 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_23 x + ((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_24 x) := by
  rw [node618_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node619 : Integer.Sparse (Fin 2886) := [(1140, 57656448), (1145, -57656448), (1523, -57656448), (1527, -345938688), (1575, 345938688), (1578, 57656448), (1662, -230625792), (1664, -230625792), (1692, 230625792), (1695, 230625792), (2178, 1804108320), (2179, -1804108320), (2246, -1804108320), (2258, -2706162480), (2300, 1804108320), (2306, 2706162480)]

theorem node619_check : node619 =
    Integer.Sparse.merge (Integer.Sparse.scale (6264265) entry_23_25) (Integer.Sparse.scale (1201176) entry_23_26) := by decide +kernel

theorem node619_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node619 x = (((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_25 x + ((1201176 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_26 x) := by
  rw [node619_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node620 : Integer.Sparse (Fin 2886) := [(1137, 339840), (1140, 57656448), (1145, -57656448), (1520, -339840), (1523, -57656448), (1527, -345938688), (1575, 345938688), (1578, 57656448), (1662, -230625792), (1664, -230625792), (1692, 230625792), (1695, 230625792), (2112, 2048395536), (2115, 6827985120), (2117, 1365597024), (2178, 1804108320), (2179, -1804108320), (2207, -2048395536), (2210, -5462388096), (2246, -1804108320), (2258, -2706162480), (2271, -3641592064), (2275, -2731194048), (2282, 910398016), (2300, 1804108320), (2306, 2706162480), (2312, 1365597024), (2314, 1365597024)]

theorem node620_check : node620 =
    Integer.Sparse.merge node618 node619 := by decide +kernel

theorem node620_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node620 x = ((((14224969 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_23 x + ((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_24 x) + (((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_25 x + ((1201176 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_26 x)) := by
  rw [node620_check, Integer.Sparse.eval_merge]
  rw [node618_eval, node619_eval]

def node621 : Integer.Sparse (Fin 2886) := [(1137, 339840), (1140, 57656448), (1145, -57656448), (1520, -339840), (1523, -57656448), (1527, -345938688), (1575, 345938688), (1578, 57656448), (1661, -661515840), (1662, -230625792), (1664, -230625792), (1691, 661515840), (1692, 230625792), (1695, 230625792), (2112, 2048395536), (2115, 6827985120), (2117, 1365597024), (2128, 728688864), (2131, 1082393280), (2140, -1082393280), (2142, -728688864), (2156, -4704557568), (2159, -1634229936), (2178, 1804108320), (2179, -1804108320), (2187, -2893475424), (2190, -4350853152), (2207, -2048395536), (2210, -5462388096), (2222, 3975868704), (2230, 1082393280), (2232, 2518490976), (2246, -1804108320), (2253, 2893475424), (2256, 4329573120), (2258, -2706162480), (2271, -3641592064), (2272, 1436097696), (2275, -2731194048), (2282, 910398016), (2288, 551836656), (2293, -1789802112), (2300, 1804108320), (2304, 21280032), (2306, 2706162480), (2312, 1365597024), (2313, -1436097696), (2314, 1365597024)]

theorem node621_check : node621 =
    Integer.Sparse.merge node617 node620 := by decide +kernel

theorem node621_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node621 x = ((((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_20 x + (((-3684421 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_21 x + ((-18865439 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_22 x)) + ((((14224969 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_23 x + ((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_24 x) + (((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_25 x + ((1201176 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_26 x))) := by
  rw [node621_check, Integer.Sparse.eval_merge]
  rw [node617_eval, node620_eval]

def node622 : Integer.Sparse (Fin 2886) := [(848, -231175584), (853, 157413024), (855, -346763376), (859, -157413024), (956, 231175584), (962, -157413024), (966, -944478144), (1035, 346763376), (1037, 944478144), (1041, 157413024), (1049, -231175584), (1051, -629652096), (1052, -629652096), (1085, 231175584), (1087, 629652096), (1089, 629652096), (1137, 339840), (1140, 57656448), (1145, -57656448), (1520, -339840), (1523, -57656448), (1527, -345938688), (1575, 345938688), (1578, 57656448), (1661, -661515840), (1662, -230625792), (1664, -230625792), (1691, 661515840), (1692, 230625792), (1695, 230625792), (1792, 44447232), (1796, 38891328), (2023, -44447232), (2027, -27779520), (2048, -11111808), (2075, -11111808), (2086, 11111808), (2111, 3311005824), (2112, 2048395536), (2114, 2897130096), (2115, 6827985120), (2117, 1365597024), (2127, 1709771328), (2128, 728688864), (2129, 94375344), (2131, 1082393280), (2139, 1139847552), (2140, -1082393280), (2142, -728688864), (2143, 251667584), (2155, -1709771328), (2156, -4704557568), (2157, 471876720), (2159, -1634229936), (2160, 755002752), (2177, -1069828800), (2178, 1804108320), (2179, -1804108320), (2186, -1139847552), (2187, -2893475424), (2188, -534914400), (2190, -4350853152), (2191, 1006670336), (2195, 377501376), (2206, -3311005824), (2207, -2048395536), (2209, -2069378640), (2210, -5462388096), (2222, 3975868704), (2223, -377501376), (2229, -1139847552), (2230, 1082393280), (2232, 2518490976), (2233, -755002752), (2245, 1069828800), (2246, -1804108320), (2252, 1139847552), (2253, 2893475424), (2254, 534914400), (2256, 4329573120), (2257, -755002752), (2258, -2706162480), (2270, -827751456), (2271, -3641592064), (2272, 1436097696), (2275, -2731194048), (2276, -377501376), (2281, -827751456), (2282, 910398016), (2288, 551836656), (2293, -1789802112), (2294, 125833792), (2300, 1804108320), (2304, 21280032), (2305, 125833792), (2306, 2706162480), (2311, 827751456), (2312, 1365597024), (2313, -1436097696), (2314, 1365597024), (2315, 188750688), (2340, -94375344), (2343, -377501376), (2350, 125833792), (2519, 94375344), (2595, -188750688), (2628, -377501376), (2658, 251667584), (2679, 125833792), (2715, -377501376), (2736, -125833792), (2738, -377501376), (2748, 188750688)]

theorem node622_check : node622 =
    Integer.Sparse.merge node615 node621 := by decide +kernel

theorem node622_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node622 x = (((((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_13 x + (((802693 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_14 x + ((8622411 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_15 x)) + ((((3957804 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_16 x + ((3932306 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_17 x) + (((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_18 x + ((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_19 x))) + ((((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_20 x + (((-3684421 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_21 x + ((-18865439 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_22 x)) + ((((14224969 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_23 x + ((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_24 x) + (((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_25 x + ((1201176 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_26 x)))) := by
  rw [node622_check, Integer.Sparse.eval_merge]
  rw [node615_eval, node621_eval]

def node623 : Integer.Sparse (Fin 2886) := [(846, -980369280), (848, -417015072), (853, 157413024), (855, -509372928), (859, -157413024), (954, 980369280), (956, 417015072), (962, -157413024), (964, 116149680), (966, -944478144), (1035, 393223248), (1037, 944478144), (1041, 157413024), (1049, -184715712), (1051, -629652096), (1052, -629652096), (1085, 184715712), (1087, 629652096), (1089, 629652096), (1118, 536111232), (1119, -253599504), (1123, -253599504), (1125, -536111232), (1126, 253599504), (1129, 253599504), (1137, 339840), (1140, 57656448), (1145, -57656448), (1365, -1876389312), (1367, 1267997520), (1372, 507199008), (1438, 1340278080), (1439, -1014398016), (1468, -253599504), (1470, 536111232), (1472, -253599504), (1475, -507199008), (1498, 253599504), (1520, -339840), (1523, -57656448), (1527, -345938688), (1575, 345938688), (1578, 57656448), (1581, -2144444928), (1582, 760798512), (1585, 1267997520), (1619, 2144444928), (1620, -760798512), (1623, -1014398016), (1644, -253599504), (1647, -253599504), (1655, 253599504), (1661, -661515840), (1662, -230625792), (1664, -230625792), (1691, 661515840), (1692, 230625792), (1695, 230625792), (1792, 44447232), (1796, 38891328), (2023, -44447232), (2027, -27779520), (2048, -11111808), (2075, -11111808), (2086, 11111808), (2107, 872677296), (2110, 2112371280), (2111, 4395938832), (2112, 1615706640), (2113, 1054559904), (2114, 3215513664), (2115, 6827985120), (2116, 745898304), (2117, 1798285920), (2127, 1775556576), (2128, 484664688), (2129, 94375344), (2131, 1082393280), (2133, -362361984), (2139, 1074062304), (2140, -1178793728), (2142, -728688864), (2143, 251667584), (2144, -693990000), (2155, -1940019696), (2156, -5053125360), (2157, 471876720), (2159, -1634229936), (2160, 755002752), (2161, -414633792), (2177, -1069828800), (2178, 1804108320), (2179, -1804108320), (2186, -1402988544), (2187, -3042147680), (2188, -534914400), (2190, -4350853152), (2191, 1006670336), (2193, -798533616), (2195, 377501376), (2202, -1254810384), (2205, -2112371280), (2206, -4013805744), (2207, -1615706640), (2208, -709162560), (2209, -2069378640), (2210, -2866254720), (2211, -108411120), (2221, 164463120), (2222, 3852932832), (2223, -377501376), (2229, -1074062304), (2230, 990191376), (2232, 2518490976), (2233, -755002752), (2234, -572901696), (2245, 1069828800), (2246, -1804108320), (2252, 1402988544), (2253, 2801273520), (2254, 534914400), (2256, 4329573120), (2257, -755002752), (2258, -2706162480), (2259, -572901696), (2267, -109009824), (2269, -586526508), (2270, -615495744), (2271, -2199295744), (2272, 1436097696), (2273, -53307504), (2274, -542167728), (2275, -1000438464), (2276, -377501376), (2278, 109009824), (2280, 163514736), (2281, -1146135024), (2282, -1397276096), (2283, -432688896), (2288, 551836656), (2293, -1789802112), (2294, 125833792), (2300, 1804108320), (2304, 21280032), (2305, 125833792), (2306, 2706162480), (2310, 218019648), (2311, 615495744), (2312, -365158560), (2313, -1436097696), (2314, -365158560), (2315, 188750688), (2317, -396358020), (2319, 449965824), (2321, 915298632), (2326, 915298632), (2329, -328226880), (2330, 470455136), (2336, 220384848), (2340, -94375344), (2341, 94825440), (2343, -377501376), (2346, 20489312), (2348, 30733968), (2350, 125833792), (2514, 168113040), (2519, 94375344), (2520, 68689536), (2590, 327029952), (2595, -188750688), (2626, 163514976), (2628, -377501376), (2633, 168113040), (2635, 137379072), (2656, 183480024), (2658, 251667584), (2675, 20489312), (2677, 30733968), (2679, 125833792), (2711, 220384848), (2713, 189650880), (2715, -377501376), (2734, 235751832), (2736, -125833792), (2738, -377501376), (2740, 30733968), (2747, 40978624), (2748, 188750688)]

theorem node623_check : node623 =
    Integer.Sparse.merge node609 node622 := by decide +kernel

theorem node623_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node623 x = ((((((-9014352 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_0 x + (((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_1 x + ((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_2 x)) + (((-685263 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_3 x + (((3406557 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_4 x + ((-3406562 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_5 x))) + ((((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_6 x + (((-1431032 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_7 x + ((5283323 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_8 x)) + ((((4687144 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_9 x + ((-5584492 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_10 x) + (((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_11 x + ((-1518183 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_12 x)))) + (((((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_13 x + (((802693 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_14 x + ((8622411 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_15 x)) + ((((3957804 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_16 x + ((3932306 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_17 x) + (((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_18 x + ((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_19 x))) + ((((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_20 x + (((-3684421 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_21 x + ((-18865439 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_22 x)) + ((((14224969 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_23 x + ((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_24 x) + (((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_25 x + ((1201176 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_26 x))))) := by
  rw [node623_check, Integer.Sparse.eval_merge]
  rw [node609_eval, node622_eval]

def node624 : Integer.Sparse (Fin 2886) := [(26, -89657280), (98, 89657280), (192, 323622720), (428, -323622720)]

theorem node624_check : node624 =
    Integer.Sparse.merge (Integer.Sparse.scale (449476) entry_24_1) (Integer.Sparse.scale (-124524) entry_24_2) := by decide +kernel

theorem node624_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node624 x = (((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_1 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_2 x) := by
  rw [node624_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node625 : Integer.Sparse (Fin 2886) := [(26, -89657280), (98, 89657280), (192, 323622720), (428, -323622720), (1520, -1875752640), (1657, 1875752640)]

theorem node625_check : node625 =
    Integer.Sparse.merge (Integer.Sparse.scale (2605212) entry_24_0) node624 := by decide +kernel

theorem node625_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node625 x = (((2605212 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_0 x + (((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_1 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_2 x)) := by
  rw [node625_check, Integer.Sparse.eval_merge]
  rw [node624_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node626 : Integer.Sparse (Fin 2886) := [(1134, 1068150240), (1325, 445785840), (1517, -1068150240), (1531, -445785840)]

theorem node626_check : node626 =
    Integer.Sparse.merge (Integer.Sparse.scale (1483542) entry_24_4) (Integer.Sparse.scale (619147) entry_24_5) := by decide +kernel

theorem node626_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node626 x = (((1483542 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_4 x + ((619147 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_5 x) := by
  rw [node626_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node627 : Integer.Sparse (Fin 2886) := [(1134, 1068150240), (1323, 883580400), (1325, 445785840), (1517, -1068150240), (1529, -883580400), (1531, -445785840)]

theorem node627_check : node627 =
    Integer.Sparse.merge (Integer.Sparse.scale (1227195) entry_24_3) node626 := by decide +kernel

theorem node627_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node627 x = (((1227195 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_3 x + (((1483542 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_4 x + ((619147 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_5 x)) := by
  rw [node627_check, Integer.Sparse.eval_merge]
  rw [node626_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node628 : Integer.Sparse (Fin 2886) := [(26, -89657280), (98, 89657280), (192, 323622720), (428, -323622720), (1134, 1068150240), (1323, 883580400), (1325, 445785840), (1517, -1068150240), (1520, -1875752640), (1529, -883580400), (1531, -445785840), (1657, 1875752640)]

theorem node628_check : node628 =
    Integer.Sparse.merge node625 node627 := by decide +kernel

theorem node628_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node628 x = ((((2605212 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_0 x + (((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_1 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_2 x)) + (((1227195 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_3 x + (((1483542 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_4 x + ((619147 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_5 x))) := by
  rw [node628_check, Integer.Sparse.eval_merge]
  rw [node625_eval, node627_eval]

def node629 : Integer.Sparse (Fin 2886) := [(347, 2099803680), (387, -2099803680), (1213, -1241195760), (1325, 1241195760)]

theorem node629_check : node629 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1723883) entry_24_7) (Integer.Sparse.scale (2916394) entry_24_8) := by decide +kernel

theorem node629_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node629 x = (((-1723883 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_7 x + ((2916394 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_8 x) := by
  rw [node629_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node630 : Integer.Sparse (Fin 2886) := [(347, 2099803680), (387, -2099803680), (1132, -336582000), (1213, -1241195760), (1325, 1241195760), (1515, 336582000)]

theorem node630_check : node630 =
    Integer.Sparse.merge (Integer.Sparse.scale (-467475) entry_24_6) node629 := by decide +kernel

theorem node630_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node630 x = (((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_6 x + (((-1723883 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_7 x + ((2916394 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_8 x)) := by
  rw [node630_check, Integer.Sparse.eval_merge]
  rw [node629_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node631 : Integer.Sparse (Fin 2886) := [(302, 1576275840), (441, -1576275840), (1531, -1663447680), (1733, 1663447680)]

theorem node631_check : node631 =
    Integer.Sparse.merge (Integer.Sparse.scale (2310344) entry_24_9) (Integer.Sparse.scale (2189272) entry_24_10) := by decide +kernel

theorem node631_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node631 x = (((2310344 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_9 x + ((2189272 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_10 x) := by
  rw [node631_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node632 : Integer.Sparse (Fin 2886) := [(1133, -1795630320), (1134, -847503360), (1656, 1795630320), (1729, 847503360)]

theorem node632_check : node632 =
    Integer.Sparse.merge (Integer.Sparse.scale (2493931) entry_24_11) (Integer.Sparse.scale (1177088) entry_24_12) := by decide +kernel

theorem node632_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node632 x = (((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_11 x + ((1177088 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_12 x) := by
  rw [node632_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node633 : Integer.Sparse (Fin 2886) := [(302, 1576275840), (441, -1576275840), (1133, -1795630320), (1134, -847503360), (1531, -1663447680), (1656, 1795630320), (1729, 847503360), (1733, 1663447680)]

theorem node633_check : node633 =
    Integer.Sparse.merge node631 node632 := by decide +kernel

theorem node633_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node633 x = ((((2310344 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_9 x + ((2189272 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_10 x) + (((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_11 x + ((1177088 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_12 x)) := by
  rw [node633_check, Integer.Sparse.eval_merge]
  rw [node631_eval, node632_eval]

def node634 : Integer.Sparse (Fin 2886) := [(302, 1576275840), (347, 2099803680), (387, -2099803680), (441, -1576275840), (1132, -336582000), (1133, -1795630320), (1134, -847503360), (1213, -1241195760), (1325, 1241195760), (1515, 336582000), (1531, -1663447680), (1656, 1795630320), (1729, 847503360), (1733, 1663447680)]

theorem node634_check : node634 =
    Integer.Sparse.merge node630 node633 := by decide +kernel

theorem node634_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node634 x = ((((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_6 x + (((-1723883 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_7 x + ((2916394 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_8 x)) + ((((2310344 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_9 x + ((2189272 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_10 x) + (((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_11 x + ((1177088 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_12 x))) := by
  rw [node634_check, Integer.Sparse.eval_merge]
  rw [node630_eval, node633_eval]

def node635 : Integer.Sparse (Fin 2886) := [(26, -89657280), (98, 89657280), (192, 323622720), (302, 1576275840), (347, 2099803680), (387, -2099803680), (428, -323622720), (441, -1576275840), (1132, -336582000), (1133, -1795630320), (1134, 220646880), (1213, -1241195760), (1323, 883580400), (1325, 1686981600), (1515, 336582000), (1517, -1068150240), (1520, -1875752640), (1529, -883580400), (1531, -2109233520), (1656, 1795630320), (1657, 1875752640), (1729, 847503360), (1733, 1663447680)]

theorem node635_check : node635 =
    Integer.Sparse.merge node628 node634 := by decide +kernel

theorem node635_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node635 x = (((((2605212 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_0 x + (((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_1 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_2 x)) + (((1227195 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_3 x + (((1483542 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_4 x + ((619147 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_5 x))) + ((((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_6 x + (((-1723883 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_7 x + ((2916394 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_8 x)) + ((((2310344 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_9 x + ((2189272 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_10 x) + (((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_11 x + ((1177088 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_12 x)))) := by
  rw [node635_check, Integer.Sparse.eval_merge]
  rw [node628_eval, node634_eval]

def node636 : Integer.Sparse (Fin 2886) := [(26, 76381920), (128, -76381920), (1133, -460473120), (1516, 460473120)]

theorem node636_check : node636 =
    Integer.Sparse.merge (Integer.Sparse.scale (-106086) entry_24_14) (Integer.Sparse.scale (-639546) entry_24_15) := by decide +kernel

theorem node636_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node636 x = (((-106086 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_14 x + ((-639546 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_15 x) := by
  rw [node636_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node637 : Integer.Sparse (Fin 2886) := [(26, 76381920), (128, -76381920), (657, 362783520), (807, -362783520), (1133, -460473120), (1516, 460473120)]

theorem node637_check : node637 =
    Integer.Sparse.merge (Integer.Sparse.scale (503866) entry_24_13) node636 := by decide +kernel

theorem node637_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node637 x = (((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_13 x + (((-106086 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_14 x + ((-639546 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_15 x)) := by
  rw [node637_check, Integer.Sparse.eval_merge]
  rw [node636_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node638 : Integer.Sparse (Fin 2886) := [(1211, -2167367040), (1323, 2167367040), (1329, 807343920), (1534, -807343920)]

theorem node638_check : node638 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3010232) entry_24_16) (Integer.Sparse.scale (1121311) entry_24_17) := by decide +kernel

theorem node638_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node638 x = (((-3010232 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_16 x + ((1121311 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_17 x) := by
  rw [node638_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node639 : Integer.Sparse (Fin 2886) := [(105, 2484252000), (137, -2484252000), (1338, 1283548320), (1549, -1283548320)]

theorem node639_check : node639 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3450350) entry_24_18) (Integer.Sparse.scale (1782706) entry_24_19) := by decide +kernel

theorem node639_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node639 x = (((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_18 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_19 x) := by
  rw [node639_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block3

end OAI
