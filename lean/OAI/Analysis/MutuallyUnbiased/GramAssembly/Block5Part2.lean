import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Part1

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

def node64 : Integer.Sparse (Fin 2886) := [(1119, -771840), (1123, -385920), (1126, -385920), (1129, -771840), (1137, 1967153760), (1142, 1967153760), (1367, -771840), (1372, -385920), (1439, -771840), (1468, -385920), (1472, -771840), (1475, -771840), (1498, -771840), (1520, 3934307520), (1526, 1967153760), (1574, 1967153760), (1582, -385920), (1585, -771840), (1620, -771840), (1623, -771840), (1644, -771840), (1647, -771840), (1655, -385920), (1657, -3131028000), (1661, -1163874240), (1691, -581937120), (2111, 9346066560), (2114, 9346066560), (2127, -9411950880), (2139, -9411950880), (2155, -9411950880), (2170, 1050524640), (2177, 4202098560), (2186, -9411950880), (2188, 1050524640), (2206, 18692133120), (2209, 9346066560), (2221, -9411950880), (2229, -18823901760), (2245, 2101049280), (2252, -18823901760), (2254, 2101049280), (2267, 9346066560), (2268, -9411950880), (2270, 18692133120), (2281, 9346066560), (2311, 9346066560)]

theorem node64_check : node64 =
    Integer.Sparse.merge node61 node63 := by decide +kernel

theorem node64_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node64 x = ((((6490324 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + (((-6536077 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x + ((-885101 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x)) + (((729531 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + (((1366079 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x + ((-804 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x))) := by
  rw [node64_check, Integer.Sparse.eval_merge]
  rw [node61_eval, node63_eval]

def node65 : Integer.Sparse (Fin 2886) := [(846, -1924917120), (848, 598328640), (855, 598328640), (954, -3849834240), (956, 1196657280), (964, 598328640), (1035, 598328640), (1044, -3849834240), (1046, 598328640), (1049, 1196657280), (1085, 598328640), (1119, -771840), (1123, -385920), (1126, -385920), (1129, -771840), (1137, 1967153760), (1142, 1967153760), (1367, -771840), (1372, -385920), (1439, -771840), (1468, -385920), (1472, -771840), (1475, -771840), (1498, -771840), (1520, 3934307520), (1526, 1967153760), (1574, 1967153760), (1582, -385920), (1585, -771840), (1620, -771840), (1623, -771840), (1644, -771840), (1647, -771840), (1655, -385920), (1657, -3131028000), (1661, -1163874240), (1691, -581937120), (2107, 4053834720), (2110, 5148691200), (2111, 13399901280), (2112, 6756330240), (2113, 5405112960), (2114, 9346066560), (2115, 27025320960), (2116, 2702556480), (2117, 6756330240), (2127, -9411950880), (2128, 1447346400), (2133, 578938560), (2139, -9411950880), (2140, 964897600), (2144, 1447346400), (2155, -9411950880), (2156, 1447346400), (2161, 578938560), (2170, 1050524640), (2177, 4202098560), (2186, -9411950880), (2187, 964897600), (2188, 1050524640), (2193, 1447346400), (2202, 8107669440), (2205, 10297382400), (2206, 26799802560), (2207, 13512660480), (2208, 4864601664), (2209, 9346066560), (2210, 27025320960), (2211, 3243067776), (2221, -9411950880), (2222, 1157877120), (2229, -18823901760), (2230, 1447346400), (2234, 1157877120), (2245, 2101049280), (2252, -18823901760), (2253, 1447346400), (2254, 2101049280), (2259, 1157877120), (2266, 10297382400), (2267, 14751179520), (2268, -9411950880), (2269, 6080752080), (2270, 18692133120), (2271, 36033761280), (2273, 8107669440), (2274, 1447346400), (2275, 16215192576), (2278, 2702556480), (2280, 8107669440), (2281, 9346066560), (2282, 18016880640), (2283, 10810128384), (2310, 5405112960), (2311, 9346066560), (2312, 13512660480), (2314, 27025320960), (2317, 2026917360), (2319, 289469280), (2321, 723673200), (2326, 723673200), (2329, 2702556480), (2330, 482448800), (2336, 1447346400), (2341, 868407840), (2346, 482448800), (2348, 1447346400), (2514, 1447346400), (2520, 868407840), (2590, 1736815680), (2626, 1157877120), (2633, 1447346400), (2635, 1736815680), (2656, 2171019600), (2675, 482448800), (2677, 1447346400), (2711, 1447346400), (2713, 1736815680), (2734, 2171019600), (2740, 1447346400), (2747, 964897600)]

theorem node65_check : node65 =
    Integer.Sparse.merge node59 node64 := by decide +kernel

theorem node65_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node65 x = (((((5630326 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + (((-668374 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x + ((3015305 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x)) + (((1787740 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + (((415506 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x + ((14075688 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x))) + ((((6490324 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + (((-6536077 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x + ((-885101 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x)) + (((729531 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + (((1366079 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x + ((-804 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x)))) := by
  rw [node65_check, Integer.Sparse.eval_merge]
  rw [node59_eval, node64_eval]

def node66 : Integer.Sparse (Fin 2886) := [(841, -2072255040), (949, -6216765120), (1043, -2072255040), (2333, -533946240), (2337, -1067892480), (2347, -533946240), (2511, -533946240), (2515, -1067892480), (2587, -1067892480), (2591, -1067892480), (2622, -1067892480), (2634, -1067892480), (2655, -533946240), (2676, -533946240), (2712, -1067892480), (2733, -533946240)]

theorem node66_check : node66 =
    Integer.Sparse.merge (Integer.Sparse.scale (-719533) entry_6_1) (Integer.Sparse.scale (-741592) entry_6_2) := by decide +kernel

theorem node66_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node66 x = (((-719533 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-741592 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x) := by
  rw [node66_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node67 : Integer.Sparse (Fin 2886) := [(841, -2072255040), (949, -6216765120), (1043, -2072255040), (2104, 2590988400), (2108, 7772965200), (2199, 7772965200), (2203, 15545930400), (2264, 7772965200), (2279, 7772965200), (2309, 2590988400), (2333, -533946240), (2337, -1067892480), (2347, -533946240), (2511, -533946240), (2515, -1067892480), (2587, -1067892480), (2591, -1067892480), (2622, -1067892480), (2634, -1067892480), (2655, -533946240), (2676, -533946240), (2712, -1067892480), (2733, -533946240)]

theorem node67_check : node67 =
    Integer.Sparse.merge (Integer.Sparse.scale (3598595) entry_6_0) node66 := by decide +kernel

theorem node67_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node67 x = (((3598595 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + (((-719533 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-741592 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x)) := by
  rw [node67_check, Integer.Sparse.eval_merge]
  rw [node66_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node68 : Integer.Sparse (Fin 2886) := [(844, -1709108640), (849, -5127325920), (952, -5127325920), (957, -10254651840), (1028, -5127325920), (1047, -5127325920), (1083, -1709108640), (2111, 9346066560), (2114, 9346066560), (2206, 18692133120), (2209, 9346066560), (2267, 9346066560), (2270, 18692133120), (2281, 9346066560), (2311, 9346066560)]

theorem node68_check : node68 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2373762) entry_6_4) (Integer.Sparse.scale (6490324) entry_6_5) := by decide +kernel

theorem node68_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node68 x = (((-2373762 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((6490324 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x) := by
  rw [node68_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node69 : Integer.Sparse (Fin 2886) := [(844, -1709108640), (849, -5127325920), (952, -5127325920), (957, -10254651840), (1028, -5127325920), (1047, -5127325920), (1083, -1709108640), (2102, 7346753280), (2111, 9346066560), (2114, 9346066560), (2197, 22040259840), (2206, 18692133120), (2209, 9346066560), (2261, 7346753280), (2267, 9346066560), (2270, 18692133120), (2281, 9346066560), (2311, 9346066560)]

theorem node69_check : node69 =
    Integer.Sparse.merge (Integer.Sparse.scale (2550956) entry_6_3) node68 := by decide +kernel

theorem node69_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node69 x = (((2550956 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + (((-2373762 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((6490324 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x)) := by
  rw [node69_check, Integer.Sparse.eval_merge]
  rw [node68_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node70 : Integer.Sparse (Fin 2886) := [(841, -2072255040), (844, -1709108640), (849, -5127325920), (949, -6216765120), (952, -5127325920), (957, -10254651840), (1028, -5127325920), (1043, -2072255040), (1047, -5127325920), (1083, -1709108640), (2102, 7346753280), (2104, 2590988400), (2108, 7772965200), (2111, 9346066560), (2114, 9346066560), (2197, 22040259840), (2199, 7772965200), (2203, 15545930400), (2206, 18692133120), (2209, 9346066560), (2261, 7346753280), (2264, 7772965200), (2267, 9346066560), (2270, 18692133120), (2279, 7772965200), (2281, 9346066560), (2309, 2590988400), (2311, 9346066560), (2333, -533946240), (2337, -1067892480), (2347, -533946240), (2511, -533946240), (2515, -1067892480), (2587, -1067892480), (2591, -1067892480), (2622, -1067892480), (2634, -1067892480), (2655, -533946240), (2676, -533946240), (2712, -1067892480), (2733, -533946240)]

theorem node70_check : node70 =
    Integer.Sparse.merge node67 node69 := by decide +kernel

theorem node70_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node70 x = ((((3598595 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + (((-719533 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-741592 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x)) + (((2550956 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + (((-2373762 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((6490324 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x))) := by
  rw [node70_check, Integer.Sparse.eval_merge]
  rw [node67_eval, node69_eval]

def node71 : Integer.Sparse (Fin 2886) := [(1729, -1062829440), (1730, -3188488320), (1749, -1062829440), (2119, 4987666800), (2134, 1662555600), (2147, 4987666800), (2181, 1662555600), (2213, 9975333600), (2224, 4987666800), (2247, 4987666800)]

theorem node71_check : node71 =
    Integer.Sparse.merge (Integer.Sparse.scale (2309105) entry_6_7) (Integer.Sparse.scale (-369038) entry_6_8) := by decide +kernel

theorem node71_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node71 x = (((2309105 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((-369038 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x) := by
  rw [node71_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node72 : Integer.Sparse (Fin 2886) := [(1729, -1062829440), (1730, -3188488320), (1749, -1062829440), (2103, 8000506080), (2106, 24001518240), (2119, 4987666800), (2134, 1662555600), (2147, 4987666800), (2181, 1662555600), (2198, 24001518240), (2201, 48003036480), (2213, 9975333600), (2224, 4987666800), (2247, 4987666800), (2263, 32002024320), (2277, 16001012160), (2308, 8000506080)]

theorem node72_check : node72 =
    Integer.Sparse.merge (Integer.Sparse.scale (11111814) entry_6_6) node71 := by decide +kernel

theorem node72_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node72 x = (((11111814 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + (((2309105 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((-369038 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x)) := by
  rw [node72_check, Integer.Sparse.eval_merge]
  rw [node71_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node73 : Integer.Sparse (Fin 2886) := [(1116, 3831340320), (1120, 7662680640), (1127, 3831340320), (1134, -107600400), (1138, -322801200), (1363, 3831340320), (1368, 7662680640), (1436, 7662680640), (1440, 7662680640), (1464, 7662680640), (1473, 7662680640), (1496, 3831340320), (1517, -322801200), (1521, -645602400), (1569, -322801200), (1583, 3831340320), (1621, 7662680640), (1642, 3831340320), (1658, -322801200), (1689, -107600400)]

theorem node73_check : node73 =
    Integer.Sparse.merge (Integer.Sparse.scale (-149445) entry_6_10) (Integer.Sparse.scale (5321306) entry_6_11) := by decide +kernel

theorem node73_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node73 x = (((-149445 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x + ((5321306 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x) := by
  rw [node73_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node74 : Integer.Sparse (Fin 2886) := [(1116, 3831340320), (1120, 7662680640), (1127, 3831340320), (1134, -107600400), (1138, -322801200), (1363, 3831340320), (1368, 7662680640), (1436, 7662680640), (1440, 7662680640), (1464, 7662680640), (1473, 7662680640), (1496, 3831340320), (1517, -322801200), (1521, -645602400), (1569, -322801200), (1583, 3831340320), (1621, 7662680640), (1642, 3831340320), (1658, -322801200), (1689, -107600400), (2163, 30366135360), (2172, 30366135360), (2236, 10122045120), (2240, 30366135360)]

theorem node74_check : node74 =
    Integer.Sparse.merge (Integer.Sparse.scale (7029198) entry_6_9) node73 := by decide +kernel

theorem node74_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node74 x = (((7029198 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + (((-149445 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x + ((5321306 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x)) := by
  rw [node74_check, Integer.Sparse.eval_merge]
  rw [node73_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node75 : Integer.Sparse (Fin 2886) := [(1116, 3831340320), (1120, 7662680640), (1127, 3831340320), (1134, -107600400), (1138, -322801200), (1363, 3831340320), (1368, 7662680640), (1436, 7662680640), (1440, 7662680640), (1464, 7662680640), (1473, 7662680640), (1496, 3831340320), (1517, -322801200), (1521, -645602400), (1569, -322801200), (1583, 3831340320), (1621, 7662680640), (1642, 3831340320), (1658, -322801200), (1689, -107600400), (1729, -1062829440), (1730, -3188488320), (1749, -1062829440), (2103, 8000506080), (2106, 24001518240), (2119, 4987666800), (2134, 1662555600), (2147, 4987666800), (2163, 30366135360), (2172, 30366135360), (2181, 1662555600), (2198, 24001518240), (2201, 48003036480), (2213, 9975333600), (2224, 4987666800), (2236, 10122045120), (2240, 30366135360), (2247, 4987666800), (2263, 32002024320), (2277, 16001012160), (2308, 8000506080)]

theorem node75_check : node75 =
    Integer.Sparse.merge node72 node74 := by decide +kernel

theorem node75_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node75 x = ((((11111814 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + (((2309105 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((-369038 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x)) + (((7029198 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + (((-149445 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x + ((5321306 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x))) := by
  rw [node75_check, Integer.Sparse.eval_merge]
  rw [node72_eval, node74_eval]

def node76 : Integer.Sparse (Fin 2886) := [(841, -2072255040), (844, -1709108640), (849, -5127325920), (949, -6216765120), (952, -5127325920), (957, -10254651840), (1028, -5127325920), (1043, -2072255040), (1047, -5127325920), (1083, -1709108640), (1116, 3831340320), (1120, 7662680640), (1127, 3831340320), (1134, -107600400), (1138, -322801200), (1363, 3831340320), (1368, 7662680640), (1436, 7662680640), (1440, 7662680640), (1464, 7662680640), (1473, 7662680640), (1496, 3831340320), (1517, -322801200), (1521, -645602400), (1569, -322801200), (1583, 3831340320), (1621, 7662680640), (1642, 3831340320), (1658, -322801200), (1689, -107600400), (1729, -1062829440), (1730, -3188488320), (1749, -1062829440), (2102, 7346753280), (2103, 8000506080), (2104, 2590988400), (2106, 24001518240), (2108, 7772965200), (2111, 9346066560), (2114, 9346066560), (2119, 4987666800), (2134, 1662555600), (2147, 4987666800), (2163, 30366135360), (2172, 30366135360), (2181, 1662555600), (2197, 22040259840), (2198, 24001518240), (2199, 7772965200), (2201, 48003036480), (2203, 15545930400), (2206, 18692133120), (2209, 9346066560), (2213, 9975333600), (2224, 4987666800), (2236, 10122045120), (2240, 30366135360), (2247, 4987666800), (2261, 7346753280), (2263, 32002024320), (2264, 7772965200), (2267, 9346066560), (2270, 18692133120), (2277, 16001012160), (2279, 7772965200), (2281, 9346066560), (2308, 8000506080), (2309, 2590988400), (2311, 9346066560), (2333, -533946240), (2337, -1067892480), (2347, -533946240), (2511, -533946240), (2515, -1067892480), (2587, -1067892480), (2591, -1067892480), (2622, -1067892480), (2634, -1067892480), (2655, -533946240), (2676, -533946240), (2712, -1067892480), (2733, -533946240)]

theorem node76_check : node76 =
    Integer.Sparse.merge node70 node75 := by decide +kernel

theorem node76_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node76 x = (((((3598595 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + (((-719533 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-741592 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x)) + (((2550956 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + (((-2373762 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((6490324 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x))) + ((((11111814 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + (((2309105 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((-369038 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x)) + (((7029198 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + (((-149445 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x + ((5321306 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x)))) := by
  rw [node76_check, Integer.Sparse.eval_merge]
  rw [node70_eval, node75_eval]

def node77 : Integer.Sparse (Fin 2886) := [(860, 5681203200), (893, 5681203200), (968, 17043609600), (2358, -3329974800), (2374, -6659949600), (2383, -3329974800), (2413, -3329974800), (2448, -6659949600), (2469, -3329974800), (2528, -6659949600), (2537, -3329974800), (2551, -6659949600), (2571, -3329974800), (2600, -6659949600), (2602, -6659949600), (2612, -6659949600)]

theorem node77_check : node77 =
    Integer.Sparse.merge (Integer.Sparse.scale (1972640) entry_7_1) (Integer.Sparse.scale (-4624965) entry_7_2) := by decide +kernel

theorem node77_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node77 x = (((1972640 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((-4624965 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x) := by
  rw [node77_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node78 : Integer.Sparse (Fin 2886) := [(860, 5681203200), (893, 5681203200), (968, 17043609600), (2122, -6047397360), (2135, -2015799120), (2150, -6047397360), (2182, -2015799120), (2216, -12094794720), (2225, -6047397360), (2248, -6047397360), (2358, -3329974800), (2374, -6659949600), (2383, -3329974800), (2413, -3329974800), (2448, -6659949600), (2469, -3329974800), (2528, -6659949600), (2537, -3329974800), (2551, -6659949600), (2571, -3329974800), (2600, -6659949600), (2602, -6659949600), (2612, -6659949600)]

theorem node78_check : node78 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2799721) entry_7_0) node77 := by decide +kernel

theorem node78_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node78 x = (((-2799721 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + (((1972640 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((-4624965 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x)) := by
  rw [node78_check, Integer.Sparse.eval_merge]
  rw [node77_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node79 : Integer.Sparse (Fin 2886) := [(865, -10186426080), (880, -3395475360), (899, -10186426080), (933, -3395475360), (974, -20372852160), (985, -10186426080), (1012, -10186426080), (2127, -9411950880), (2139, -9411950880), (2155, -9411950880), (2186, -9411950880), (2221, -9411950880), (2229, -18823901760), (2252, -18823901760), (2268, -9411950880)]

theorem node79_check : node79 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4715938) entry_7_4) (Integer.Sparse.scale (-6536077) entry_7_5) := by decide +kernel

theorem node79_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node79 x = (((-4715938 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((-6536077 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x) := by
  rw [node79_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node80 : Integer.Sparse (Fin 2886) := [(865, -10186426080), (880, -3395475360), (899, -10186426080), (933, -3395475360), (974, -20372852160), (985, -10186426080), (1012, -10186426080), (2118, 2657263680), (2127, -9411950880), (2139, -9411950880), (2146, 2657263680), (2155, -9411950880), (2186, -9411950880), (2212, 5314527360), (2221, -9411950880), (2229, -18823901760), (2252, -18823901760), (2268, -9411950880), (2331, 2657263680), (2508, 2657263680), (2584, 10629054720)]

theorem node80_check : node80 =
    Integer.Sparse.merge (Integer.Sparse.scale (1845322) entry_7_3) node79 := by decide +kernel

theorem node80_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node80 x = (((1845322 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + (((-4715938 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((-6536077 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x)) := by
  rw [node80_check, Integer.Sparse.eval_merge]
  rw [node79_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node81 : Integer.Sparse (Fin 2886) := [(860, 5681203200), (865, -10186426080), (880, -3395475360), (893, 5681203200), (899, -10186426080), (933, -3395475360), (968, 17043609600), (974, -20372852160), (985, -10186426080), (1012, -10186426080), (2118, 2657263680), (2122, -6047397360), (2127, -9411950880), (2135, -2015799120), (2139, -9411950880), (2146, 2657263680), (2150, -6047397360), (2155, -9411950880), (2182, -2015799120), (2186, -9411950880), (2212, 5314527360), (2216, -12094794720), (2221, -9411950880), (2225, -6047397360), (2229, -18823901760), (2248, -6047397360), (2252, -18823901760), (2268, -9411950880), (2331, 2657263680), (2358, -3329974800), (2374, -6659949600), (2383, -3329974800), (2413, -3329974800), (2448, -6659949600), (2469, -3329974800), (2508, 2657263680), (2528, -6659949600), (2537, -3329974800), (2551, -6659949600), (2571, -3329974800), (2584, 10629054720), (2600, -6659949600), (2602, -6659949600), (2612, -6659949600)]

theorem node81_check : node81 =
    Integer.Sparse.merge node78 node80 := by decide +kernel

theorem node81_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node81 x = ((((-2799721 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + (((1972640 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((-4624965 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x)) + (((1845322 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + (((-4715938 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((-6536077 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x))) := by
  rw [node81_check, Integer.Sparse.eval_merge]
  rw [node78_eval, node80_eval]

def node82 : Integer.Sparse (Fin 2886) := [(1754, 21735855360), (1756, 7245285120), (1762, 7245285120), (2354, 15072150960), (2370, 45216452880), (2409, 15072150960), (2444, 60288603840), (2524, 30144301920), (2547, 45216452880), (2596, 90432905760)]

theorem node82_check : node82 =
    Integer.Sparse.merge (Integer.Sparse.scale (20933543) entry_7_7) (Integer.Sparse.scale (2515724) entry_7_8) := by decide +kernel

theorem node82_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node82 x = (((20933543 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + ((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x) := by
  rw [node82_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node83 : Integer.Sparse (Fin 2886) := [(1754, 21735855360), (1756, 7245285120), (1762, 7245285120), (2119, 4987666800), (2134, 1662555600), (2147, 4987666800), (2181, 1662555600), (2213, 9975333600), (2224, 4987666800), (2247, 4987666800), (2354, 15072150960), (2370, 45216452880), (2409, 15072150960), (2444, 60288603840), (2524, 30144301920), (2547, 45216452880), (2596, 90432905760)]

theorem node83_check : node83 =
    Integer.Sparse.merge (Integer.Sparse.scale (2309105) entry_7_6) node82 := by decide +kernel

theorem node83_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node83 x = (((2309105 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + (((20933543 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + ((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x)) := by
  rw [node83_check, Integer.Sparse.eval_merge]
  rw [node82_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node84 : Integer.Sparse (Fin 2886) := [(1151, 5900270400), (1170, 11800540800), (1179, 5900270400), (1214, -12324465360), (1224, -4108155120), (1237, 5900270400), (1264, 11800540800), (1283, 5900270400), (1326, -12324465360), (1349, -4108155120), (1379, 11800540800), (1389, 5900270400), (1405, 11800540800), (1422, 5900270400), (1447, 11800540800), (1449, 11800540800), (1457, 11800540800), (1532, -24648930720), (1540, -12324465360), (1558, -12324465360)]

theorem node84_check : node84 =
    Integer.Sparse.merge (Integer.Sparse.scale (-5705771) entry_7_10) (Integer.Sparse.scale (8194820) entry_7_11) := by decide +kernel

theorem node84_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node84 x = (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x + ((8194820 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x) := by
  rw [node84_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node85 : Integer.Sparse (Fin 2886) := [(1151, 5900270400), (1170, 11800540800), (1179, 5900270400), (1214, -12324465360), (1224, -4108155120), (1237, 5900270400), (1264, 11800540800), (1283, 5900270400), (1326, -12324465360), (1349, -4108155120), (1379, 11800540800), (1389, 5900270400), (1405, 11800540800), (1422, 5900270400), (1447, 11800540800), (1449, 11800540800), (1457, 11800540800), (1532, -24648930720), (1540, -12324465360), (1558, -12324465360), (2425, 25470819360), (2456, 25470819360), (2559, 16980546240), (2608, 6792218496), (2787, 25470819360), (2799, 25470819360), (2834, 33961092480), (2861, 10188327744)]

theorem node85_check : node85 =
    Integer.Sparse.merge (Integer.Sparse.scale (11792046) entry_7_9) node84 := by decide +kernel

theorem node85_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node85 x = (((11792046 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x + ((8194820 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x)) := by
  rw [node85_check, Integer.Sparse.eval_merge]
  rw [node84_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node86 : Integer.Sparse (Fin 2886) := [(1151, 5900270400), (1170, 11800540800), (1179, 5900270400), (1214, -12324465360), (1224, -4108155120), (1237, 5900270400), (1264, 11800540800), (1283, 5900270400), (1326, -12324465360), (1349, -4108155120), (1379, 11800540800), (1389, 5900270400), (1405, 11800540800), (1422, 5900270400), (1447, 11800540800), (1449, 11800540800), (1457, 11800540800), (1532, -24648930720), (1540, -12324465360), (1558, -12324465360), (1754, 21735855360), (1756, 7245285120), (1762, 7245285120), (2119, 4987666800), (2134, 1662555600), (2147, 4987666800), (2181, 1662555600), (2213, 9975333600), (2224, 4987666800), (2247, 4987666800), (2354, 15072150960), (2370, 45216452880), (2409, 15072150960), (2425, 25470819360), (2444, 60288603840), (2456, 25470819360), (2524, 30144301920), (2547, 45216452880), (2559, 16980546240), (2596, 90432905760), (2608, 6792218496), (2787, 25470819360), (2799, 25470819360), (2834, 33961092480), (2861, 10188327744)]

theorem node86_check : node86 =
    Integer.Sparse.merge node83 node85 := by decide +kernel

theorem node86_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node86 x = ((((2309105 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + (((20933543 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + ((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x)) + (((11792046 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x + ((8194820 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x))) := by
  rw [node86_check, Integer.Sparse.eval_merge]
  rw [node83_eval, node85_eval]

def node87 : Integer.Sparse (Fin 2886) := [(860, 5681203200), (865, -10186426080), (880, -3395475360), (893, 5681203200), (899, -10186426080), (933, -3395475360), (968, 17043609600), (974, -20372852160), (985, -10186426080), (1012, -10186426080), (1151, 5900270400), (1170, 11800540800), (1179, 5900270400), (1214, -12324465360), (1224, -4108155120), (1237, 5900270400), (1264, 11800540800), (1283, 5900270400), (1326, -12324465360), (1349, -4108155120), (1379, 11800540800), (1389, 5900270400), (1405, 11800540800), (1422, 5900270400), (1447, 11800540800), (1449, 11800540800), (1457, 11800540800), (1532, -24648930720), (1540, -12324465360), (1558, -12324465360), (1754, 21735855360), (1756, 7245285120), (1762, 7245285120), (2118, 2657263680), (2119, 4987666800), (2122, -6047397360), (2127, -9411950880), (2134, 1662555600), (2135, -2015799120), (2139, -9411950880), (2146, 2657263680), (2147, 4987666800), (2150, -6047397360), (2155, -9411950880), (2181, 1662555600), (2182, -2015799120), (2186, -9411950880), (2212, 5314527360), (2213, 9975333600), (2216, -12094794720), (2221, -9411950880), (2224, 4987666800), (2225, -6047397360), (2229, -18823901760), (2247, 4987666800), (2248, -6047397360), (2252, -18823901760), (2268, -9411950880), (2331, 2657263680), (2354, 15072150960), (2358, -3329974800), (2370, 45216452880), (2374, -6659949600), (2383, -3329974800), (2409, 15072150960), (2413, -3329974800), (2425, 25470819360), (2444, 60288603840), (2448, -6659949600), (2456, 25470819360), (2469, -3329974800), (2508, 2657263680), (2524, 30144301920), (2528, -6659949600), (2537, -3329974800), (2547, 45216452880), (2551, -6659949600), (2559, 16980546240), (2571, -3329974800), (2584, 10629054720), (2596, 90432905760), (2600, -6659949600), (2602, -6659949600), (2608, 6792218496), (2612, -6659949600), (2787, 25470819360), (2799, 25470819360), (2834, 33961092480), (2861, 10188327744)]

theorem node87_check : node87 =
    Integer.Sparse.merge node81 node86 := by decide +kernel

theorem node87_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node87 x = (((((-2799721 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + (((1972640 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((-4624965 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x)) + (((1845322 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + (((-4715938 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((-6536077 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x))) + ((((2309105 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + (((20933543 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + ((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x)) + (((11792046 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x + ((8194820 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x)))) := by
  rw [node87_check, Integer.Sparse.eval_merge]
  rw [node81_eval, node86_eval]

def node88 : Integer.Sparse (Fin 2886) := [(600, 5447082240), (606, 1361770560), (1665, -2437168320), (1667, -4874336640), (1673, -2437168320), (1683, -2437168320)]

theorem node88_check : node88 =
    Integer.Sparse.merge (Integer.Sparse.scale (472837) entry_8_1) (Integer.Sparse.scale (-846239) entry_8_2) := by decide +kernel

theorem node88_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node88 x = (((472837 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x + ((-846239 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x) := by
  rw [node88_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node89 : Integer.Sparse (Fin 2886) := [(600, 5447082240), (606, 1361770560), (1656, -613356480), (1658, -1840069440), (1665, -2437168320), (1667, -4874336640), (1673, -2437168320), (1683, -2437168320), (1689, -613356480)]

theorem node89_check : node89 =
    Integer.Sparse.merge (Integer.Sparse.scale (-212971) entry_8_0) node88 := by decide +kernel

theorem node89_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node89 x = (((-212971 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + (((472837 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x + ((-846239 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x)) := by
  rw [node89_check, Integer.Sparse.eval_merge]
  rw [node88_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node90 : Integer.Sparse (Fin 2886) := [(538, -2279030400), (540, -6837091200), (561, -2279030400), (1657, -5098181760), (1661, -5098181760), (1691, -2549090880)]

theorem node90_check : node90 =
    Integer.Sparse.merge (Integer.Sparse.scale (-791330) entry_8_4) (Integer.Sparse.scale (-885101) entry_8_5) := by decide +kernel

theorem node90_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node90 x = (((-791330 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x + ((-885101 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x) := by
  rw [node90_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node91 : Integer.Sparse (Fin 2886) := [(538, -2279030400), (540, -6837091200), (561, -2279030400), (1657, -5098181760), (1661, -5098181760), (1691, -2549090880), (1753, 2231884800), (1765, 557971200)]

theorem node91_check : node91 =
    Integer.Sparse.merge (Integer.Sparse.scale (193740) entry_8_3) node90 := by decide +kernel

theorem node91_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node91 x = (((193740 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + (((-791330 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x + ((-885101 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x)) := by
  rw [node91_check, Integer.Sparse.eval_merge]
  rw [node90_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node92 : Integer.Sparse (Fin 2886) := [(538, -2279030400), (540, -6837091200), (561, -2279030400), (600, 5447082240), (606, 1361770560), (1656, -613356480), (1657, -5098181760), (1658, -1840069440), (1661, -5098181760), (1665, -2437168320), (1667, -4874336640), (1673, -2437168320), (1683, -2437168320), (1689, -613356480), (1691, -2549090880), (1753, 2231884800), (1765, 557971200)]

theorem node92_check : node92 =
    Integer.Sparse.merge node89 node91 := by decide +kernel

theorem node92_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node92 x = ((((-212971 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + (((472837 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x + ((-846239 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x)) + (((193740 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + (((-791330 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x + ((-885101 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x))) := by
  rw [node92_check, Integer.Sparse.eval_merge]
  rw [node89_eval, node91_eval]

def node93 : Integer.Sparse (Fin 2886) := [(249, 4187833920), (250, 16751335680), (1754, 21735855360), (1756, 7245285120), (1762, 7245285120)]

theorem node93_check : node93 =
    Integer.Sparse.merge (Integer.Sparse.scale (2515724) entry_8_7) (Integer.Sparse.scale (1454109) entry_8_8) := by decide +kernel

theorem node93_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node93 x = (((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + ((1454109 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x) := by
  rw [node93_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node94 : Integer.Sparse (Fin 2886) := [(249, 4187833920), (250, 16751335680), (1729, -1062829440), (1730, -3188488320), (1749, -1062829440), (1754, 21735855360), (1756, 7245285120), (1762, 7245285120)]

theorem node94_check : node94 =
    Integer.Sparse.merge (Integer.Sparse.scale (-369038) entry_8_6) node93 := by decide +kernel

theorem node94_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node94 x = (((-369038 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + (((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + ((1454109 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x)) := by
  rw [node94_check, Integer.Sparse.eval_merge]
  rw [node93_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node95 : Integer.Sparse (Fin 2886) := [(447, -1446969600), (449, -4340908800), (478, -1446969600), (547, -936371520), (548, -1872743040), (550, -936371520), (558, -936371520)]

theorem node95_check : node95 =
    Integer.Sparse.merge (Integer.Sparse.scale (-502420) entry_8_10) (Integer.Sparse.scale (-325129) entry_8_11) := by decide +kernel

theorem node95_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node95 x = (((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x + ((-325129 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x) := by
  rw [node95_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block5

end OAI
