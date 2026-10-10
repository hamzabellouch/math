import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Part4

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

def node160 : Integer.Sparse (Fin 2886) := [(1340, -481533696), (1345, 481533696), (1552, 481533696), (1554, -481533696), (2170, -1411469568), (2177, 1411469568), (2245, 1411469568), (2254, -1411469568), (2436, 429793056), (2457, -1171313856), (2460, 1179031680), (2461, 1171313856), (2462, -1608824736), (2560, 1171313856), (2563, -1179031680), (2564, -1171313856), (2565, 749238624), (2610, 429793056)]

theorem node160_check : node160 =
    Integer.Sparse.merge node157 node159 := by decide +kernel

theorem node160_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node160 x = ((((1671992 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x + ((-4900936 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x) + (((1492337 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + (((-4093860 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x + ((4067062 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x))) := by
  rw [node160_check, Integer.Sparse.eval_merge]
  rw [node157_eval, node159_eval]

def node161 : Integer.Sparse (Fin 2886) := [(1894, -95592096), (1899, 95592096), (1900, 95592096), (1905, -264314592), (1916, -95592096), (1938, 528629184), (2012, -264314592)]

theorem node161_check : node161 =
    Integer.Sparse.merge (Integer.Sparse.scale (-917759) entry_7_17) (Integer.Sparse.scale (331917) entry_7_18) := by decide +kernel

theorem node161_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node161 x = (((-917759 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x) := by
  rw [node161_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node162 : Integer.Sparse (Fin 2886) := [(1894, -95592096), (1899, 95592096), (1900, 95592096), (1905, -264314592), (1916, -95592096), (1938, 528629184), (2012, -264314592), (2433, 1995128640), (2440, -1995128640), (2466, -1995128640), (2475, 1995128640)]

theorem node162_check : node162 =
    Integer.Sparse.merge (Integer.Sparse.scale (6927530) entry_7_16) node161 := by decide +kernel

theorem node162_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node162 x = (((6927530 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + (((-917759 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x)) := by
  rw [node162_check, Integer.Sparse.eval_merge]
  rw [node161_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node163 : Integer.Sparse (Fin 2886) := [(1906, -1927233504), (1939, 3854467008), (2013, -1927233504), (2820, 2527783488), (2825, -2527783488), (2827, -2527783488), (2840, 2527783488)]

theorem node163_check : node163 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6691783) entry_7_20) (Integer.Sparse.scale (-8777026) entry_7_21) := by decide +kernel

theorem node163_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node163 x = (((-6691783 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x + ((-8777026 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_21 x) := by
  rw [node163_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node164 : Integer.Sparse (Fin 2886) := [(1759, -28867392), (1761, 57734784), (1764, -28867392), (1906, -1927233504), (1939, 3854467008), (2013, -1927233504), (2820, 2527783488), (2825, -2527783488), (2827, -2527783488), (2840, 2527783488)]

theorem node164_check : node164 =
    Integer.Sparse.merge (Integer.Sparse.scale (-100234) entry_7_19) node163 := by decide +kernel

theorem node164_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node164 x = (((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x + (((-6691783 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x + ((-8777026 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_21 x)) := by
  rw [node164_check, Integer.Sparse.eval_merge]
  rw [node163_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node165 : Integer.Sparse (Fin 2886) := [(1759, -28867392), (1761, 57734784), (1764, -28867392), (1894, -95592096), (1899, 95592096), (1900, 95592096), (1905, -264314592), (1906, -1927233504), (1916, -95592096), (1938, 528629184), (1939, 3854467008), (2012, -264314592), (2013, -1927233504), (2433, 1995128640), (2440, -1995128640), (2466, -1995128640), (2475, 1995128640), (2820, 2527783488), (2825, -2527783488), (2827, -2527783488), (2840, 2527783488)]

theorem node165_check : node165 =
    Integer.Sparse.merge node162 node164 := by decide +kernel

theorem node165_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node165 x = ((((6927530 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + (((-917759 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x)) + (((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x + (((-6691783 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x + ((-8777026 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_21 x))) := by
  rw [node165_check, Integer.Sparse.eval_merge]
  rw [node162_eval, node164_eval]

def node166 : Integer.Sparse (Fin 2886) := [(1340, -481533696), (1345, 481533696), (1552, 481533696), (1554, -481533696), (1759, -28867392), (1761, 57734784), (1764, -28867392), (1894, -95592096), (1899, 95592096), (1900, 95592096), (1905, -264314592), (1906, -1927233504), (1916, -95592096), (1938, 528629184), (1939, 3854467008), (2012, -264314592), (2013, -1927233504), (2170, -1411469568), (2177, 1411469568), (2245, 1411469568), (2254, -1411469568), (2433, 1995128640), (2436, 429793056), (2440, -1995128640), (2457, -1171313856), (2460, 1179031680), (2461, 1171313856), (2462, -1608824736), (2466, -1995128640), (2475, 1995128640), (2560, 1171313856), (2563, -1179031680), (2564, -1171313856), (2565, 749238624), (2610, 429793056), (2820, 2527783488), (2825, -2527783488), (2827, -2527783488), (2840, 2527783488)]

theorem node166_check : node166 =
    Integer.Sparse.merge node160 node165 := by decide +kernel

theorem node166_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node166 x = (((((1671992 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x + ((-4900936 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x) + (((1492337 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + (((-4093860 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x + ((4067062 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x))) + ((((6927530 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + (((-917759 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x)) + (((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x + (((-6691783 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x + ((-8777026 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_21 x)))) := by
  rw [node166_check, Integer.Sparse.eval_merge]
  rw [node160_eval, node165_eval]

def node167 : Integer.Sparse (Fin 2886) := [(915, -796202784), (918, 113710752), (923, 101989728), (925, 796202784), (926, -113710752), (929, -203979456), (940, 101989728), (999, 796202784), (1002, -113710752), (1003, -796202784), (1004, 113710752), (1340, -481533696), (1345, 481533696), (1552, 481533696), (1554, -481533696), (1759, -28867392), (1761, 57734784), (1764, -28867392), (1891, 441763488), (1894, -95592096), (1896, -883526976), (1899, 95592096), (1900, 95592096), (1905, -264314592), (1906, -1927233504), (1915, 441763488), (1916, -95592096), (1938, 528629184), (1939, 3854467008), (2012, -264314592), (2013, -1927233504), (2163, 80928), (2166, -575902944), (2170, -753835680), (2172, -80928), (2173, 575902944), (2177, 96201792), (2188, 657633888), (2236, -80928), (2239, 575902944), (2240, 80928), (2241, -575902944), (2245, 1411469568), (2254, -1411469568), (2425, -764192688), (2426, 46174176), (2429, 2095804512), (2433, 1995128640), (2435, -46174176), (2436, -1666011456), (2440, -1995128640), (2456, 545851920), (2457, -1217488032), (2460, -916772832), (2461, 1217488032), (2462, 486979776), (2466, -1995128640), (2475, 1995128640), (2559, 509461792), (2560, 1171313856), (2563, -1179031680), (2564, -1171313856), (2565, 749238624), (2608, -436681536), (2610, 429793056), (2787, 109170384), (2799, 109170384), (2819, 1879681824), (2820, 2527783488), (2824, -3759363648), (2825, -2527783488), (2827, -2527783488), (2834, 145560512), (2839, 1879681824), (2840, 2527783488), (2861, -218340768)]

theorem node167_check : node167 =
    Integer.Sparse.merge node156 node166 := by decide +kernel

theorem node167_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node167 x = ((((((2283451 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + ((-394829 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x) + (((1999663 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x + (((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + ((2764593 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x))) + ((((354131 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x + (((-7277099 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + ((6526673 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x)) + (((-281 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x + (((1533901 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((-160327 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x)))) + (((((1671992 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x + ((-4900936 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x) + (((1492337 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + (((-4093860 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x + ((4067062 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x))) + ((((6927530 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + (((-917759 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x)) + (((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x + (((-6691783 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x + ((-8777026 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_21 x))))) := by
  rw [node167_check, Integer.Sparse.eval_merge]
  rw [node156_eval, node166_eval]

def node168 : Integer.Sparse (Fin 2886) := [(844, 728227584), (849, -728227584), (952, -728227584), (957, 1456455168), (1028, -728227584), (1047, -728227584), (1083, 728227584), (2206, -1690778880), (2209, 1690778880), (2267, 1690778880), (2270, -1690778880)]

theorem node168_check : node168 =
    Integer.Sparse.merge (Integer.Sparse.scale (5870760) entry_8_0) (Integer.Sparse.scale (5057136) entry_8_1) := by decide +kernel

theorem node168_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node168 x = (((5870760 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + ((5057136 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x) := by
  rw [node168_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node169 : Integer.Sparse (Fin 2886) := [(843, 547754976), (847, -547754976), (951, -547754976), (955, 1095509952), (1027, -547754976), (1045, -547754976), (1082, 547754976), (2119, 560146464), (2134, -560146464), (2147, 560146464), (2181, -560146464), (2213, -1120292928), (2224, 560146464), (2247, 560146464)]

theorem node169_check : node169 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3889906) entry_8_3) (Integer.Sparse.scale (3803854) entry_8_4) := by decide +kernel

theorem node169_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node169 x = (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x) := by
  rw [node169_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node170 : Integer.Sparse (Fin 2886) := [(843, 547754976), (847, -547754976), (951, -547754976), (955, 1095509952), (1027, -547754976), (1045, -547754976), (1082, 547754976), (2104, 1356839568), (2108, -1356839568), (2119, 560146464), (2134, -560146464), (2147, 560146464), (2181, -560146464), (2199, -1356839568), (2203, 2713679136), (2213, -1120292928), (2224, 560146464), (2247, 560146464), (2264, -1356839568), (2279, -1356839568), (2309, 1356839568)]

theorem node170_check : node170 =
    Integer.Sparse.merge (Integer.Sparse.scale (9422497) entry_8_2) node169 := by decide +kernel

theorem node170_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node170 x = (((9422497 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x + (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x)) := by
  rw [node170_check, Integer.Sparse.eval_merge]
  rw [node169_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node171 : Integer.Sparse (Fin 2886) := [(843, 547754976), (844, 728227584), (847, -547754976), (849, -728227584), (951, -547754976), (952, -728227584), (955, 1095509952), (957, 1456455168), (1027, -547754976), (1028, -728227584), (1045, -547754976), (1047, -728227584), (1082, 547754976), (1083, 728227584), (2104, 1356839568), (2108, -1356839568), (2119, 560146464), (2134, -560146464), (2147, 560146464), (2181, -560146464), (2199, -1356839568), (2203, 2713679136), (2206, -1690778880), (2209, 1690778880), (2213, -1120292928), (2224, 560146464), (2247, 560146464), (2264, -1356839568), (2267, 1690778880), (2270, -1690778880), (2279, -1356839568), (2309, 1356839568)]

theorem node171_check : node171 =
    Integer.Sparse.merge node168 node170 := by decide +kernel

theorem node171_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node171 x = ((((5870760 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + ((5057136 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x) + (((9422497 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x + (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x))) := by
  rw [node171_check, Integer.Sparse.eval_merge]
  rw [node168_eval, node170_eval]

def node172 : Integer.Sparse (Fin 2886) := [(2163, 80928), (2172, -80928), (2236, -80928), (2240, 80928), (2511, 1240066512), (2515, -1240066512), (2587, -1240066512), (2591, 2480133024), (2622, -1240066512), (2634, -1240066512), (2655, 1240066512)]

theorem node172_check : node172 =
    Integer.Sparse.merge (Integer.Sparse.scale (8611573) entry_8_6) (Integer.Sparse.scale (-281) entry_8_7) := by decide +kernel

theorem node172_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node172 x = (((8611573 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + ((-281 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x) := by
  rw [node172_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node173 : Integer.Sparse (Fin 2886) := [(961, 920203200), (965, -920203200), (1032, -920203200), (1036, 920203200), (2163, 80928), (2172, -80928), (2236, -80928), (2240, 80928), (2511, 1240066512), (2515, -1240066512), (2587, -1240066512), (2591, 2480133024), (2622, -1240066512), (2634, -1240066512), (2655, 1240066512)]

theorem node173_check : node173 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3195150) entry_8_5) node172 := by decide +kernel

theorem node173_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node173 x = (((-3195150 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x + (((8611573 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + ((-281 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x)) := by
  rw [node173_check, Integer.Sparse.eval_merge]
  rw [node172_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node174 : Integer.Sparse (Fin 2886) := [(1767, -377144352), (1775, 377144352), (1978, 377144352), (1987, -377144352), (2120, 325416864), (2123, 162708432), (2136, -271180720), (2148, 1627084320), (2151, -976250592), (2183, -108472288), (2214, -1355903600), (2217, 1952501184), (2226, -1464375888), (2249, -162708432), (2284, -488125296), (2290, 922014448), (2301, 271180720), (2332, -325416864), (2335, -162708432), (2345, 271180720), (2510, 325416864), (2513, -976250592), (2586, -596597584), (2589, 1952501184), (2621, -1464375888), (2632, -488125296), (2654, 1030486736), (2674, 108472288), (2710, 162708432), (2732, -271180720)]

theorem node174_check : node174 =
    Integer.Sparse.merge (Integer.Sparse.scale (1309529) entry_8_9) (Integer.Sparse.scale (13559036) entry_8_10) := by decide +kernel

theorem node174_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node174 x = (((1309529 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((13559036 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x) := by
  rw [node174_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node175 : Integer.Sparse (Fin 2886) := [(1767, -377144352), (1775, 377144352), (1978, 377144352), (1987, -377144352), (2103, 2252928096), (2106, -2252928096), (2120, 325416864), (2123, 162708432), (2136, -271180720), (2148, 1627084320), (2151, -976250592), (2183, -108472288), (2198, -2252928096), (2201, 4505856192), (2214, -1355903600), (2217, 1952501184), (2226, -1464375888), (2249, -162708432), (2263, -4005205504), (2277, -500650688), (2284, -488125296), (2290, 922014448), (2301, 271180720), (2308, 2252928096), (2332, -325416864), (2335, -162708432), (2345, 271180720), (2510, 325416864), (2513, -976250592), (2586, -596597584), (2589, 1952501184), (2621, -1464375888), (2632, -488125296), (2654, 1030486736), (2674, 108472288), (2710, 162708432), (2732, -271180720)]

theorem node175_check : node175 =
    Integer.Sparse.merge (Integer.Sparse.scale (15645334) entry_8_8) node174 := by decide +kernel

theorem node175_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node175 x = (((15645334 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + (((1309529 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((13559036 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x)) := by
  rw [node175_check, Integer.Sparse.eval_merge]
  rw [node174_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node176 : Integer.Sparse (Fin 2886) := [(961, 920203200), (965, -920203200), (1032, -920203200), (1036, 920203200), (1767, -377144352), (1775, 377144352), (1978, 377144352), (1987, -377144352), (2103, 2252928096), (2106, -2252928096), (2120, 325416864), (2123, 162708432), (2136, -271180720), (2148, 1627084320), (2151, -976250592), (2163, 80928), (2172, -80928), (2183, -108472288), (2198, -2252928096), (2201, 4505856192), (2214, -1355903600), (2217, 1952501184), (2226, -1464375888), (2236, -80928), (2240, 80928), (2249, -162708432), (2263, -4005205504), (2277, -500650688), (2284, -488125296), (2290, 922014448), (2301, 271180720), (2308, 2252928096), (2332, -325416864), (2335, -162708432), (2345, 271180720), (2510, 325416864), (2511, 1240066512), (2513, -976250592), (2515, -1240066512), (2586, -596597584), (2587, -1240066512), (2589, 1952501184), (2591, 2480133024), (2621, -1464375888), (2622, -1240066512), (2632, -488125296), (2634, -1240066512), (2654, 1030486736), (2655, 1240066512), (2674, 108472288), (2710, 162708432), (2732, -271180720)]

theorem node176_check : node176 =
    Integer.Sparse.merge node173 node175 := by decide +kernel

theorem node176_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node176 x = ((((-3195150 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x + (((8611573 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + ((-281 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x)) + (((15645334 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + (((1309529 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((13559036 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x))) := by
  rw [node176_check, Integer.Sparse.eval_merge]
  rw [node173_eval, node175_eval]

def node177 : Integer.Sparse (Fin 2886) := [(843, 547754976), (844, 728227584), (847, -547754976), (849, -728227584), (951, -547754976), (952, -728227584), (955, 1095509952), (957, 1456455168), (961, 920203200), (965, -920203200), (1027, -547754976), (1028, -728227584), (1032, -920203200), (1036, 920203200), (1045, -547754976), (1047, -728227584), (1082, 547754976), (1083, 728227584), (1767, -377144352), (1775, 377144352), (1978, 377144352), (1987, -377144352), (2103, 2252928096), (2104, 1356839568), (2106, -2252928096), (2108, -1356839568), (2119, 560146464), (2120, 325416864), (2123, 162708432), (2134, -560146464), (2136, -271180720), (2147, 560146464), (2148, 1627084320), (2151, -976250592), (2163, 80928), (2172, -80928), (2181, -560146464), (2183, -108472288), (2198, -2252928096), (2199, -1356839568), (2201, 4505856192), (2203, 2713679136), (2206, -1690778880), (2209, 1690778880), (2213, -1120292928), (2214, -1355903600), (2217, 1952501184), (2224, 560146464), (2226, -1464375888), (2236, -80928), (2240, 80928), (2247, 560146464), (2249, -162708432), (2263, -4005205504), (2264, -1356839568), (2267, 1690778880), (2270, -1690778880), (2277, -500650688), (2279, -1356839568), (2284, -488125296), (2290, 922014448), (2301, 271180720), (2308, 2252928096), (2309, 1356839568), (2332, -325416864), (2335, -162708432), (2345, 271180720), (2510, 325416864), (2511, 1240066512), (2513, -976250592), (2515, -1240066512), (2586, -596597584), (2587, -1240066512), (2589, 1952501184), (2591, 2480133024), (2621, -1464375888), (2622, -1240066512), (2632, -488125296), (2634, -1240066512), (2654, 1030486736), (2655, 1240066512), (2674, 108472288), (2710, 162708432), (2732, -271180720)]

theorem node177_check : node177 =
    Integer.Sparse.merge node171 node176 := by decide +kernel

theorem node177_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node177 x = (((((5870760 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + ((5057136 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x) + (((9422497 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x + (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x))) + ((((-3195150 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x + (((8611573 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + ((-281 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x)) + (((15645334 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + (((1309529 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((13559036 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x)))) := by
  rw [node177_check, Integer.Sparse.eval_merge]
  rw [node171_eval, node176_eval]

def node178 : Integer.Sparse (Fin 2886) := [(1134, 844103088), (1138, -844103088), (1517, -844103088), (1521, 1688206176), (1569, -844103088), (1658, -844103088), (1689, 844103088), (2111, 2535445440), (2114, -2535445440), (2206, 2535445440), (2267, -5070890880), (2270, 2535445440), (2281, -2535445440), (2311, 2535445440)]

theorem node178_check : node178 =
    Integer.Sparse.merge (Integer.Sparse.scale (5861827) entry_8_11) (Integer.Sparse.scale (-17607260) entry_8_12) := by decide +kernel

theorem node178_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node178 x = (((5861827 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x + ((-17607260 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x) := by
  rw [node178_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node179 : Integer.Sparse (Fin 2886) := [(2120, 1117403520), (2123, -977728080), (2136, 139675440), (2148, -1117403520), (2151, 977728080), (2183, -139675440), (2226, 1117403520), (2249, -1117403520), (2290, -558701760), (2301, 558701760), (2332, 558701760), (2333, 3159106272), (2335, -698377200), (2337, -3159106272), (2345, -139675440), (2510, -558701760), (2511, -3159106272), (2513, 698377200), (2515, 3159106272), (2632, 558701760), (2634, 3159106272), (2654, -1117403520), (2655, -3159106272), (2674, 139675440), (2710, -558701760), (2712, -3159106272), (2732, 1117403520), (2733, 3159106272)]

theorem node179_check : node179 =
    Integer.Sparse.merge (Integer.Sparse.scale (21938238) entry_8_14) (Integer.Sparse.scale (11639620) entry_8_15) := by decide +kernel

theorem node179_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node179 x = (((21938238 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x + ((11639620 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x) := by
  rw [node179_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node180 : Integer.Sparse (Fin 2886) := [(2120, 1117403520), (2123, -977728080), (2136, 139675440), (2148, -1117403520), (2151, 977728080), (2183, -139675440), (2226, 1117403520), (2249, -1117403520), (2290, -558701760), (2301, 558701760), (2332, 558701760), (2333, 3159106272), (2335, -698377200), (2337, -3545641296), (2345, -139675440), (2347, 386535024), (2510, -558701760), (2511, -3159106272), (2513, 698377200), (2515, 2772571248), (2591, 773070048), (2632, 558701760), (2634, 2772571248), (2654, -1117403520), (2655, -3159106272), (2674, 139675440), (2676, 386535024), (2710, -558701760), (2712, -3545641296), (2732, 1117403520), (2733, 3159106272)]

theorem node180_check : node180 =
    Integer.Sparse.merge (Integer.Sparse.scale (2684271) entry_8_13) node179 := by decide +kernel

theorem node180_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node180 x = (((2684271 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + (((21938238 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x + ((11639620 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x)) := by
  rw [node180_check, Integer.Sparse.eval_merge]
  rw [node179_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node181 : Integer.Sparse (Fin 2886) := [(1134, 844103088), (1138, -844103088), (1517, -844103088), (1521, 1688206176), (1569, -844103088), (1658, -844103088), (1689, 844103088), (2111, 2535445440), (2114, -2535445440), (2120, 1117403520), (2123, -977728080), (2136, 139675440), (2148, -1117403520), (2151, 977728080), (2183, -139675440), (2206, 2535445440), (2226, 1117403520), (2249, -1117403520), (2267, -5070890880), (2270, 2535445440), (2281, -2535445440), (2290, -558701760), (2301, 558701760), (2311, 2535445440), (2332, 558701760), (2333, 3159106272), (2335, -698377200), (2337, -3545641296), (2345, -139675440), (2347, 386535024), (2510, -558701760), (2511, -3159106272), (2513, 698377200), (2515, 2772571248), (2591, 773070048), (2632, 558701760), (2634, 2772571248), (2654, -1117403520), (2655, -3159106272), (2674, 139675440), (2676, 386535024), (2710, -558701760), (2712, -3545641296), (2732, 1117403520), (2733, 3159106272)]

theorem node181_check : node181 =
    Integer.Sparse.merge node178 node180 := by decide +kernel

theorem node181_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node181 x = ((((5861827 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x + ((-17607260 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x) + (((2684271 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + (((21938238 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x + ((11639620 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x))) := by
  rw [node181_check, Integer.Sparse.eval_merge]
  rw [node178_eval, node180_eval]

def node182 : Integer.Sparse (Fin 2886) := [(1770, 7586208), (1773, 7586208), (1778, -15172416), (1783, -593670240), (1793, 593670240), (1981, -7586208), (1985, -7586208), (1990, 7586208), (1991, 7586208), (2000, 593670240), (2024, -593670240)]

theorem node182_check : node182 =
    Integer.Sparse.merge (Integer.Sparse.scale (2061355) entry_8_17) (Integer.Sparse.scale (52682) entry_8_18) := by decide +kernel

theorem node182_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node182 x = (((2061355 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x + ((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x) := by
  rw [node182_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node183 : Integer.Sparse (Fin 2886) := [(1770, 7586208), (1773, 7586208), (1778, -15172416), (1783, -593670240), (1793, 593670240), (1981, -7586208), (1985, -7586208), (1990, 7586208), (1991, 7586208), (2000, 593670240), (2024, -593670240), (2518, 2478194352), (2521, -2478194352), (2594, 2478194352), (2624, -4956388704), (2627, 2478194352), (2636, -2478194352), (2657, 2478194352)]

theorem node183_check : node183 =
    Integer.Sparse.merge (Integer.Sparse.scale (-17209683) entry_8_16) node182 := by decide +kernel

theorem node183_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node183 x = (((-17209683 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + (((2061355 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x + ((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x)) := by
  rw [node183_check, Integer.Sparse.eval_merge]
  rw [node182_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node184 : Integer.Sparse (Fin 2886) := [(1784, 656597088), (1794, -656597088), (2001, -656597088), (2025, 656597088), (2164, 239382528), (2167, 239382528), (2174, -718147584), (2237, -209459712), (2242, 239382528), (2296, -119691264), (2298, 209459712), (2777, 119691264), (2779, 119691264), (2859, -149614080), (2867, -239382528), (2870, 119691264), (2875, 149614080)]

theorem node184_check : node184 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2279851) entry_8_20) (Integer.Sparse.scale (2493568) entry_8_21) := by decide +kernel

theorem node184_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node184 x = (((-2279851 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x + ((2493568 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_21 x) := by
  rw [node184_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node185 : Integer.Sparse (Fin 2886) := [(1731, -84860928), (1732, 84860928), (1750, 84860928), (1751, -84860928), (1784, 656597088), (1794, -656597088), (2001, -656597088), (2025, 656597088), (2164, 239382528), (2167, 239382528), (2174, -718147584), (2237, -209459712), (2242, 239382528), (2296, -119691264), (2298, 209459712), (2777, 119691264), (2779, 119691264), (2859, -149614080), (2867, -239382528), (2870, 119691264), (2875, 149614080)]

theorem node185_check : node185 =
    Integer.Sparse.merge (Integer.Sparse.scale (294656) entry_8_19) node184 := by decide +kernel

theorem node185_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node185 x = (((294656 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x + (((-2279851 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x + ((2493568 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_21 x)) := by
  rw [node185_check, Integer.Sparse.eval_merge]
  rw [node184_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node186 : Integer.Sparse (Fin 2886) := [(1731, -84860928), (1732, 84860928), (1750, 84860928), (1751, -84860928), (1770, 7586208), (1773, 7586208), (1778, -15172416), (1783, -593670240), (1784, 656597088), (1793, 593670240), (1794, -656597088), (1981, -7586208), (1985, -7586208), (1990, 7586208), (1991, 7586208), (2000, 593670240), (2001, -656597088), (2024, -593670240), (2025, 656597088), (2164, 239382528), (2167, 239382528), (2174, -718147584), (2237, -209459712), (2242, 239382528), (2296, -119691264), (2298, 209459712), (2518, 2478194352), (2521, -2478194352), (2594, 2478194352), (2624, -4956388704), (2627, 2478194352), (2636, -2478194352), (2657, 2478194352), (2777, 119691264), (2779, 119691264), (2859, -149614080), (2867, -239382528), (2870, 119691264), (2875, 149614080)]

theorem node186_check : node186 =
    Integer.Sparse.merge node183 node185 := by decide +kernel

theorem node186_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node186 x = ((((-17209683 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + (((2061355 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x + ((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x)) + (((294656 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x + (((-2279851 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x + ((2493568 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_21 x))) := by
  rw [node186_check, Integer.Sparse.eval_merge]
  rw [node183_eval, node185_eval]

def node187 : Integer.Sparse (Fin 2886) := [(1134, 844103088), (1138, -844103088), (1517, -844103088), (1521, 1688206176), (1569, -844103088), (1658, -844103088), (1689, 844103088), (1731, -84860928), (1732, 84860928), (1750, 84860928), (1751, -84860928), (1770, 7586208), (1773, 7586208), (1778, -15172416), (1783, -593670240), (1784, 656597088), (1793, 593670240), (1794, -656597088), (1981, -7586208), (1985, -7586208), (1990, 7586208), (1991, 7586208), (2000, 593670240), (2001, -656597088), (2024, -593670240), (2025, 656597088), (2111, 2535445440), (2114, -2535445440), (2120, 1117403520), (2123, -977728080), (2136, 139675440), (2148, -1117403520), (2151, 977728080), (2164, 239382528), (2167, 239382528), (2174, -718147584), (2183, -139675440), (2206, 2535445440), (2226, 1117403520), (2237, -209459712), (2242, 239382528), (2249, -1117403520), (2267, -5070890880), (2270, 2535445440), (2281, -2535445440), (2290, -558701760), (2296, -119691264), (2298, 209459712), (2301, 558701760), (2311, 2535445440), (2332, 558701760), (2333, 3159106272), (2335, -698377200), (2337, -3545641296), (2345, -139675440), (2347, 386535024), (2510, -558701760), (2511, -3159106272), (2513, 698377200), (2515, 2772571248), (2518, 2478194352), (2521, -2478194352), (2591, 773070048), (2594, 2478194352), (2624, -4956388704), (2627, 2478194352), (2632, 558701760), (2634, 2772571248), (2636, -2478194352), (2654, -1117403520), (2655, -3159106272), (2657, 2478194352), (2674, 139675440), (2676, 386535024), (2710, -558701760), (2712, -3545641296), (2732, 1117403520), (2733, 3159106272), (2777, 119691264), (2779, 119691264), (2859, -149614080), (2867, -239382528), (2870, 119691264), (2875, 149614080)]

theorem node187_check : node187 =
    Integer.Sparse.merge node181 node186 := by decide +kernel

theorem node187_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node187 x = (((((5861827 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x + ((-17607260 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x) + (((2684271 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + (((21938238 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x + ((11639620 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x))) + ((((-17209683 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + (((2061355 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x + ((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x)) + (((294656 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x + (((-2279851 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x + ((2493568 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_21 x)))) := by
  rw [node187_check, Integer.Sparse.eval_merge]
  rw [node181_eval, node186_eval]

def node188 : Integer.Sparse (Fin 2886) := [(843, 547754976), (844, 728227584), (847, -547754976), (849, -728227584), (951, -547754976), (952, -728227584), (955, 1095509952), (957, 1456455168), (961, 920203200), (965, -920203200), (1027, -547754976), (1028, -728227584), (1032, -920203200), (1036, 920203200), (1045, -547754976), (1047, -728227584), (1082, 547754976), (1083, 728227584), (1134, 844103088), (1138, -844103088), (1517, -844103088), (1521, 1688206176), (1569, -844103088), (1658, -844103088), (1689, 844103088), (1731, -84860928), (1732, 84860928), (1750, 84860928), (1751, -84860928), (1767, -377144352), (1770, 7586208), (1773, 7586208), (1775, 377144352), (1778, -15172416), (1783, -593670240), (1784, 656597088), (1793, 593670240), (1794, -656597088), (1978, 377144352), (1981, -7586208), (1985, -7586208), (1987, -377144352), (1990, 7586208), (1991, 7586208), (2000, 593670240), (2001, -656597088), (2024, -593670240), (2025, 656597088), (2103, 2252928096), (2104, 1356839568), (2106, -2252928096), (2108, -1356839568), (2111, 2535445440), (2114, -2535445440), (2119, 560146464), (2120, 1442820384), (2123, -815019648), (2134, -560146464), (2136, -131505280), (2147, 560146464), (2148, 509680800), (2151, 1477488), (2163, 80928), (2164, 239382528), (2167, 239382528), (2172, -80928), (2174, -718147584), (2181, -560146464), (2183, -248147728), (2198, -2252928096), (2199, -1356839568), (2201, 4505856192), (2203, 2713679136), (2206, 844666560), (2209, 1690778880), (2213, -1120292928), (2214, -1355903600), (2217, 1952501184), (2224, 560146464), (2226, -346972368), (2236, -80928), (2237, -209459712), (2240, 80928), (2242, 239382528), (2247, 560146464), (2249, -1280111952), (2263, -4005205504), (2264, -1356839568), (2267, -3380112000), (2270, 844666560), (2277, -500650688), (2279, -1356839568), (2281, -2535445440), (2284, -488125296), (2290, 363312688), (2296, -119691264), (2298, 209459712), (2301, 829882480), (2308, 2252928096), (2309, 1356839568), (2311, 2535445440), (2332, 233284896), (2333, 3159106272), (2335, -861085632), (2337, -3545641296), (2345, 131505280), (2347, 386535024), (2510, -233284896), (2511, -1919039760), (2513, -277873392), (2515, 1532504736), (2518, 2478194352), (2521, -2478194352), (2586, -596597584), (2587, -1240066512), (2589, 1952501184), (2591, 3253203072), (2594, 2478194352), (2621, -1464375888), (2622, -1240066512), (2624, -4956388704), (2627, 2478194352), (2632, 70576464), (2634, 1532504736), (2636, -2478194352), (2654, -86916784), (2655, -1919039760), (2657, 2478194352), (2674, 248147728), (2676, 386535024), (2710, -395993328), (2712, -3545641296), (2732, 846222800), (2733, 3159106272), (2777, 119691264), (2779, 119691264), (2859, -149614080), (2867, -239382528), (2870, 119691264), (2875, 149614080)]

theorem node188_check : node188 =
    Integer.Sparse.merge node177 node187 := by decide +kernel

theorem node188_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node188 x = ((((((5870760 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + ((5057136 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x) + (((9422497 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x + (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x))) + ((((-3195150 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x + (((8611573 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + ((-281 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x)) + (((15645334 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + (((1309529 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((13559036 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x)))) + (((((5861827 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x + ((-17607260 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x) + (((2684271 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + (((21938238 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x + ((11639620 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x))) + ((((-17209683 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + (((2061355 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x + ((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x)) + (((294656 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x + (((-2279851 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x + ((2493568 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_21 x))))) := by
  rw [node188_check, Integer.Sparse.eval_merge]
  rw [node177_eval, node187_eval]

def node189 : Integer.Sparse (Fin 2886) := [(49, 84330432), (55, -84330432), (110, -84330432), (113, 84330432), (1771, 1475236224), (1776, -2950472448), (1789, 1475236224)]

theorem node189_check : node189 =
    Integer.Sparse.merge (Integer.Sparse.scale (5122348) entry_9_0) (Integer.Sparse.scale (-292814) entry_9_1) := by decide +kernel

theorem node189_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node189 x = (((5122348 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + ((-292814 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x) := by
  rw [node189_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node190 : Integer.Sparse (Fin 2886) := [(47, 196849440), (53, -196849440), (108, -196849440), (111, 196849440), (1803, -676630944), (1832, 676630944), (1909, 676630944), (1982, -676630944)]

theorem node190_check : node190 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2349413) entry_9_3) (Integer.Sparse.scale (-683505) entry_9_4) := by decide +kernel

theorem node190_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node190 x = (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x) := by
  rw [node190_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node191 : Integer.Sparse (Fin 2886) := [(47, 196849440), (53, -196849440), (108, -196849440), (111, 196849440), (1768, -345877632), (1780, 345877632), (1803, -676630944), (1832, 676630944), (1909, 676630944), (1979, 345877632), (1982, -676630944), (1993, -345877632)]

theorem node191_check : node191 =
    Integer.Sparse.merge (Integer.Sparse.scale (1200964) entry_9_2) node190 := by decide +kernel

theorem node191_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node191 x = (((1200964 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x + (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x)) := by
  rw [node191_check, Integer.Sparse.eval_merge]
  rw [node190_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block4

end OAI
