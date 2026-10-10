import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Part1

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

def node64 : Integer.Sparse (Fin 2886) := [(862, 577936368), (879, -577936368), (896, 577936368), (932, -577936368), (971, -1155872736), (984, 577936368), (1011, 577936368), (2354, 1523875248), (2370, -1523875248), (2409, 1523875248), (2444, -1693194720), (2524, -1354555776), (2547, -1523875248), (2596, 3047750496)]

theorem node64_check : node64 =
    Integer.Sparse.merge (Integer.Sparse.scale (10582467) entry_3_3) (Integer.Sparse.scale (-4013447) entry_3_4) := by decide +kernel

theorem node64_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node64 x = (((10582467 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x) := by
  rw [node64_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node65 : Integer.Sparse (Fin 2886) := [(862, 577936368), (879, -577936368), (896, 577936368), (932, -577936368), (971, -1155872736), (984, 577936368), (1011, 577936368), (2122, 927842256), (2135, -927842256), (2150, 927842256), (2182, -927842256), (2216, -1855684512), (2225, 927842256), (2248, 927842256), (2354, 1523875248), (2370, -1523875248), (2409, 1523875248), (2444, -1693194720), (2524, -1354555776), (2547, -1523875248), (2596, 3047750496)]

theorem node65_check : node65 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6443349) entry_3_2) node64 := by decide +kernel

theorem node65_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node65 x = (((-6443349 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((10582467 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x)) := by
  rw [node65_check, Integer.Sparse.eval_merge]
  rw [node64_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node66 : Integer.Sparse (Fin 2886) := [(862, 577936368), (865, 213633648), (879, -577936368), (880, -213633648), (896, 577936368), (899, 213633648), (932, -577936368), (933, -213633648), (971, -1155872736), (974, -427267296), (984, 577936368), (985, 213633648), (1011, 577936368), (1012, 213633648), (2122, 927842256), (2135, -927842256), (2150, 927842256), (2182, -927842256), (2216, -1855684512), (2221, -1924327008), (2225, 927842256), (2229, 1924327008), (2248, 927842256), (2252, 1924327008), (2268, -1924327008), (2354, 1523875248), (2370, -1523875248), (2409, 1523875248), (2444, -1693194720), (2524, -1354555776), (2547, -1523875248), (2596, 3047750496)]

theorem node66_check : node66 =
    Integer.Sparse.merge node63 node65 := by decide +kernel

theorem node66_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node66 x = ((((-6681691 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-1483567 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) + (((-6443349 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((10582467 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x))) := by
  rw [node66_check, Integer.Sparse.eval_merge]
  rw [node63_eval, node65_eval]

def node67 : Integer.Sparse (Fin 2886) := [(2425, -764192688), (2456, 545851920), (2528, 666575856), (2537, -666575856), (2551, 666575856), (2559, 509461792), (2571, -666575856), (2600, -1333151712), (2602, 666575856), (2608, -436681536), (2612, 666575856), (2787, 109170384), (2799, 109170384), (2834, 145560512), (2861, -218340768)]

theorem node67_check : node67 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4628999) entry_3_6) (Integer.Sparse.scale (-2274383) entry_3_7) := by decide +kernel

theorem node67_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node67 x = (((-4628999 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + ((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x) := by
  rw [node67_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node68 : Integer.Sparse (Fin 2886) := [(981, 146170368), (990, -146170368), (1017, -146170368), (1033, 146170368), (2425, -764192688), (2456, 545851920), (2528, 666575856), (2537, -666575856), (2551, 666575856), (2559, 509461792), (2571, -666575856), (2600, -1333151712), (2602, 666575856), (2608, -436681536), (2612, 666575856), (2787, 109170384), (2799, 109170384), (2834, 145560512), (2861, -218340768)]

theorem node68_check : node68 =
    Integer.Sparse.merge (Integer.Sparse.scale (507536) entry_3_5) node67 := by decide +kernel

theorem node68_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node68 x = (((507536 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + (((-4628999 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + ((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x)) := by
  rw [node68_check, Integer.Sparse.eval_merge]
  rw [node67_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node69 : Integer.Sparse (Fin 2886) := [(1803, -676630944), (1832, 676630944), (1909, 676630944), (1982, -676630944), (2525, 512544384), (2536, -512544384), (2548, 512544384), (2570, -512544384), (2597, -1025088768), (2601, 512544384), (2611, 512544384)]

theorem node69_check : node69 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2349413) entry_3_9) (Integer.Sparse.scale (-3559336) entry_3_10) := by decide +kernel

theorem node69_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node69 x = (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((-3559336 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x) := by
  rw [node69_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node70 : Integer.Sparse (Fin 2886) := [(1803, -676630944), (1832, 676630944), (1909, 676630944), (1982, -676630944), (2119, 560146464), (2134, -560146464), (2147, 560146464), (2181, -560146464), (2213, -1120292928), (2224, 560146464), (2247, 560146464), (2525, 512544384), (2536, -512544384), (2548, 512544384), (2570, -512544384), (2597, -1025088768), (2601, 512544384), (2611, 512544384)]

theorem node70_check : node70 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3889906) entry_3_8) node69 := by decide +kernel

theorem node70_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node70 x = (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((-3559336 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x)) := by
  rw [node70_check, Integer.Sparse.eval_merge]
  rw [node69_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node71 : Integer.Sparse (Fin 2886) := [(981, 146170368), (990, -146170368), (1017, -146170368), (1033, 146170368), (1803, -676630944), (1832, 676630944), (1909, 676630944), (1982, -676630944), (2119, 560146464), (2134, -560146464), (2147, 560146464), (2181, -560146464), (2213, -1120292928), (2224, 560146464), (2247, 560146464), (2425, -764192688), (2456, 545851920), (2525, 512544384), (2528, 666575856), (2536, -512544384), (2537, -666575856), (2548, 512544384), (2551, 666575856), (2559, 509461792), (2570, -512544384), (2571, -666575856), (2597, -1025088768), (2600, -1333151712), (2601, 512544384), (2602, 666575856), (2608, -436681536), (2611, 512544384), (2612, 666575856), (2787, 109170384), (2799, 109170384), (2834, 145560512), (2861, -218340768)]

theorem node71_check : node71 =
    Integer.Sparse.merge node68 node70 := by decide +kernel

theorem node71_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node71 x = ((((507536 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + (((-4628999 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + ((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x)) + (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((-3559336 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x))) := by
  rw [node71_check, Integer.Sparse.eval_merge]
  rw [node68_eval, node70_eval]

def node72 : Integer.Sparse (Fin 2886) := [(862, 577936368), (865, 213633648), (879, -577936368), (880, -213633648), (896, 577936368), (899, 213633648), (932, -577936368), (933, -213633648), (971, -1155872736), (974, -427267296), (981, 146170368), (984, 577936368), (985, 213633648), (990, -146170368), (1011, 577936368), (1012, 213633648), (1017, -146170368), (1033, 146170368), (1803, -676630944), (1832, 676630944), (1909, 676630944), (1982, -676630944), (2119, 560146464), (2122, 927842256), (2134, -560146464), (2135, -927842256), (2147, 560146464), (2150, 927842256), (2181, -560146464), (2182, -927842256), (2213, -1120292928), (2216, -1855684512), (2221, -1924327008), (2224, 560146464), (2225, 927842256), (2229, 1924327008), (2247, 560146464), (2248, 927842256), (2252, 1924327008), (2268, -1924327008), (2354, 1523875248), (2370, -1523875248), (2409, 1523875248), (2425, -764192688), (2444, -1693194720), (2456, 545851920), (2524, -1354555776), (2525, 512544384), (2528, 666575856), (2536, -512544384), (2537, -666575856), (2547, -1523875248), (2548, 512544384), (2551, 666575856), (2559, 509461792), (2570, -512544384), (2571, -666575856), (2596, 3047750496), (2597, -1025088768), (2600, -1333151712), (2601, 512544384), (2602, 666575856), (2608, -436681536), (2611, 512544384), (2612, 666575856), (2787, 109170384), (2799, 109170384), (2834, 145560512), (2861, -218340768)]

theorem node72_check : node72 =
    Integer.Sparse.merge node66 node71 := by decide +kernel

theorem node72_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node72 x = (((((-6681691 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-1483567 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) + (((-6443349 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((10582467 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x))) + ((((507536 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + (((-4628999 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + ((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x)) + (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((-3559336 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x)))) := by
  rw [node72_check, Integer.Sparse.eval_merge]
  rw [node66_eval, node71_eval]

def node73 : Integer.Sparse (Fin 2886) := [(1214, -16228800), (1224, 16228800), (1326, -16228800), (1349, 16228800), (1532, 32457600), (1540, -16228800), (1558, -16228800), (2127, 1828131264), (2139, -1828131264), (2155, 1828131264), (2186, -1828131264), (2229, -1828131264), (2252, -1828131264), (2268, 3656262528)]

theorem node73_check : node73 =
    Integer.Sparse.merge (Integer.Sparse.scale (112700) entry_3_11) (Integer.Sparse.scale (12695356) entry_3_12) := by decide +kernel

theorem node73_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node73 x = (((112700 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((12695356 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x) := by
  rw [node73_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node74 : Integer.Sparse (Fin 2886) := [(2371, 2089600848), (2374, 1073287728), (2382, -2089600848), (2383, -1073287728), (2445, 2089600848), (2448, 1073287728), (2468, -2089600848), (2469, -1073287728), (2525, -2089600848), (2528, -1073287728), (2536, 2089600848), (2537, 1073287728), (2548, -2089600848), (2551, -1073287728), (2570, 2089600848), (2571, 1073287728)]

theorem node74_check : node74 =
    Integer.Sparse.merge (Integer.Sparse.scale (-7453387) entry_3_14) (Integer.Sparse.scale (-14511117) entry_3_15) := by decide +kernel

theorem node74_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node74 x = (((-7453387 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-14511117 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x) := by
  rw [node74_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node75 : Integer.Sparse (Fin 2886) := [(2358, 485507664), (2371, 2089600848), (2374, 587780064), (2382, -2089600848), (2383, -1073287728), (2413, 485507664), (2445, 2089600848), (2448, 587780064), (2468, -2089600848), (2469, -1073287728), (2525, -2089600848), (2528, -1558795392), (2536, 2089600848), (2537, 1073287728), (2548, -2089600848), (2551, -1558795392), (2570, 2089600848), (2571, 1073287728), (2600, 971015328)]

theorem node75_check : node75 =
    Integer.Sparse.merge (Integer.Sparse.scale (3371581) entry_3_13) node74 := by decide +kernel

theorem node75_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node75 x = (((3371581 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + (((-7453387 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-14511117 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x)) := by
  rw [node75_check, Integer.Sparse.eval_merge]
  rw [node74_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node76 : Integer.Sparse (Fin 2886) := [(1214, -16228800), (1224, 16228800), (1326, -16228800), (1349, 16228800), (1532, 32457600), (1540, -16228800), (1558, -16228800), (2127, 1828131264), (2139, -1828131264), (2155, 1828131264), (2186, -1828131264), (2229, -1828131264), (2252, -1828131264), (2268, 3656262528), (2358, 485507664), (2371, 2089600848), (2374, 587780064), (2382, -2089600848), (2383, -1073287728), (2413, 485507664), (2445, 2089600848), (2448, 587780064), (2468, -2089600848), (2469, -1073287728), (2525, -2089600848), (2528, -1558795392), (2536, 2089600848), (2537, 1073287728), (2548, -2089600848), (2551, -1558795392), (2570, 2089600848), (2571, 1073287728), (2600, 971015328)]

theorem node76_check : node76 =
    Integer.Sparse.merge node73 node75 := by decide +kernel

theorem node76_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node76 x = ((((112700 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((12695356 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x) + (((3371581 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + (((-7453387 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-14511117 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x))) := by
  rw [node76_check, Integer.Sparse.eval_merge]
  rw [node73_eval, node75_eval]

def node77 : Integer.Sparse (Fin 2886) := [(1808, 221140800), (1822, 54512928), (1837, -110570400), (1838, -110570400), (1852, -54512928), (1914, -110570400), (1917, -110570400), (1930, -54512928), (1983, 110570400), (1984, 110570400), (2006, 54512928)]

theorem node77_check : node77 =
    Integer.Sparse.merge (Integer.Sparse.scale (189281) entry_3_17) (Integer.Sparse.scale (-767850) entry_3_18) := by decide +kernel

theorem node77_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node77 x = (((189281 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x + ((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x) := by
  rw [node77_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node78 : Integer.Sparse (Fin 2886) := [(1808, 221140800), (1822, 54512928), (1837, -110570400), (1838, -110570400), (1852, -54512928), (1914, -110570400), (1917, -110570400), (1930, -54512928), (1983, 110570400), (1984, 110570400), (2006, 54512928), (2533, -21162672), (2541, 21162672), (2556, -21162672), (2575, 21162672), (2606, 21162672), (2616, 21162672), (2625, -42325344)]

theorem node78_check : node78 =
    Integer.Sparse.merge (Integer.Sparse.scale (-146963) entry_3_16) node77 := by decide +kernel

theorem node78_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node78 x = (((-146963 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + (((189281 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x + ((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x)) := by
  rw [node78_check, Integer.Sparse.eval_merge]
  rw [node77_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node79 : Integer.Sparse (Fin 2886) := [(1823, 1318022784), (1853, -1318022784), (1931, -1318022784), (2007, 1318022784), (2788, -2116817856), (2800, 1058408928), (2804, 1058408928), (2835, 1058408928), (2841, 1058408928), (2862, -1058408928), (2864, -1058408928)]

theorem node79_check : node79 =
    Integer.Sparse.merge (Integer.Sparse.scale (4576468) entry_3_20) (Integer.Sparse.scale (7350062) entry_3_21) := by decide +kernel

theorem node79_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node79 x = (((4576468 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x + ((7350062 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_21 x) := by
  rw [node79_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node80 : Integer.Sparse (Fin 2886) := [(1755, 91588896), (1757, -91588896), (1763, -91588896), (1766, 91588896), (1823, 1318022784), (1853, -1318022784), (1931, -1318022784), (2007, 1318022784), (2788, -2116817856), (2800, 1058408928), (2804, 1058408928), (2835, 1058408928), (2841, 1058408928), (2862, -1058408928), (2864, -1058408928)]

theorem node80_check : node80 =
    Integer.Sparse.merge (Integer.Sparse.scale (318017) entry_3_19) node79 := by decide +kernel

theorem node80_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node80 x = (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + (((4576468 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x + ((7350062 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_21 x)) := by
  rw [node80_check, Integer.Sparse.eval_merge]
  rw [node79_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node81 : Integer.Sparse (Fin 2886) := [(1755, 91588896), (1757, -91588896), (1763, -91588896), (1766, 91588896), (1808, 221140800), (1822, 54512928), (1823, 1318022784), (1837, -110570400), (1838, -110570400), (1852, -54512928), (1853, -1318022784), (1914, -110570400), (1917, -110570400), (1930, -54512928), (1931, -1318022784), (1983, 110570400), (1984, 110570400), (2006, 54512928), (2007, 1318022784), (2533, -21162672), (2541, 21162672), (2556, -21162672), (2575, 21162672), (2606, 21162672), (2616, 21162672), (2625, -42325344), (2788, -2116817856), (2800, 1058408928), (2804, 1058408928), (2835, 1058408928), (2841, 1058408928), (2862, -1058408928), (2864, -1058408928)]

theorem node81_check : node81 =
    Integer.Sparse.merge node78 node80 := by decide +kernel

theorem node81_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node81 x = ((((-146963 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + (((189281 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x + ((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x)) + (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + (((4576468 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x + ((7350062 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_21 x))) := by
  rw [node81_check, Integer.Sparse.eval_merge]
  rw [node78_eval, node80_eval]

def node82 : Integer.Sparse (Fin 2886) := [(1214, -16228800), (1224, 16228800), (1326, -16228800), (1349, 16228800), (1532, 32457600), (1540, -16228800), (1558, -16228800), (1755, 91588896), (1757, -91588896), (1763, -91588896), (1766, 91588896), (1808, 221140800), (1822, 54512928), (1823, 1318022784), (1837, -110570400), (1838, -110570400), (1852, -54512928), (1853, -1318022784), (1914, -110570400), (1917, -110570400), (1930, -54512928), (1931, -1318022784), (1983, 110570400), (1984, 110570400), (2006, 54512928), (2007, 1318022784), (2127, 1828131264), (2139, -1828131264), (2155, 1828131264), (2186, -1828131264), (2229, -1828131264), (2252, -1828131264), (2268, 3656262528), (2358, 485507664), (2371, 2089600848), (2374, 587780064), (2382, -2089600848), (2383, -1073287728), (2413, 485507664), (2445, 2089600848), (2448, 587780064), (2468, -2089600848), (2469, -1073287728), (2525, -2089600848), (2528, -1558795392), (2533, -21162672), (2536, 2089600848), (2537, 1073287728), (2541, 21162672), (2548, -2089600848), (2551, -1558795392), (2556, -21162672), (2570, 2089600848), (2571, 1073287728), (2575, 21162672), (2600, 971015328), (2606, 21162672), (2616, 21162672), (2625, -42325344), (2788, -2116817856), (2800, 1058408928), (2804, 1058408928), (2835, 1058408928), (2841, 1058408928), (2862, -1058408928), (2864, -1058408928)]

theorem node82_check : node82 =
    Integer.Sparse.merge node76 node81 := by decide +kernel

theorem node82_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node82 x = (((((112700 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((12695356 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x) + (((3371581 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + (((-7453387 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-14511117 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x))) + ((((-146963 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + (((189281 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x + ((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x)) + (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + (((4576468 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x + ((7350062 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_21 x)))) := by
  rw [node82_check, Integer.Sparse.eval_merge]
  rw [node76_eval, node81_eval]

def node83 : Integer.Sparse (Fin 2886) := [(862, 577936368), (865, 213633648), (879, -577936368), (880, -213633648), (896, 577936368), (899, 213633648), (932, -577936368), (933, -213633648), (971, -1155872736), (974, -427267296), (981, 146170368), (984, 577936368), (985, 213633648), (990, -146170368), (1011, 577936368), (1012, 213633648), (1017, -146170368), (1033, 146170368), (1214, -16228800), (1224, 16228800), (1326, -16228800), (1349, 16228800), (1532, 32457600), (1540, -16228800), (1558, -16228800), (1755, 91588896), (1757, -91588896), (1763, -91588896), (1766, 91588896), (1803, -676630944), (1808, 221140800), (1822, 54512928), (1823, 1318022784), (1832, 676630944), (1837, -110570400), (1838, -110570400), (1852, -54512928), (1853, -1318022784), (1909, 676630944), (1914, -110570400), (1917, -110570400), (1930, -54512928), (1931, -1318022784), (1982, -676630944), (1983, 110570400), (1984, 110570400), (2006, 54512928), (2007, 1318022784), (2119, 560146464), (2122, 927842256), (2127, 1828131264), (2134, -560146464), (2135, -927842256), (2139, -1828131264), (2147, 560146464), (2150, 927842256), (2155, 1828131264), (2181, -560146464), (2182, -927842256), (2186, -1828131264), (2213, -1120292928), (2216, -1855684512), (2221, -1924327008), (2224, 560146464), (2225, 927842256), (2229, 96195744), (2247, 560146464), (2248, 927842256), (2252, 96195744), (2268, 1731935520), (2354, 1523875248), (2358, 485507664), (2370, -1523875248), (2371, 2089600848), (2374, 587780064), (2382, -2089600848), (2383, -1073287728), (2409, 1523875248), (2413, 485507664), (2425, -764192688), (2444, -1693194720), (2445, 2089600848), (2448, 587780064), (2456, 545851920), (2468, -2089600848), (2469, -1073287728), (2524, -1354555776), (2525, -1577056464), (2528, -892219536), (2533, -21162672), (2536, 1577056464), (2537, 406711872), (2541, 21162672), (2547, -1523875248), (2548, -1577056464), (2551, -892219536), (2556, -21162672), (2559, 509461792), (2570, 1577056464), (2571, 406711872), (2575, 21162672), (2596, 3047750496), (2597, -1025088768), (2600, -362136384), (2601, 512544384), (2602, 666575856), (2606, 21162672), (2608, -436681536), (2611, 512544384), (2612, 666575856), (2616, 21162672), (2625, -42325344), (2787, 109170384), (2788, -2116817856), (2799, 109170384), (2800, 1058408928), (2804, 1058408928), (2834, 145560512), (2835, 1058408928), (2841, 1058408928), (2861, -218340768), (2862, -1058408928), (2864, -1058408928)]

theorem node83_check : node83 =
    Integer.Sparse.merge node72 node82 := by decide +kernel

theorem node83_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node83 x = ((((((-6681691 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-1483567 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) + (((-6443349 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((10582467 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x))) + ((((507536 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + (((-4628999 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + ((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x)) + (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((-3559336 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x)))) + (((((112700 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((12695356 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x) + (((3371581 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + (((-7453387 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-14511117 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x))) + ((((-146963 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + (((189281 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x + ((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x)) + (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + (((4576468 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x + ((7350062 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_21 x))))) := by
  rw [node83_check, Integer.Sparse.eval_merge]
  rw [node72_eval, node82_eval]

def node84 : Integer.Sparse (Fin 2886) := [(2, 539093088), (6, -539093088), (77, -539093088), (81, 1078186176), (132, -539093088), (147, -539093088), (162, 539093088), (956, -545546304), (963, 545546304), (1046, 545546304), (1048, -545546304)]

theorem node84_check : node84 =
    Integer.Sparse.merge (Integer.Sparse.scale (1894258) entry_4_0) (Integer.Sparse.scale (3743702) entry_4_1) := by decide +kernel

theorem node84_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node84 x = (((1894258 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((3743702 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) := by
  rw [node84_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node85 : Integer.Sparse (Fin 2886) := [(1, 1152268128), (4, -1152268128), (76, -1152268128), (79, 2304536256), (130, -2048476672), (145, -256059584), (160, 1152268128), (862, 577936368), (879, -577936368), (896, 577936368), (932, -577936368), (971, -1155872736), (984, 577936368), (1011, 577936368)]

theorem node85_check : node85 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4013447) entry_4_3) (Integer.Sparse.scale (8001862) entry_4_4) := by decide +kernel

theorem node85_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node85 x = (((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((8001862 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x) := by
  rw [node85_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node86 : Integer.Sparse (Fin 2886) := [(1, 1152268128), (4, -1152268128), (76, -1152268128), (79, 2304536256), (130, -2048476672), (145, -256059584), (160, 1152268128), (844, 709408800), (850, -709408800), (862, 577936368), (879, -577936368), (896, 577936368), (932, -577936368), (952, -709408800), (958, 1418817600), (971, -1155872736), (984, 577936368), (1011, 577936368), (1029, -709408800), (1092, -709408800), (1109, 709408800)]

theorem node86_check : node86 =
    Integer.Sparse.merge (Integer.Sparse.scale (4926450) entry_4_2) node85 := by decide +kernel

theorem node86_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node86 x = (((4926450 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((8001862 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x)) := by
  rw [node86_check, Integer.Sparse.eval_merge]
  rw [node85_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node87 : Integer.Sparse (Fin 2886) := [(1, 1152268128), (2, 539093088), (4, -1152268128), (6, -539093088), (76, -1152268128), (77, -539093088), (79, 2304536256), (81, 1078186176), (130, -2048476672), (132, -539093088), (145, -256059584), (147, -539093088), (160, 1152268128), (162, 539093088), (844, 709408800), (850, -709408800), (862, 577936368), (879, -577936368), (896, 577936368), (932, -577936368), (952, -709408800), (956, -545546304), (958, 1418817600), (963, 545546304), (971, -1155872736), (984, 577936368), (1011, 577936368), (1029, -709408800), (1046, 545546304), (1048, -545546304), (1092, -709408800), (1109, 709408800)]

theorem node87_check : node87 =
    Integer.Sparse.merge node84 node86 := by decide +kernel

theorem node87_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node87 x = ((((1894258 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((3743702 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) + (((4926450 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((8001862 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x))) := by
  rw [node87_check, Integer.Sparse.eval_merge]
  rw [node84_eval, node86_eval]

def node88 : Integer.Sparse (Fin 2886) := [(898, 498697056), (904, -498697056), (915, -796202784), (925, 796202784), (973, -498697056), (979, 997394112), (988, -498697056), (999, 796202784), (1003, -796202784), (1096, -498697056), (1099, 498697056)]

theorem node88_check : node88 =
    Integer.Sparse.merge (Integer.Sparse.scale (3463174) entry_4_6) (Integer.Sparse.scale (2764593) entry_4_7) := by decide +kernel

theorem node88_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node88 x = (((3463174 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + ((2764593 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x) := by
  rw [node88_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node89 : Integer.Sparse (Fin 2886) := [(84, 618956640), (87, -618956640), (135, -618956640), (139, 618956640), (898, 498697056), (904, -498697056), (915, -796202784), (925, 796202784), (973, -498697056), (979, 997394112), (988, -498697056), (999, 796202784), (1003, -796202784), (1096, -498697056), (1099, 498697056)]

theorem node89_check : node89 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2149155) entry_4_5) node88 := by decide +kernel

theorem node89_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node89 x = (((-2149155 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + (((3463174 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + ((2764593 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x)) := by
  rw [node89_check, Integer.Sparse.eval_merge]
  rw [node88_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node90 : Integer.Sparse (Fin 2886) := [(47, 196849440), (53, -196849440), (108, -196849440), (111, 196849440), (897, 859338864), (901, -859338864), (972, -859338864), (976, 1718677728), (986, -859338864), (1054, -859338864), (1061, 859338864)]

theorem node90_check : node90 =
    Integer.Sparse.merge (Integer.Sparse.scale (-683505) entry_4_9) (Integer.Sparse.scale (5967631) entry_4_10) := by decide +kernel

theorem node90_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node90 x = (((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((5967631 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x) := by
  rw [node90_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node91 : Integer.Sparse (Fin 2886) := [(47, 196849440), (53, -196849440), (108, -196849440), (111, 196849440), (843, 547754976), (847, -547754976), (897, 859338864), (901, -859338864), (951, -547754976), (955, 1095509952), (972, -859338864), (976, 1718677728), (986, -859338864), (1027, -547754976), (1045, -547754976), (1054, -859338864), (1061, 859338864), (1082, 547754976)]

theorem node91_check : node91 =
    Integer.Sparse.merge (Integer.Sparse.scale (3803854) entry_4_8) node90 := by decide +kernel

theorem node91_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node91 x = (((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + (((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((5967631 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x)) := by
  rw [node91_check, Integer.Sparse.eval_merge]
  rw [node90_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node92 : Integer.Sparse (Fin 2886) := [(47, 196849440), (53, -196849440), (84, 618956640), (87, -618956640), (108, -196849440), (111, 196849440), (135, -618956640), (139, 618956640), (843, 547754976), (847, -547754976), (897, 859338864), (898, 498697056), (901, -859338864), (904, -498697056), (915, -796202784), (925, 796202784), (951, -547754976), (955, 1095509952), (972, -859338864), (973, -498697056), (976, 1718677728), (979, 997394112), (986, -859338864), (988, -498697056), (999, 796202784), (1003, -796202784), (1027, -547754976), (1045, -547754976), (1054, -859338864), (1061, 859338864), (1082, 547754976), (1096, -498697056), (1099, 498697056)]

theorem node92_check : node92 =
    Integer.Sparse.merge node89 node91 := by decide +kernel

theorem node92_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node92 x = ((((-2149155 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + (((3463174 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + ((2764593 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x)) + (((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + (((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((5967631 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x))) := by
  rw [node92_check, Integer.Sparse.eval_merge]
  rw [node89_eval, node91_eval]

def node93 : Integer.Sparse (Fin 2886) := [(1, 1152268128), (2, 539093088), (4, -1152268128), (6, -539093088), (47, 196849440), (53, -196849440), (76, -1152268128), (77, -539093088), (79, 2304536256), (81, 1078186176), (84, 618956640), (87, -618956640), (108, -196849440), (111, 196849440), (130, -2048476672), (132, -539093088), (135, -618956640), (139, 618956640), (145, -256059584), (147, -539093088), (160, 1152268128), (162, 539093088), (843, 547754976), (844, 709408800), (847, -547754976), (850, -709408800), (862, 577936368), (879, -577936368), (896, 577936368), (897, 859338864), (898, 498697056), (901, -859338864), (904, -498697056), (915, -796202784), (925, 796202784), (932, -577936368), (951, -547754976), (952, -709408800), (955, 1095509952), (956, -545546304), (958, 1418817600), (963, 545546304), (971, -1155872736), (972, -859338864), (973, -498697056), (976, 1718677728), (979, 997394112), (984, 577936368), (986, -859338864), (988, -498697056), (999, 796202784), (1003, -796202784), (1011, 577936368), (1027, -547754976), (1029, -709408800), (1045, -547754976), (1046, 545546304), (1048, -545546304), (1054, -859338864), (1061, 859338864), (1082, 547754976), (1092, -709408800), (1096, -498697056), (1099, 498697056), (1109, 709408800)]

theorem node93_check : node93 =
    Integer.Sparse.merge node87 node92 := by decide +kernel

theorem node93_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node93 x = (((((1894258 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((3743702 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) + (((4926450 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((8001862 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x))) + ((((-2149155 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + (((3463174 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + ((2764593 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x)) + (((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + (((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((5967631 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x)))) := by
  rw [node93_check, Integer.Sparse.eval_merge]
  rw [node87_eval, node92_eval]

def node94 : Integer.Sparse (Fin 2886) := [(194, 501370992), (197, -501370992), (430, -501370992), (434, 1002741984), (481, -501370992), (540, -501370992), (561, 501370992), (848, 1720488672), (854, -1720488672), (956, 1720488672), (1034, -1720488672), (1046, -3440977344), (1048, 1720488672), (1084, 1720488672)]

theorem node94_check : node94 =
    Integer.Sparse.merge (Integer.Sparse.scale (3481743) entry_4_11) (Integer.Sparse.scale (-11947838) entry_4_12) := by decide +kernel

theorem node94_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node94 x = (((3481743 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x + ((-11947838 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x) := by
  rw [node94_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node95 : Integer.Sparse (Fin 2886) := [(863, 3184727472), (864, 691282800), (866, -3184727472), (869, -691282800), (897, -3184727472), (898, -691282800), (901, 3184727472), (904, 691282800), (986, 3184727472), (988, 691282800), (1013, -3184727472), (1015, -691282800), (1061, -3184727472), (1074, 3184727472), (1099, -691282800), (1106, 691282800)]

theorem node95_check : node95 =
    Integer.Sparse.merge (Integer.Sparse.scale (4800575) entry_4_14) (Integer.Sparse.scale (22116163) entry_4_15) := by decide +kernel

theorem node95_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node95 x = (((4800575 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x + ((22116163 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x) := by
  rw [node95_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block4

end OAI
