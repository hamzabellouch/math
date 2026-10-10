import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Part15

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

def node512 : Integer.Sparse (Fin 2886) := [(2426, 8132425920), (2435, 7320907680), (2457, -7320907680), (2461, -8132425920), (2560, 405759120), (2564, 7320907680), (2609, -7726666800)]

theorem node512_check : node512 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1690663) entry_19_21) (Integer.Sparse.scale (32194445) entry_19_22) := by decide +kernel

theorem node512_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node512 x = (((-1690663 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x + ((32194445 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_22 x) := by
  rw [node512_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node513 : Integer.Sparse (Fin 2886) := [(1758, -2097762480), (1760, 2097762480), (2426, 8132425920), (2435, 7320907680), (2457, -7320907680), (2461, -8132425920), (2560, 405759120), (2564, 7320907680), (2609, -7726666800)]

theorem node513_check : node513 =
    Integer.Sparse.merge (Integer.Sparse.scale (2913559) entry_19_20) node512 := by decide +kernel

theorem node513_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node513 x = (((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x + (((-1690663 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x + ((32194445 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_22 x)) := by
  rw [node513_check, Integer.Sparse.eval_merge]
  rw [node512_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node514 : Integer.Sparse (Fin 2886) := [(1338, 1283548320), (1549, -1283548320), (2177, -1069828800), (2188, -534914400), (2245, 1069828800), (2254, 534914400)]

theorem node514_check : node514 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2228810) entry_19_23) (Integer.Sparse.scale (1782706) entry_19_24) := by decide +kernel

theorem node514_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node514 x = (((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_23 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_24 x) := by
  rw [node514_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node515 : Integer.Sparse (Fin 2886) := [(1344, -148502880), (1355, 148502880), (1557, -148502880), (1564, 148502880), (2825, 1390038480), (2827, -1390038480)]

theorem node515_check : node515 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1930609) entry_19_25) (Integer.Sparse.scale (618762) entry_19_26) := by decide +kernel

theorem node515_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node515 x = (((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_25 x + ((618762 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_26 x) := by
  rw [node515_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node516 : Integer.Sparse (Fin 2886) := [(1338, 1283548320), (1344, -148502880), (1355, 148502880), (1549, -1283548320), (1557, -148502880), (1564, 148502880), (2177, -1069828800), (2188, -534914400), (2245, 1069828800), (2254, 534914400), (2825, 1390038480), (2827, -1390038480)]

theorem node516_check : node516 =
    Integer.Sparse.merge node514 node515 := by decide +kernel

theorem node516_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node516 x = ((((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_23 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_24 x) + (((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_25 x + ((618762 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_26 x)) := by
  rw [node516_check, Integer.Sparse.eval_merge]
  rw [node514_eval, node515_eval]

def node517 : Integer.Sparse (Fin 2886) := [(1338, 1283548320), (1344, -148502880), (1355, 148502880), (1549, -1283548320), (1557, -148502880), (1564, 148502880), (1758, -2097762480), (1760, 2097762480), (2177, -1069828800), (2188, -534914400), (2245, 1069828800), (2254, 534914400), (2426, 8132425920), (2435, 7320907680), (2457, -7320907680), (2461, -8132425920), (2560, 405759120), (2564, 7320907680), (2609, -7726666800), (2825, 1390038480), (2827, -1390038480)]

theorem node517_check : node517 =
    Integer.Sparse.merge node513 node516 := by decide +kernel

theorem node517_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node517 x = ((((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x + (((-1690663 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x + ((32194445 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_22 x)) + ((((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_23 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_24 x) + (((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_25 x + ((618762 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_26 x))) := by
  rw [node517_check, Integer.Sparse.eval_merge]
  rw [node513_eval, node516_eval]

def node518 : Integer.Sparse (Fin 2886) := [(918, 720293760), (923, -216511920), (940, 216511920), (1004, -720293760), (1009, -216511920), (1019, 216511920), (1338, 1283548320), (1344, -148502880), (1355, 148502880), (1549, -1283548320), (1557, -148502880), (1564, 148502880), (1758, -2097762480), (1760, 2097762480), (1975, 862133520), (1976, 1724267040), (2071, -862133520), (2072, -1724267040), (2163, -6006663120), (2172, -12013326240), (2177, -1069828800), (2188, -534914400), (2236, 6006663120), (2240, 12013326240), (2245, 1069828800), (2254, 534914400), (2425, 456104160), (2426, 8132425920), (2435, 7320907680), (2440, -6515904000), (2456, 2280520800), (2457, -7320907680), (2461, -8132425920), (2466, 6515904000), (2559, -1672381920), (2560, 405759120), (2564, 7320907680), (2577, -3257952000), (2609, -7726666800), (2618, 3257952000), (2787, -456104160), (2819, 10071274080), (2824, 10071274080), (2825, 1390038480), (2827, -1390038480), (2834, -608138880), (2839, -20142548160)]

theorem node518_check : node518 =
    Integer.Sparse.merge node511 node517 := by decide +kernel

theorem node518_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node518 x = (((((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + (((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-25027763 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x)) + ((((3167390 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + ((-13574800 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x) + (((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x + ((41963642 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x))) + ((((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x + (((-1690663 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x + ((32194445 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_22 x)) + ((((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_23 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_24 x) + (((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_25 x + ((618762 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_26 x)))) := by
  rw [node518_check, Integer.Sparse.eval_merge]
  rw [node511_eval, node517_eval]

def node519 : Integer.Sparse (Fin 2886) := [(914, -1697683680), (918, 686634000), (923, -216511920), (926, -67319520), (940, 216511920), (997, 1697683680), (1002, 33659760), (1004, -652974240), (1009, -216511920), (1019, 216511920), (1251, 4551535680), (1254, -253890240), (1258, -253890240), (1273, -4551535680), (1278, 253890240), (1279, 253890240), (1338, 1283548320), (1344, -148502880), (1355, 148502880), (1414, 2275767840), (1418, -253890240), (1454, -2275767840), (1455, 253890240), (1549, -1283548320), (1557, -148502880), (1564, 148502880), (1758, -2097762480), (1760, 2097762480), (1975, 862133520), (1976, 1724267040), (2071, -862133520), (2072, -1724267040), (2162, -4213756080), (2163, -10308372240), (2166, -437162640), (2170, -1140278160), (2172, -12013326240), (2173, -230946240), (2177, -1069828800), (2188, 605363760), (2235, 3160317060), (2236, 6006663120), (2239, 115473120), (2240, 16315035360), (2241, 552635760), (2245, -70449360), (2254, 1675192560), (2425, 6770321280), (2426, 8132425920), (2429, 1681454400), (2435, 7320907680), (2436, -3001969440), (2440, -6515904000), (2456, -5612250600), (2457, -7320907680), (2460, 3093205920), (2461, -8132425920), (2462, -1498981440), (2466, 6515904000), (2559, 1484726640), (2560, 405759120), (2563, 2250475440), (2564, 7320907680), (2565, -3184442400), (2577, -3257952000), (2608, -3157108560), (2609, -7726666800), (2610, 660257520), (2618, 3257952000), (2787, 3753373920), (2799, -2630923800), (2819, 10071274080), (2824, 10071274080), (2825, 1390038480), (2827, -1390038480), (2834, 1496600160), (2839, -20142548160), (2857, 1053439020), (2861, -2104739040)]

theorem node519_check : node519 =
    Integer.Sparse.merge node505 node518 := by decide +kernel

theorem node519_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node519 x = ((((((4751159 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + (((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x)) + (((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + (((-481138 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x + ((-2751073 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x))) + ((((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + (((380152 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x + ((-1057876 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x)) + ((((-9757133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((9482366 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x) + (((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((446791 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x)))) + (((((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + (((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-25027763 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x)) + ((((3167390 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + ((-13574800 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x) + (((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x + ((41963642 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x))) + ((((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x + (((-1690663 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x + ((32194445 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_22 x)) + ((((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_23 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_24 x) + (((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_25 x + ((618762 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_26 x))))) := by
  rw [node519_check, Integer.Sparse.eval_merge]
  rw [node505_eval, node518_eval]

def node520 : Integer.Sparse (Fin 2886) := [(540, -328612320), (561, 328612320), (600, 184731120), (606, -184731120)]

theorem node520_check : node520 =
    Integer.Sparse.merge (Integer.Sparse.scale (-256571) entry_20_1) (Integer.Sparse.scale (456406) entry_20_2) := by decide +kernel

theorem node520_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node520 x = (((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x + ((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x) := by
  rw [node520_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node521 : Integer.Sparse (Fin 2886) := [(540, -328612320), (561, 328612320), (600, 184731120), (606, -184731120), (1657, 51094800), (1661, -51094800)]

theorem node521_check : node521 =
    Integer.Sparse.merge (Integer.Sparse.scale (70965) entry_20_0) node520 := by decide +kernel

theorem node521_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node521 x = (((70965 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_0 x + (((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x + ((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x)) := by
  rw [node521_check, Integer.Sparse.eval_merge]
  rw [node520_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node522 : Integer.Sparse (Fin 2886) := [(1658, -492868080), (1667, 245944080), (1673, -245944080), (1689, 492868080)]

theorem node522_check : node522 =
    Integer.Sparse.merge (Integer.Sparse.scale (684539) entry_20_4) (Integer.Sparse.scale (-341589) entry_20_5) := by decide +kernel

theorem node522_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node522 x = (((684539 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x + ((-341589 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x) := by
  rw [node522_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node523 : Integer.Sparse (Fin 2886) := [(1658, -492868080), (1667, 245944080), (1673, -245944080), (1689, 492868080), (1754, -1639162080), (1756, 1639162080)]

theorem node523_check : node523 =
    Integer.Sparse.merge (Integer.Sparse.scale (2276614) entry_20_3) node522 := by decide +kernel

theorem node523_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node523 x = (((2276614 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + (((684539 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x + ((-341589 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x)) := by
  rw [node523_check, Integer.Sparse.eval_merge]
  rw [node522_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node524 : Integer.Sparse (Fin 2886) := [(540, -328612320), (561, 328612320), (600, 184731120), (606, -184731120), (1657, 51094800), (1658, -492868080), (1661, -51094800), (1667, 245944080), (1673, -245944080), (1689, 492868080), (1754, -1639162080), (1756, 1639162080)]

theorem node524_check : node524 =
    Integer.Sparse.merge node521 node523 := by decide +kernel

theorem node524_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node524 x = ((((70965 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_0 x + (((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x + ((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x)) + (((2276614 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + (((684539 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x + ((-341589 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x))) := by
  rw [node524_check, Integer.Sparse.eval_merge]
  rw [node521_eval, node523_eval]

def node525 : Integer.Sparse (Fin 2886) := [(548, 60441840), (550, -60441840), (1673, 185585760), (1683, -185585760)]

theorem node525_check : node525 =
    Integer.Sparse.merge (Integer.Sparse.scale (-257758) entry_20_7) (Integer.Sparse.scale (-83947) entry_20_8) := by decide +kernel

theorem node525_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node525 x = (((-257758 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x + ((-83947 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x) := by
  rw [node525_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node526 : Integer.Sparse (Fin 2886) := [(548, 60441840), (550, -60441840), (1673, 185585760), (1683, -185585760), (1753, 273776400), (1765, -273776400)]

theorem node526_check : node526 =
    Integer.Sparse.merge (Integer.Sparse.scale (-380245) entry_20_6) node525 := by decide +kernel

theorem node526_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node526 x = (((-380245 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x + (((-257758 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x + ((-83947 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x)) := by
  rw [node526_check, Integer.Sparse.eval_merge]
  rw [node525_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node527 : Integer.Sparse (Fin 2886) := [(601, 23035680), (602, -23035680), (1665, -219127680), (1667, 219127680)]

theorem node527_check : node527 =
    Integer.Sparse.merge (Integer.Sparse.scale (-304344) entry_20_9) (Integer.Sparse.scale (-31994) entry_20_10) := by decide +kernel

theorem node527_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node527 x = (((-304344 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x + ((-31994 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x) := by
  rw [node527_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node528 : Integer.Sparse (Fin 2886) := [(1656, 341975520), (1689, -341975520), (1729, 1135280880), (1749, -1135280880)]

theorem node528_check : node528 =
    Integer.Sparse.merge (Integer.Sparse.scale (1576779) entry_20_11) (Integer.Sparse.scale (474966) entry_20_12) := by decide +kernel

theorem node528_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node528 x = (((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x + ((474966 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x) := by
  rw [node528_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node529 : Integer.Sparse (Fin 2886) := [(601, 23035680), (602, -23035680), (1656, 341975520), (1665, -219127680), (1667, 219127680), (1689, -341975520), (1729, 1135280880), (1749, -1135280880)]

theorem node529_check : node529 =
    Integer.Sparse.merge node527 node528 := by decide +kernel

theorem node529_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node529 x = ((((-304344 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x + ((-31994 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x) + (((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x + ((474966 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x)) := by
  rw [node529_check, Integer.Sparse.eval_merge]
  rw [node527_eval, node528_eval]

def node530 : Integer.Sparse (Fin 2886) := [(548, 60441840), (550, -60441840), (601, 23035680), (602, -23035680), (1656, 341975520), (1665, -219127680), (1667, 219127680), (1673, 185585760), (1683, -185585760), (1689, -341975520), (1729, 1135280880), (1749, -1135280880), (1753, 273776400), (1765, -273776400)]

theorem node530_check : node530 =
    Integer.Sparse.merge node526 node529 := by decide +kernel

theorem node530_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node530 x = ((((-380245 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x + (((-257758 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x + ((-83947 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x)) + ((((-304344 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x + ((-31994 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x) + (((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x + ((474966 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x))) := by
  rw [node530_check, Integer.Sparse.eval_merge]
  rw [node526_eval, node529_eval]

def node531 : Integer.Sparse (Fin 2886) := [(540, -328612320), (548, 60441840), (550, -60441840), (561, 328612320), (600, 184731120), (601, 23035680), (602, -23035680), (606, -184731120), (1656, 341975520), (1657, 51094800), (1658, -492868080), (1661, -51094800), (1665, -219127680), (1667, 465071760), (1673, -60358320), (1683, -185585760), (1689, 150892560), (1729, 1135280880), (1749, -1135280880), (1753, 273776400), (1754, -1639162080), (1756, 1639162080), (1765, -273776400)]

theorem node531_check : node531 =
    Integer.Sparse.merge node524 node530 := by decide +kernel

theorem node531_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node531 x = (((((70965 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_0 x + (((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x + ((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x)) + (((2276614 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + (((684539 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x + ((-341589 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x))) + ((((-380245 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x + (((-257758 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x + ((-83947 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x)) + ((((-304344 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x + ((-31994 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x) + (((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x + ((474966 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x)))) := by
  rw [node531_check, Integer.Sparse.eval_merge]
  rw [node524_eval, node530_eval]

def node532 : Integer.Sparse (Fin 2886) := [(538, 282892320), (561, -282892320), (1730, 442335600), (1749, -442335600)]

theorem node532_check : node532 =
    Integer.Sparse.merge (Integer.Sparse.scale (392906) entry_20_14) (Integer.Sparse.scale (-614355) entry_20_15) := by decide +kernel

theorem node532_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node532 x = (((392906 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x + ((-614355 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x) := by
  rw [node532_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node533 : Integer.Sparse (Fin 2886) := [(315, -427308480), (319, 427308480), (538, 282892320), (561, -282892320), (1730, 442335600), (1749, -442335600)]

theorem node533_check : node533 =
    Integer.Sparse.merge (Integer.Sparse.scale (593484) entry_20_13) node532 := by decide +kernel

theorem node533_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node533 x = (((593484 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_13 x + (((392906 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x + ((-614355 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x)) := by
  rw [node533_check, Integer.Sparse.eval_merge]
  rw [node532_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node534 : Integer.Sparse (Fin 2886) := [(1670, -141531840), (1675, 141531840), (1756, -823439520), (1762, 823439520)]

theorem node534_check : node534 =
    Integer.Sparse.merge (Integer.Sparse.scale (1143666) entry_20_16) (Integer.Sparse.scale (196572) entry_20_17) := by decide +kernel

theorem node534_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node534 x = (((1143666 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + ((196572 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x) := by
  rw [node534_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node535 : Integer.Sparse (Fin 2886) := [(539, 567596880), (543, -567596880), (1758, -2097762480), (1760, 2097762480)]

theorem node535_check : node535 =
    Integer.Sparse.merge (Integer.Sparse.scale (788329) entry_20_18) (Integer.Sparse.scale (2913559) entry_20_19) := by decide +kernel

theorem node535_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node535 x = (((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x + ((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x) := by
  rw [node535_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node536 : Integer.Sparse (Fin 2886) := [(539, 567596880), (543, -567596880), (1670, -141531840), (1675, 141531840), (1756, -823439520), (1758, -2097762480), (1760, 2097762480), (1762, 823439520)]

theorem node536_check : node536 =
    Integer.Sparse.merge node534 node535 := by decide +kernel

theorem node536_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node536 x = ((((1143666 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + ((196572 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x) + (((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x + ((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x)) := by
  rw [node536_check, Integer.Sparse.eval_merge]
  rw [node534_eval, node535_eval]

def node537 : Integer.Sparse (Fin 2886) := [(315, -427308480), (319, 427308480), (538, 282892320), (539, 567596880), (543, -567596880), (561, -282892320), (1670, -141531840), (1675, 141531840), (1730, 442335600), (1749, -442335600), (1756, -823439520), (1758, -2097762480), (1760, 2097762480), (1762, 823439520)]

theorem node537_check : node537 =
    Integer.Sparse.merge node533 node536 := by decide +kernel

theorem node537_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node537 x = ((((593484 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_13 x + (((392906 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x + ((-614355 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x)) + ((((1143666 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + ((196572 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x) + (((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x + ((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x))) := by
  rw [node537_check, Integer.Sparse.eval_merge]
  rw [node533_eval, node536_eval]

def node538 : Integer.Sparse (Fin 2886) := [(1733, 686943360), (1734, -1595039760), (1737, 908096400)]

theorem node538_check : node538 =
    Integer.Sparse.merge (Integer.Sparse.scale (954088) entry_20_21) (Integer.Sparse.scale (1261245) entry_20_22) := by decide +kernel

theorem node538_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node538 x = (((954088 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_21 x + ((1261245 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_22 x) := by
  rw [node538_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node539 : Integer.Sparse (Fin 2886) := [(249, 673745040), (250, -673745040), (1733, 686943360), (1734, -1595039760), (1737, 908096400)]

theorem node539_check : node539 =
    Integer.Sparse.merge (Integer.Sparse.scale (935757) entry_20_20) node538 := by decide +kernel

theorem node539_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node539 x = (((935757 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x + (((954088 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_21 x + ((1261245 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_22 x)) := by
  rw [node539_check, Integer.Sparse.eval_merge]
  rw [node538_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node540 : Integer.Sparse (Fin 2886) := [(585, -168154560), (595, 168154560), (1661, -661515840), (1691, 661515840)]

theorem node540_check : node540 =
    Integer.Sparse.merge (Integer.Sparse.scale (918772) entry_20_23) (Integer.Sparse.scale (233548) entry_20_24) := by decide +kernel

theorem node540_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node540 x = (((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_23 x + ((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_24 x) := by
  rw [node540_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node541 : Integer.Sparse (Fin 2886) := [(448, -308329920), (453, 308329920), (1740, 1185227280), (1741, -1185227280)]

theorem node541_check : node541 =
    Integer.Sparse.merge (Integer.Sparse.scale (1646149) entry_20_25) (Integer.Sparse.scale (-428236) entry_20_26) := by decide +kernel

theorem node541_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node541 x = (((1646149 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_25 x + ((-428236 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_26 x) := by
  rw [node541_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node542 : Integer.Sparse (Fin 2886) := [(448, -308329920), (453, 308329920), (585, -168154560), (595, 168154560), (1661, -661515840), (1691, 661515840), (1740, 1185227280), (1741, -1185227280)]

theorem node542_check : node542 =
    Integer.Sparse.merge node540 node541 := by decide +kernel

theorem node542_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node542 x = ((((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_23 x + ((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_24 x) + (((1646149 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_25 x + ((-428236 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_26 x)) := by
  rw [node542_check, Integer.Sparse.eval_merge]
  rw [node540_eval, node541_eval]

def node543 : Integer.Sparse (Fin 2886) := [(249, 673745040), (250, -673745040), (448, -308329920), (453, 308329920), (585, -168154560), (595, 168154560), (1661, -661515840), (1691, 661515840), (1733, 686943360), (1734, -1595039760), (1737, 908096400), (1740, 1185227280), (1741, -1185227280)]

theorem node543_check : node543 =
    Integer.Sparse.merge node539 node542 := by decide +kernel

theorem node543_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node543 x = ((((935757 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x + (((954088 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_21 x + ((1261245 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_22 x)) + ((((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_23 x + ((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_24 x) + (((1646149 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_25 x + ((-428236 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_26 x))) := by
  rw [node543_check, Integer.Sparse.eval_merge]
  rw [node539_eval, node542_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
