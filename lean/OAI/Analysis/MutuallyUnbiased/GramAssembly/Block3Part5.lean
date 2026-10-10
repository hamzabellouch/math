import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Part4

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

def node160 : Integer.Sparse (Fin 2886) := [(840, -406750320), (845, -725058720), (948, 406750320), (953, 725058720), (2105, 588288960), (2118, -228670344), (2146, -2058033096), (2200, -588288960), (2205, 1190262240), (2212, 1524468960), (2266, -1190262240), (2331, 228670344), (2508, -228670344), (2512, -442600560), (2584, 762234480), (2588, 442600560)]

theorem node160_check : node160 =
    Integer.Sparse.merge node157 node159 := by decide +kernel

theorem node160_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node160 x = ((((-1653142 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + (((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x)) + (((-3175977 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + (((817068 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((-614723 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x))) := by
  rw [node160_check, Integer.Sparse.eval_merge]
  rw [node157_eval, node159_eval]

def node161 : Integer.Sparse (Fin 2886) := [(1364, 2163503520), (1437, -2163503520), (2334, -1129870080), (2512, 1129870080)]

theorem node161_check : node161 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1569264) entry_6_7) (Integer.Sparse.scale (3004866) entry_6_8) := by decide +kernel

theorem node161_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node161 x = (((-1569264 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((3004866 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x) := by
  rw [node161_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node162 : Integer.Sparse (Fin 2886) := [(1364, 2163503520), (1437, -2163503520), (2101, 2506006080), (2196, -2506006080), (2334, -1129870080), (2512, 1129870080)]

theorem node162_check : node162 =
    Integer.Sparse.merge (Integer.Sparse.scale (3480564) entry_6_6) node161 := by decide +kernel

theorem node162_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node162 x = (((3480564 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + (((-1569264 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((3004866 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x)) := by
  rw [node162_check, Integer.Sparse.eval_merge]
  rw [node161_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node163 : Integer.Sparse (Fin 2886) := [(1359, -1407186000), (1432, 1407186000), (2588, -1324720080), (2620, 1324720080)]

theorem node163_check : node163 =
    Integer.Sparse.merge (Integer.Sparse.scale (1839889) entry_6_9) (Integer.Sparse.scale (-1954425) entry_6_10) := by decide +kernel

theorem node163_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node163 x = (((1839889 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((-1954425 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x) := by
  rw [node163_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node164 : Integer.Sparse (Fin 2886) := [(2102, 2219898240), (2105, 274836240), (2261, -2219898240), (2262, -274836240)]

theorem node164_check : node164 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3083192) entry_6_11) (Integer.Sparse.scale (-381717) entry_6_12) := by decide +kernel

theorem node164_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node164 x = (((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x + ((-381717 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x) := by
  rw [node164_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node165 : Integer.Sparse (Fin 2886) := [(1359, -1407186000), (1432, 1407186000), (2102, 2219898240), (2105, 274836240), (2261, -2219898240), (2262, -274836240), (2588, -1324720080), (2620, 1324720080)]

theorem node165_check : node165 =
    Integer.Sparse.merge node163 node164 := by decide +kernel

theorem node165_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node165 x = ((((1839889 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((-1954425 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x) + (((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x + ((-381717 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x)) := by
  rw [node165_check, Integer.Sparse.eval_merge]
  rw [node163_eval, node164_eval]

def node166 : Integer.Sparse (Fin 2886) := [(1359, -1407186000), (1364, 2163503520), (1432, 1407186000), (1437, -2163503520), (2101, 2506006080), (2102, 2219898240), (2105, 274836240), (2196, -2506006080), (2261, -2219898240), (2262, -274836240), (2334, -1129870080), (2512, 1129870080), (2588, -1324720080), (2620, 1324720080)]

theorem node166_check : node166 =
    Integer.Sparse.merge node162 node165 := by decide +kernel

theorem node166_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node166 x = ((((3480564 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + (((-1569264 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((3004866 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x)) + ((((1839889 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((-1954425 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x) + (((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x + ((-381717 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x))) := by
  rw [node166_check, Integer.Sparse.eval_merge]
  rw [node162_eval, node165_eval]

def node167 : Integer.Sparse (Fin 2886) := [(840, -406750320), (845, -725058720), (948, 406750320), (953, 725058720), (1359, -1407186000), (1364, 2163503520), (1432, 1407186000), (1437, -2163503520), (2101, 2506006080), (2102, 2219898240), (2105, 863125200), (2118, -228670344), (2146, -2058033096), (2196, -2506006080), (2200, -588288960), (2205, 1190262240), (2212, 1524468960), (2261, -2219898240), (2262, -274836240), (2266, -1190262240), (2331, 228670344), (2334, -1129870080), (2508, -228670344), (2512, 687269520), (2584, 762234480), (2588, -882119520), (2620, 1324720080)]

theorem node167_check : node167 =
    Integer.Sparse.merge node160 node166 := by decide +kernel

theorem node167_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node167 x = (((((-1653142 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + (((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x)) + (((-3175977 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + (((817068 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((-614723 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x))) + ((((3480564 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + (((-1569264 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((3004866 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x)) + ((((1839889 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((-1954425 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x) + (((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x + ((-381717 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x)))) := by
  rw [node167_check, Integer.Sparse.eval_merge]
  rw [node160_eval, node166_eval]

def node168 : Integer.Sparse (Fin 2886) := [(845, -394678800), (1026, 394678800), (2102, 5729666400), (2197, -5729666400)]

theorem node168_check : node168 =
    Integer.Sparse.merge (Integer.Sparse.scale (548165) entry_6_14) (Integer.Sparse.scale (7957870) entry_6_15) := by decide +kernel

theorem node168_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node168 x = (((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x + ((7957870 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x) := by
  rw [node168_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node169 : Integer.Sparse (Fin 2886) := [(845, -394678800), (1026, 394678800), (1802, -560113920), (2068, 560113920), (2102, 5729666400), (2197, -5729666400)]

theorem node169_check : node169 =
    Integer.Sparse.merge (Integer.Sparse.scale (-777936) entry_6_13) node168 := by decide +kernel

theorem node169_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node169 x = (((-777936 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + (((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x + ((7957870 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x)) := by
  rw [node169_check, Integer.Sparse.eval_merge]
  rw [node168_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node170 : Integer.Sparse (Fin 2886) := [(2118, 772399872), (2146, -772399872), (2331, 193099968), (2508, -193099968), (2517, 1180402560), (2593, -1180402560)]

theorem node170_check : node170 =
    Integer.Sparse.merge (Integer.Sparse.scale (1340972) entry_6_16) (Integer.Sparse.scale (1639448) entry_6_17) := by decide +kernel

theorem node170_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node170 x = (((1340972 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + ((1639448 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x) := by
  rw [node170_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node171 : Integer.Sparse (Fin 2886) := [(960, 826673040), (1031, -826673040), (2162, -4213756080), (2235, 3160317060), (2857, 1053439020)]

theorem node171_check : node171 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1148157) entry_6_18) (Integer.Sparse.scale (-5852439) entry_6_19) := by decide +kernel

theorem node171_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node171 x = (((-1148157 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x + ((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x) := by
  rw [node171_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node172 : Integer.Sparse (Fin 2886) := [(960, 826673040), (1031, -826673040), (2118, 772399872), (2146, -772399872), (2162, -4213756080), (2235, 3160317060), (2331, 193099968), (2508, -193099968), (2517, 1180402560), (2593, -1180402560), (2857, 1053439020)]

theorem node172_check : node172 =
    Integer.Sparse.merge node170 node171 := by decide +kernel

theorem node172_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node172 x = ((((1340972 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + ((1639448 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x) + (((-1148157 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x + ((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x)) := by
  rw [node172_check, Integer.Sparse.eval_merge]
  rw [node170_eval, node171_eval]

def node173 : Integer.Sparse (Fin 2886) := [(845, -394678800), (960, 826673040), (1026, 394678800), (1031, -826673040), (1802, -560113920), (2068, 560113920), (2102, 5729666400), (2118, 772399872), (2146, -772399872), (2162, -4213756080), (2197, -5729666400), (2235, 3160317060), (2331, 193099968), (2508, -193099968), (2517, 1180402560), (2593, -1180402560), (2857, 1053439020)]

theorem node173_check : node173 =
    Integer.Sparse.merge node169 node172 := by decide +kernel

theorem node173_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node173 x = ((((-777936 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + (((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x + ((7957870 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x)) + ((((1340972 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + ((1639448 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x) + (((-1148157 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x + ((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x))) := by
  rw [node173_check, Integer.Sparse.eval_merge]
  rw [node169_eval, node172_eval]

def node174 : Integer.Sparse (Fin 2886) := [(2509, -7498457280), (2585, 4938860160), (2619, 2559597120)]

theorem node174_check : node174 =
    Integer.Sparse.merge (Integer.Sparse.scale (3554996) entry_6_21) (Integer.Sparse.scale (-10414524) entry_6_22) := by decide +kernel

theorem node174_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node174 x = (((3554996 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_21 x + ((-10414524 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_22 x) := by
  rw [node174_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node175 : Integer.Sparse (Fin 2886) := [(1753, 273776400), (1765, -273776400), (2509, -7498457280), (2585, 4938860160), (2619, 2559597120)]

theorem node175_check : node175 =
    Integer.Sparse.merge (Integer.Sparse.scale (-380245) entry_6_20) node174 := by decide +kernel

theorem node175_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node175 x = (((-380245 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x + (((3554996 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_21 x + ((-10414524 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_22 x)) := by
  rw [node175_check, Integer.Sparse.eval_merge]
  rw [node174_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node176 : Integer.Sparse (Fin 2886) := [(1132, -336582000), (1515, 336582000), (2110, 2112371280), (2205, -2112371280)]

theorem node176_check : node176 =
    Integer.Sparse.merge (Integer.Sparse.scale (2933849) entry_6_23) (Integer.Sparse.scale (-467475) entry_6_24) := by decide +kernel

theorem node176_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node176 x = (((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_23 x + ((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_24 x) := by
  rw [node176_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node177 : Integer.Sparse (Fin 2886) := [(1525, 743539680), (1572, -743539680), (2858, 1420727760), (2866, -1420727760)]

theorem node177_check : node177 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1973233) entry_6_25) (Integer.Sparse.scale (-1032694) entry_6_26) := by decide +kernel

theorem node177_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node177 x = (((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_25 x + ((-1032694 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_26 x) := by
  rw [node177_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node178 : Integer.Sparse (Fin 2886) := [(1132, -336582000), (1515, 336582000), (1525, 743539680), (1572, -743539680), (2110, 2112371280), (2205, -2112371280), (2858, 1420727760), (2866, -1420727760)]

theorem node178_check : node178 =
    Integer.Sparse.merge node176 node177 := by decide +kernel

theorem node178_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node178 x = ((((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_23 x + ((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_24 x) + (((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_25 x + ((-1032694 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_26 x)) := by
  rw [node178_check, Integer.Sparse.eval_merge]
  rw [node176_eval, node177_eval]

def node179 : Integer.Sparse (Fin 2886) := [(1132, -336582000), (1515, 336582000), (1525, 743539680), (1572, -743539680), (1753, 273776400), (1765, -273776400), (2110, 2112371280), (2205, -2112371280), (2509, -7498457280), (2585, 4938860160), (2619, 2559597120), (2858, 1420727760), (2866, -1420727760)]

theorem node179_check : node179 =
    Integer.Sparse.merge node175 node178 := by decide +kernel

theorem node179_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node179 x = ((((-380245 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x + (((3554996 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_21 x + ((-10414524 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_22 x)) + ((((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_23 x + ((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_24 x) + (((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_25 x + ((-1032694 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_26 x))) := by
  rw [node179_check, Integer.Sparse.eval_merge]
  rw [node175_eval, node178_eval]

def node180 : Integer.Sparse (Fin 2886) := [(845, -394678800), (960, 826673040), (1026, 394678800), (1031, -826673040), (1132, -336582000), (1515, 336582000), (1525, 743539680), (1572, -743539680), (1753, 273776400), (1765, -273776400), (1802, -560113920), (2068, 560113920), (2102, 5729666400), (2110, 2112371280), (2118, 772399872), (2146, -772399872), (2162, -4213756080), (2197, -5729666400), (2205, -2112371280), (2235, 3160317060), (2331, 193099968), (2508, -193099968), (2509, -7498457280), (2517, 1180402560), (2585, 4938860160), (2593, -1180402560), (2619, 2559597120), (2857, 1053439020), (2858, 1420727760), (2866, -1420727760)]

theorem node180_check : node180 =
    Integer.Sparse.merge node173 node179 := by decide +kernel

theorem node180_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node180 x = (((((-777936 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + (((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x + ((7957870 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x)) + ((((1340972 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + ((1639448 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x) + (((-1148157 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x + ((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x))) + ((((-380245 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x + (((3554996 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_21 x + ((-10414524 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_22 x)) + ((((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_23 x + ((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_24 x) + (((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_25 x + ((-1032694 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_26 x)))) := by
  rw [node180_check, Integer.Sparse.eval_merge]
  rw [node173_eval, node179_eval]

def node181 : Integer.Sparse (Fin 2886) := [(840, -406750320), (845, -1119737520), (948, 406750320), (953, 725058720), (960, 826673040), (1026, 394678800), (1031, -826673040), (1132, -336582000), (1359, -1407186000), (1364, 2163503520), (1432, 1407186000), (1437, -2163503520), (1515, 336582000), (1525, 743539680), (1572, -743539680), (1753, 273776400), (1765, -273776400), (1802, -560113920), (2068, 560113920), (2101, 2506006080), (2102, 7949564640), (2105, 863125200), (2110, 2112371280), (2118, 543729528), (2146, -2830432968), (2162, -4213756080), (2196, -2506006080), (2197, -5729666400), (2200, -588288960), (2205, -922109040), (2212, 1524468960), (2235, 3160317060), (2261, -2219898240), (2262, -274836240), (2266, -1190262240), (2331, 421770312), (2334, -1129870080), (2508, -421770312), (2509, -7498457280), (2512, 687269520), (2517, 1180402560), (2584, 762234480), (2585, 4938860160), (2588, -882119520), (2593, -1180402560), (2619, 2559597120), (2620, 1324720080), (2857, 1053439020), (2858, 1420727760), (2866, -1420727760)]

theorem node181_check : node181 =
    Integer.Sparse.merge node167 node180 := by decide +kernel

theorem node181_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node181 x = ((((((-1653142 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + (((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x)) + (((-3175977 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + (((817068 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((-614723 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x))) + ((((3480564 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + (((-1569264 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((3004866 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x)) + ((((1839889 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((-1954425 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x) + (((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x + ((-381717 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x)))) + (((((-777936 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + (((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x + ((7957870 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x)) + ((((1340972 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + ((1639448 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x) + (((-1148157 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x + ((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x))) + ((((-380245 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x + (((3554996 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_21 x + ((-10414524 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_22 x)) + ((((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_23 x + ((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_24 x) + (((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_25 x + ((-1032694 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_26 x))))) := by
  rw [node181_check, Integer.Sparse.eval_merge]
  rw [node167_eval, node180_eval]

def node182 : Integer.Sparse (Fin 2886) := [(861, -25456320), (863, 167748864), (870, 335497728), (884, 125811648), (895, 25456320), (897, -167748864), (905, -335497728), (937, -125811648), (989, -83874432), (1016, 83874432), (1100, -41937216), (1107, 41937216)]

theorem node182_check : node182 =
    Integer.Sparse.merge (Integer.Sparse.scale (-35356) entry_7_1) (Integer.Sparse.scale (873692) entry_7_2) := by decide +kernel

theorem node182_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node182 x = (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x) := by
  rw [node182_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node183 : Integer.Sparse (Fin 2886) := [(861, -25456320), (863, 167748864), (870, 335497728), (884, 125811648), (895, 25456320), (897, -167748864), (905, -335497728), (937, -125811648), (989, -83874432), (1016, 83874432), (1100, -41937216), (1107, 41937216), (2336, -641213568), (2341, -320606784), (2346, 320606784), (2348, 641213568), (2514, 641213568), (2520, 320606784), (2633, 1282427136), (2635, 1282427136), (2656, 1282427136), (2675, -320606784), (2677, -641213568), (2711, -1282427136), (2713, -1282427136), (2734, -1282427136)]

theorem node183_check : node183 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6679308) entry_7_0) node182 := by decide +kernel

theorem node183_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node183 x = (((-6679308 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x)) := by
  rw [node183_check, Integer.Sparse.eval_merge]
  rw [node182_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node184 : Integer.Sparse (Fin 2886) := [(2120, -666288144), (2126, -1332576288), (2138, -666288144), (2148, 666288144), (2154, 1332576288), (2185, 666288144), (2332, -222096048), (2338, -444192096), (2356, -117495888), (2362, -234991776), (2372, 117495888), (2378, 117495888), (2386, 117495888), (2411, 117495888), (2417, 234991776), (2446, 352487664), (2452, 352487664), (2472, 352487664), (2500, 234991776), (2505, 117495888), (2510, 222096048), (2516, 444192096), (2526, -117495888), (2532, -117495888), (2540, -117495888), (2549, -352487664), (2555, -352487664), (2574, -430818256), (2662, 444192096), (2664, -117495888), (2665, -117495888), (2668, -117495888), (2671, 222096048), (2756, -156661184), (2761, -117495888), (2764, -444192096), (2766, 117495888), (2767, 117495888), (2770, 117495888), (2773, -222096048)]

theorem node184_check : node184 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4627001) entry_7_4) (Integer.Sparse.scale (2447831) entry_7_5) := by decide +kernel

theorem node184_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node184 x = (((-4627001 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((2447831 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x) := by
  rw [node184_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node185 : Integer.Sparse (Fin 2886) := [(2120, -666288144), (2126, -1332576288), (2138, -666288144), (2148, 666288144), (2154, 1332576288), (2185, 666288144), (2332, -222096048), (2338, -444192096), (2356, -117495888), (2358, 271207440), (2362, -234991776), (2372, 117495888), (2374, -180804960), (2378, 117495888), (2383, -90402480), (2386, 117495888), (2411, 117495888), (2413, -271207440), (2417, 234991776), (2446, 352487664), (2448, -723219840), (2452, 352487664), (2469, -361609920), (2472, 352487664), (2500, 234991776), (2505, 117495888), (2510, 222096048), (2516, 444192096), (2526, -117495888), (2528, 180804960), (2532, -117495888), (2537, 90402480), (2540, -117495888), (2549, -352487664), (2551, 723219840), (2555, -352487664), (2571, 361609920), (2574, -430818256), (2662, 444192096), (2664, -117495888), (2665, -117495888), (2668, -117495888), (2671, 222096048), (2756, -156661184), (2761, -117495888), (2764, -444192096), (2766, 117495888), (2767, 117495888), (2770, 117495888), (2773, -222096048)]

theorem node185_check : node185 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1883385) entry_7_3) node184 := by decide +kernel

theorem node185_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node185 x = (((-1883385 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + (((-4627001 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((2447831 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x)) := by
  rw [node185_check, Integer.Sparse.eval_merge]
  rw [node184_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node186 : Integer.Sparse (Fin 2886) := [(861, -25456320), (863, 167748864), (870, 335497728), (884, 125811648), (895, 25456320), (897, -167748864), (905, -335497728), (937, -125811648), (989, -83874432), (1016, 83874432), (1100, -41937216), (1107, 41937216), (2120, -666288144), (2126, -1332576288), (2138, -666288144), (2148, 666288144), (2154, 1332576288), (2185, 666288144), (2332, -222096048), (2336, -641213568), (2338, -444192096), (2341, -320606784), (2346, 320606784), (2348, 641213568), (2356, -117495888), (2358, 271207440), (2362, -234991776), (2372, 117495888), (2374, -180804960), (2378, 117495888), (2383, -90402480), (2386, 117495888), (2411, 117495888), (2413, -271207440), (2417, 234991776), (2446, 352487664), (2448, -723219840), (2452, 352487664), (2469, -361609920), (2472, 352487664), (2500, 234991776), (2505, 117495888), (2510, 222096048), (2514, 641213568), (2516, 444192096), (2520, 320606784), (2526, -117495888), (2528, 180804960), (2532, -117495888), (2537, 90402480), (2540, -117495888), (2549, -352487664), (2551, 723219840), (2555, -352487664), (2571, 361609920), (2574, -430818256), (2633, 1282427136), (2635, 1282427136), (2656, 1282427136), (2662, 444192096), (2664, -117495888), (2665, -117495888), (2668, -117495888), (2671, 222096048), (2675, -320606784), (2677, -641213568), (2711, -1282427136), (2713, -1282427136), (2734, -1282427136), (2756, -156661184), (2761, -117495888), (2764, -444192096), (2766, 117495888), (2767, 117495888), (2770, 117495888), (2773, -222096048)]

theorem node186_check : node186 =
    Integer.Sparse.merge node183 node185 := by decide +kernel

theorem node186_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node186 x = ((((-6679308 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x)) + (((-1883385 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + (((-4627001 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((2447831 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x))) := by
  rw [node186_check, Integer.Sparse.eval_merge]
  rw [node183_eval, node185_eval]

def node187 : Integer.Sparse (Fin 2886) := [(1149, 368248032), (1157, 736496064), (1168, -368248032), (1176, -368248032), (1206, -368248032), (1235, -368248032), (1243, -736496064), (1262, 368248032), (1270, 368248032), (1313, 368248032), (1377, -1104744096), (1385, -1104744096), (1393, -736496064), (1403, 1104744096), (1411, 1104744096), (1426, 736496064), (1453, 368248032), (1461, -368248032), (1506, 368248032), (1511, -368248032), (1701, -1104744096), (1704, -368248032), (1708, 1104744096), (1713, 368248032), (1721, 368248032), (1726, -368248032), (2356, 708803328), (2362, 1417606656), (2372, 708803328), (2378, 708803328), (2386, 945071104), (2405, 472535552), (2407, 354401664), (2411, -708803328), (2417, -1417606656), (2446, -1417606656), (2452, -1417606656), (2472, -1417606656), (2500, -1417606656), (2505, -708803328), (2549, 708803328), (2555, 708803328), (2574, 945071104), (2756, 472535552), (2761, 354401664)]

theorem node187_check : node187 =
    Integer.Sparse.merge (Integer.Sparse.scale (7383368) entry_7_7) (Integer.Sparse.scale (-7671834) entry_7_8) := by decide +kernel

theorem node187_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node187 x = (((7383368 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + ((-7671834 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x) := by
  rw [node187_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node188 : Integer.Sparse (Fin 2886) := [(1149, 368248032), (1157, 736496064), (1168, -368248032), (1176, -368248032), (1206, -368248032), (1235, -368248032), (1243, -736496064), (1262, 368248032), (1270, 368248032), (1313, 368248032), (1377, -1104744096), (1385, -1104744096), (1393, -736496064), (1403, 1104744096), (1411, 1104744096), (1426, 736496064), (1453, 368248032), (1461, -368248032), (1506, 368248032), (1511, -368248032), (1701, -1104744096), (1704, -368248032), (1708, 1104744096), (1713, 368248032), (1721, 368248032), (1726, -368248032), (2334, -1129870080), (2356, 708803328), (2362, 1417606656), (2372, 708803328), (2378, 708803328), (2386, 945071104), (2405, 472535552), (2407, 354401664), (2411, -708803328), (2417, -1417606656), (2446, -1417606656), (2452, -1417606656), (2472, -1417606656), (2500, -1417606656), (2505, -708803328), (2512, 1129870080), (2549, 708803328), (2555, 708803328), (2574, 945071104), (2756, 472535552), (2761, 354401664)]

theorem node188_check : node188 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1569264) entry_7_6) node187 := by decide +kernel

theorem node188_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node188 x = (((-1569264 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + (((7383368 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + ((-7671834 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x)) := by
  rw [node188_check, Integer.Sparse.eval_merge]
  rw [node187_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node189 : Integer.Sparse (Fin 2886) := [(1148, -17079984), (1167, 11386656), (1204, 5693328), (1234, 17079984), (1261, -11386656), (1311, -5693328), (1375, 45546624), (1401, -45546624), (1699, 22773312), (1706, -22773312), (2372, -323326416), (2378, -323326416), (2386, -323326416), (2405, 646652832), (2407, 323326416), (2446, -323326416), (2452, -323326416), (2472, -323326416), (2500, 646652832), (2505, 323326416), (2526, 323326416), (2532, 323326416), (2540, 323326416), (2549, 323326416), (2555, 323326416), (2574, 323326416), (2664, 969979248), (2665, 969979248), (2668, 969979248), (2752, -646652832), (2754, -323326416), (2756, -646652832), (2761, -323326416), (2766, -969979248), (2767, -969979248), (2770, -969979248)]

theorem node189_check : node189 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6735967) entry_7_9) (Integer.Sparse.scale (118611) entry_7_10) := by decide +kernel

theorem node189_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node189 x = (((-6735967 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((118611 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x) := by
  rw [node189_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node190 : Integer.Sparse (Fin 2886) := [(2120, 509876640), (2126, 1019753280), (2138, 509876640), (2148, -509876640), (2154, -1019753280), (2185, -509876640), (2333, 475391088), (2337, 950782176), (2347, 950782176), (2352, 509876640), (2511, -475391088), (2515, -950782176), (2634, 950782176), (2655, 475391088), (2662, 1019753280), (2671, 509876640), (2676, -950782176), (2712, -950782176), (2733, -475391088), (2750, -509876640), (2764, -1019753280), (2773, -509876640)]

theorem node190_check : node190 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3301327) entry_7_11) (Integer.Sparse.scale (-3540810) entry_7_12) := by decide +kernel

theorem node190_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node190 x = (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x + ((-3540810 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x) := by
  rw [node190_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node191 : Integer.Sparse (Fin 2886) := [(1148, -17079984), (1167, 11386656), (1204, 5693328), (1234, 17079984), (1261, -11386656), (1311, -5693328), (1375, 45546624), (1401, -45546624), (1699, 22773312), (1706, -22773312), (2120, 509876640), (2126, 1019753280), (2138, 509876640), (2148, -509876640), (2154, -1019753280), (2185, -509876640), (2333, 475391088), (2337, 950782176), (2347, 950782176), (2352, 509876640), (2372, -323326416), (2378, -323326416), (2386, -323326416), (2405, 646652832), (2407, 323326416), (2446, -323326416), (2452, -323326416), (2472, -323326416), (2500, 646652832), (2505, 323326416), (2511, -475391088), (2515, -950782176), (2526, 323326416), (2532, 323326416), (2540, 323326416), (2549, 323326416), (2555, 323326416), (2574, 323326416), (2634, 950782176), (2655, 475391088), (2662, 1019753280), (2664, 969979248), (2665, 969979248), (2668, 969979248), (2671, 509876640), (2676, -950782176), (2712, -950782176), (2733, -475391088), (2750, -509876640), (2752, -646652832), (2754, -323326416), (2756, -646652832), (2761, -323326416), (2764, -1019753280), (2766, -969979248), (2767, -969979248), (2770, -969979248), (2773, -509876640)]

theorem node191_check : node191 =
    Integer.Sparse.merge node189 node190 := by decide +kernel

theorem node191_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node191 x = ((((-6735967 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((118611 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x) + (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x + ((-3540810 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x)) := by
  rw [node191_check, Integer.Sparse.eval_merge]
  rw [node189_eval, node190_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
