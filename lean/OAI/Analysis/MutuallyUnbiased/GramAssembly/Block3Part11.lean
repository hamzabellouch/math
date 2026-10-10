import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Part10

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

def node352 : Integer.Sparse (Fin 2886) := [(1873, 99063168), (1878, -99063168), (1889, -14025024), (1890, -3506256), (1948, -792505344), (1952, -297189504), (1961, -396252672), (1974, 14025024), (1977, 3506256), (2030, 792505344), (2036, 297189504), (2044, 396252672), (2070, 3506256), (2073, -3506256), (2078, 198126336), (2080, -198126336)]

theorem node352_check : node352 =
    Integer.Sparse.merge (Integer.Sparse.scale (-24349) entry_13_16) (Integer.Sparse.scale (-2063816) entry_13_17) := by decide +kernel

theorem node352_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node352 x = (((-24349 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + ((-2063816 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x) := by
  rw [node352_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node353 : Integer.Sparse (Fin 2886) := [(625, 53651712), (629, -53651712), (776, -321910272), (780, -268258560), (799, -214606848), (824, 268258560), (825, 321910272), (832, 214606848), (1975, 862133520), (1976, 1724267040), (2071, -862133520), (2072, -1724267040)]

theorem node353_check : node353 =
    Integer.Sparse.merge (Integer.Sparse.scale (1117744) entry_13_18) (Integer.Sparse.scale (3592223) entry_13_19) := by decide +kernel

theorem node353_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node353 x = (((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x + ((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x) := by
  rw [node353_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node354 : Integer.Sparse (Fin 2886) := [(625, 53651712), (629, -53651712), (776, -321910272), (780, -268258560), (799, -214606848), (824, 268258560), (825, 321910272), (832, 214606848), (1873, 99063168), (1878, -99063168), (1889, -14025024), (1890, -3506256), (1948, -792505344), (1952, -297189504), (1961, -396252672), (1974, 14025024), (1975, 862133520), (1976, 1724267040), (1977, 3506256), (2030, 792505344), (2036, 297189504), (2044, 396252672), (2070, 3506256), (2071, -862133520), (2072, -1724267040), (2073, -3506256), (2078, 198126336), (2080, -198126336)]

theorem node354_check : node354 =
    Integer.Sparse.merge node352 node353 := by decide +kernel

theorem node354_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node354 x = ((((-24349 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + ((-2063816 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x) + (((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x + ((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x)) := by
  rw [node354_check, Integer.Sparse.eval_merge]
  rw [node352_eval, node353_eval]

def node355 : Integer.Sparse (Fin 2886) := [(624, 70202304), (625, 53651712), (626, 280809216), (629, -53651712), (678, 425700288), (680, 1170675792), (699, -425700288), (701, -1064250720), (709, -354750240), (733, 141900096), (736, 106425072), (775, -70202304), (776, -321910272), (780, -268258560), (798, 70202304), (799, -214606848), (824, 268258560), (825, 321910272), (832, 214606848), (836, -280809216), (839, -70202304), (1799, -790272960), (1800, -2173250640), (1873, 99063168), (1878, -99063168), (1889, -14025024), (1890, -3506256), (1948, -792505344), (1952, -297189504), (1961, -396252672), (1974, 14025024), (1975, 862133520), (1976, 1724267040), (1977, 3506256), (2030, 792505344), (2036, 297189504), (2044, 396252672), (2053, 790272960), (2054, 1975682400), (2067, 197568240), (2070, 3506256), (2071, -862133520), (2072, -1724267040), (2073, -3506256), (2078, 198126336), (2080, -198126336), (2090, 197568240), (2099, -197568240)]

theorem node355_check : node355 =
    Integer.Sparse.merge node351 node354 := by decide +kernel

theorem node355_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node355 x = ((((2217189 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + (((-487516 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x + ((-4116005 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x)) + ((((-24349 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + ((-2063816 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x) + (((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x + ((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x))) := by
  rw [node355_check, Integer.Sparse.eval_merge]
  rw [node351_eval, node354_eval]

def node356 : Integer.Sparse (Fin 2886) := [(1882, -191416512), (1883, 198500688), (1886, -7084176), (1965, -219753216), (1966, 141827280), (1971, -28336704), (2056, 411169728), (2057, 992503440), (2059, 779834400), (2064, 794002752), (2091, -1332831408), (2093, -772750224), (2097, -765666048)]

theorem node356_check : node356 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3987844) entry_13_21) (Integer.Sparse.scale (-147587) entry_13_22) := by decide +kernel

theorem node356_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node356 x = (((-3987844 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_21 x + ((-147587 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_22 x) := by
  rw [node356_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node357 : Integer.Sparse (Fin 2886) := [(315, -427308480), (319, 427308480), (1882, -191416512), (1883, 198500688), (1886, -7084176), (1965, -219753216), (1966, 141827280), (1971, -28336704), (2056, 411169728), (2057, 992503440), (2059, 779834400), (2064, 794002752), (2091, -1332831408), (2093, -772750224), (2097, -765666048)]

theorem node357_check : node357 =
    Integer.Sparse.merge (Integer.Sparse.scale (593484) entry_13_20) node356 := by decide +kernel

theorem node357_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node357 x = (((593484 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x + (((-3987844 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_21 x + ((-147587 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_22 x)) := by
  rw [node357_check, Integer.Sparse.eval_merge]
  rw [node356_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node358 : Integer.Sparse (Fin 2886) := [(657, 362783520), (807, -362783520), (1792, 44447232), (1796, 38891328), (2023, -44447232), (2027, -27779520), (2048, -11111808), (2075, -11111808), (2086, 11111808)]

theorem node358_check : node358 =
    Integer.Sparse.merge (Integer.Sparse.scale (115748) entry_13_23) (Integer.Sparse.scale (503866) entry_13_24) := by decide +kernel

theorem node358_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node358 x = (((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_23 x + ((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_24 x) := by
  rw [node358_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node359 : Integer.Sparse (Fin 2886) := [(642, 11650128), (644, -11650128), (757, -69900768), (759, -58250640), (772, -46600512), (784, 58250640), (785, 69900768), (797, 46600512), (1969, 281771568), (1970, -281771568), (2062, -281771568), (2063, -1127086272), (2095, 281771568), (2096, 1127086272)]

theorem node359_check : node359 =
    Integer.Sparse.merge (Integer.Sparse.scale (1956747) entry_13_25) (Integer.Sparse.scale (242711) entry_13_26) := by decide +kernel

theorem node359_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node359 x = (((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_25 x + ((242711 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_26 x) := by
  rw [node359_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node360 : Integer.Sparse (Fin 2886) := [(642, 11650128), (644, -11650128), (657, 362783520), (757, -69900768), (759, -58250640), (772, -46600512), (784, 58250640), (785, 69900768), (797, 46600512), (807, -362783520), (1792, 44447232), (1796, 38891328), (1969, 281771568), (1970, -281771568), (2023, -44447232), (2027, -27779520), (2048, -11111808), (2062, -281771568), (2063, -1127086272), (2075, -11111808), (2086, 11111808), (2095, 281771568), (2096, 1127086272)]

theorem node360_check : node360 =
    Integer.Sparse.merge node358 node359 := by decide +kernel

theorem node360_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node360 x = ((((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_23 x + ((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_24 x) + (((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_25 x + ((242711 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_26 x)) := by
  rw [node360_check, Integer.Sparse.eval_merge]
  rw [node358_eval, node359_eval]

def node361 : Integer.Sparse (Fin 2886) := [(315, -427308480), (319, 427308480), (642, 11650128), (644, -11650128), (657, 362783520), (757, -69900768), (759, -58250640), (772, -46600512), (784, 58250640), (785, 69900768), (797, 46600512), (807, -362783520), (1792, 44447232), (1796, 38891328), (1882, -191416512), (1883, 198500688), (1886, -7084176), (1965, -219753216), (1966, 141827280), (1969, 281771568), (1970, -281771568), (1971, -28336704), (2023, -44447232), (2027, -27779520), (2048, -11111808), (2056, 411169728), (2057, 992503440), (2059, 779834400), (2062, -281771568), (2063, -1127086272), (2064, 794002752), (2075, -11111808), (2086, 11111808), (2091, -1332831408), (2093, -772750224), (2095, 281771568), (2096, 1127086272), (2097, -765666048)]

theorem node361_check : node361 =
    Integer.Sparse.merge node357 node360 := by decide +kernel

theorem node361_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node361 x = ((((593484 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x + (((-3987844 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_21 x + ((-147587 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_22 x)) + ((((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_23 x + ((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_24 x) + (((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_25 x + ((242711 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_26 x))) := by
  rw [node361_check, Integer.Sparse.eval_merge]
  rw [node357_eval, node360_eval]

def node362 : Integer.Sparse (Fin 2886) := [(315, -427308480), (319, 427308480), (624, 70202304), (625, 53651712), (626, 280809216), (629, -53651712), (642, 11650128), (644, -11650128), (657, 362783520), (678, 425700288), (680, 1170675792), (699, -425700288), (701, -1064250720), (709, -354750240), (733, 141900096), (736, 106425072), (757, -69900768), (759, -58250640), (772, -46600512), (775, -70202304), (776, -321910272), (780, -268258560), (784, 58250640), (785, 69900768), (797, 46600512), (798, 70202304), (799, -214606848), (807, -362783520), (824, 268258560), (825, 321910272), (832, 214606848), (836, -280809216), (839, -70202304), (1792, 44447232), (1796, 38891328), (1799, -790272960), (1800, -2173250640), (1873, 99063168), (1878, -99063168), (1882, -191416512), (1883, 198500688), (1886, -7084176), (1889, -14025024), (1890, -3506256), (1948, -792505344), (1952, -297189504), (1961, -396252672), (1965, -219753216), (1966, 141827280), (1969, 281771568), (1970, -281771568), (1971, -28336704), (1974, 14025024), (1975, 862133520), (1976, 1724267040), (1977, 3506256), (2023, -44447232), (2027, -27779520), (2030, 792505344), (2036, 297189504), (2044, 396252672), (2048, -11111808), (2053, 790272960), (2054, 1975682400), (2056, 411169728), (2057, 992503440), (2059, 779834400), (2062, -281771568), (2063, -1127086272), (2064, 794002752), (2067, 197568240), (2070, 3506256), (2071, -862133520), (2072, -1724267040), (2073, -3506256), (2075, -11111808), (2078, 198126336), (2080, -198126336), (2086, 11111808), (2090, 197568240), (2091, -1332831408), (2093, -772750224), (2095, 281771568), (2096, 1127086272), (2097, -765666048), (2099, -197568240)]

theorem node362_check : node362 =
    Integer.Sparse.merge node355 node361 := by decide +kernel

theorem node362_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node362 x = (((((2217189 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + (((-487516 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x + ((-4116005 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x)) + ((((-24349 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + ((-2063816 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x) + (((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x + ((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x))) + ((((593484 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x + (((-3987844 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_21 x + ((-147587 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_22 x)) + ((((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_23 x + ((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_24 x) + (((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_25 x + ((242711 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_26 x)))) := by
  rw [node362_check, Integer.Sparse.eval_merge]
  rw [node355_eval, node361_eval]

def node363 : Integer.Sparse (Fin 2886) := [(315, -427308480), (319, 427308480), (624, 211707456), (625, 53651712), (626, 669948384), (629, -53651712), (635, -47187360), (642, 11650128), (644, -11650128), (647, 171823920), (652, -171823920), (657, 362783520), (660, -50921232), (661, 50921232), (678, 425700288), (680, 1170675792), (699, -425700288), (701, -1064250720), (709, -354750240), (715, -687295680), (716, -1202767440), (723, -687295680), (733, 141900096), (736, 106425072), (739, 560133552), (740, 203684928), (757, -69900768), (759, -58250640), (772, -46600512), (775, -211707456), (776, -321910272), (777, -353762880), (780, -268258560), (782, 687295680), (783, 859119600), (784, 58250640), (785, 69900768), (786, 343647840), (792, 687295680), (797, 46600512), (798, 34826016), (799, -214606848), (807, -362783520), (820, 47187360), (821, -509212320), (822, -50921232), (823, -203684928), (824, 268258560), (825, 321910272), (832, 214606848), (836, -316185504), (837, 171823920), (838, -171823920), (839, -34826016), (1791, -102276432), (1792, -68358336), (1793, -82886688), (1796, 151696896), (1799, -820168224), (1800, -2292831696), (1802, -560113920), (1868, 191473680), (1870, 690592896), (1873, 99063168), (1876, 245768784), (1878, -99063168), (1882, -191416512), (1883, 198500688), (1886, -7084176), (1889, -123478176), (1890, 105946896), (1947, -329231664), (1948, -792505344), (1949, -350817792), (1952, -297189504), (1959, -144760224), (1961, -396252672), (1965, -219753216), (1966, 141827280), (1969, 281771568), (1970, -281771568), (1971, -28336704), (1974, 1218009696), (1975, 862133520), (1976, 1724267040), (1977, 441318864), (2022, 102276432), (2023, 632386176), (2024, 652438080), (2027, 536248320), (2029, 137757984), (2030, 792505344), (2031, 445403520), (2034, 246348192), (2036, 297189504), (2042, 506700864), (2044, 396252672), (2047, 223942608), (2048, 440110464), (2053, 820168224), (2054, 1975682400), (2056, 411169728), (2057, 992503440), (2059, 779834400), (2062, -281771568), (2063, -1127086272), (2064, 794002752), (2067, 167672976), (2068, 560113920), (2069, -1094531520), (2070, -105946896), (2071, -862133520), (2072, -1724267040), (2073, -441318864), (2074, -564027840), (2075, -687945216), (2078, 198126336), (2080, -198126336), (2086, -440110464), (2090, -252402096), (2091, -2118010032), (2093, -1264867200), (2095, 281771568), (2096, 1127086272), (2097, -1127606688), (2099, -391615584)]

theorem node363_check : node363 =
    Integer.Sparse.merge node349 node362 := by decide +kernel

theorem node363_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node363 x = ((((((-2350116 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_0 x + (((-65538 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_1 x + ((737006 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_2 x)) + (((2280274 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_3 x + (((-1359246 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x + ((420869 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_5 x))) + ((((-777936 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_6 x + (((1566438 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_7 x + ((-3579665 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_8 x)) + ((((-2276717 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x + ((1060859 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_10 x) + (((207606 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_11 x + ((-1102075 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_12 x)))) + (((((2217189 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + (((-487516 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x + ((-4116005 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x)) + ((((-24349 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + ((-2063816 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x) + (((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x + ((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x))) + ((((593484 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x + (((-3987844 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_21 x + ((-147587 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_22 x)) + ((((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_23 x + ((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_24 x) + (((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_25 x + ((242711 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_26 x))))) := by
  rw [node363_check, Integer.Sparse.eval_merge]
  rw [node349_eval, node362_eval]

def node364 : Integer.Sparse (Fin 2886) := [(1, -333424512), (3, -40865760), (7, -1333698048), (76, 333424512), (129, 40865760), (167, 1000273536), (176, 333424512)]

theorem node364_check : node364 =
    Integer.Sparse.merge (Integer.Sparse.scale (56758) entry_14_1) (Integer.Sparse.scale (2315448) entry_14_2) := by decide +kernel

theorem node364_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node364 x = (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x + ((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x) := by
  rw [node364_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node365 : Integer.Sparse (Fin 2886) := [(1, -333424512), (3, -40865760), (7, -1333698048), (76, 333424512), (129, 40865760), (167, 1000273536), (176, 333424512), (848, 256574880), (855, -256574880), (956, 1026299520), (1035, 256574880), (1049, -1026299520), (1085, -256574880)]

theorem node365_check : node365 =
    Integer.Sparse.merge (Integer.Sparse.scale (1781770) entry_14_0) node364 := by decide +kernel

theorem node365_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node365 x = (((1781770 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_0 x + (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x + ((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x)) := by
  rw [node365_check, Integer.Sparse.eval_merge]
  rw [node364_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node366 : Integer.Sparse (Fin 2886) := [(843, -220745520), (851, -882982080), (870, -143337312), (884, 143337312), (897, -143337312), (905, -430011936), (937, -143337312), (951, 220745520), (972, 143337312), (989, 430011936), (1016, 143337312), (1030, 882982080), (1093, -220745520), (1097, -143337312), (1100, 143337312), (1110, 220745520)]

theorem node366_check : node366 =
    Integer.Sparse.merge (Integer.Sparse.scale (1532955) entry_14_4) (Integer.Sparse.scale (995398) entry_14_5) := by decide +kernel

theorem node366_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node366 x = (((1532955 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x + ((995398 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x) := by
  rw [node366_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node367 : Integer.Sparse (Fin 2886) := [(843, -220745520), (851, -882982080), (865, -389772576), (870, -143337312), (880, 389772576), (884, 143337312), (897, -143337312), (899, -1559090304), (905, -430011936), (933, -389772576), (937, -143337312), (951, 220745520), (972, 143337312), (985, 1559090304), (989, 430011936), (1012, 389772576), (1016, 143337312), (1030, 882982080), (1093, -220745520), (1097, -143337312), (1100, 143337312), (1110, 220745520)]

theorem node367_check : node367 =
    Integer.Sparse.merge (Integer.Sparse.scale (2706754) entry_14_3) node366 := by decide +kernel

theorem node367_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node367 x = (((2706754 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + (((1532955 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x + ((995398 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x)) := by
  rw [node367_check, Integer.Sparse.eval_merge]
  rw [node366_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node368 : Integer.Sparse (Fin 2886) := [(1, -333424512), (3, -40865760), (7, -1333698048), (76, 333424512), (129, 40865760), (167, 1000273536), (176, 333424512), (843, -220745520), (848, 256574880), (851, -882982080), (855, -256574880), (865, -389772576), (870, -143337312), (880, 389772576), (884, 143337312), (897, -143337312), (899, -1559090304), (905, -430011936), (933, -389772576), (937, -143337312), (951, 220745520), (956, 1026299520), (972, 143337312), (985, 1559090304), (989, 430011936), (1012, 389772576), (1016, 143337312), (1030, 882982080), (1035, 256574880), (1049, -1026299520), (1085, -256574880), (1093, -220745520), (1097, -143337312), (1100, 143337312), (1110, 220745520)]

theorem node368_check : node368 =
    Integer.Sparse.merge node365 node367 := by decide +kernel

theorem node368_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node368 x = ((((1781770 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_0 x + (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x + ((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x)) + (((2706754 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + (((1532955 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x + ((995398 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x))) := by
  rw [node368_check, Integer.Sparse.eval_merge]
  rw [node365_eval, node367_eval]

def node369 : Integer.Sparse (Fin 2886) := [(37, -330572160), (42, -661144320), (66, -330572160), (91, 330572160), (94, 330572160), (102, 330572160), (121, 330572160), (185, -330572160), (191, 330572160), (333, -330572160), (380, -330572160), (400, -330572160), (423, 661144320), (427, 330572160), (863, 220502016), (870, 441004032), (884, 441004032), (897, -220502016), (905, -441004032), (937, -441004032), (989, 441004032), (1016, -441004032), (1100, 220502016), (1107, -220502016)]

theorem node369_check : node369 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1531264) entry_14_7) (Integer.Sparse.scale (2295640) entry_14_8) := by decide +kernel

theorem node369_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node369 x = (((-1531264 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x + ((2295640 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x) := by
  rw [node369_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node370 : Integer.Sparse (Fin 2886) := [(37, -330572160), (42, -661144320), (66, -330572160), (91, 330572160), (94, 330572160), (102, 330572160), (121, 330572160), (185, -330572160), (191, 330572160), (333, -330572160), (380, -330572160), (400, -330572160), (423, 661144320), (427, 330572160), (845, -394678800), (863, 220502016), (870, 441004032), (884, 441004032), (897, -220502016), (905, -441004032), (937, -441004032), (989, 441004032), (1016, -441004032), (1026, 394678800), (1100, 220502016), (1107, -220502016)]

theorem node370_check : node370 =
    Integer.Sparse.merge (Integer.Sparse.scale (548165) entry_14_6) node369 := by decide +kernel

theorem node370_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node370 x = (((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x + (((-1531264 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x + ((2295640 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x)) := by
  rw [node370_check, Integer.Sparse.eval_merge]
  rw [node369_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node371 : Integer.Sparse (Fin 2886) := [(17, 221244624), (27, -221244624), (39, 884978496), (64, 221244624), (99, -884978496), (118, -221244624), (863, 199377648), (870, -199377648), (897, 199377648), (905, -199377648), (972, 598132944), (989, 199377648), (1016, 199377648), (1097, -598132944), (1100, -199377648), (1107, -199377648)]

theorem node371_check : node371 =
    Integer.Sparse.merge (Integer.Sparse.scale (1384567) entry_14_9) (Integer.Sparse.scale (-1536421) entry_14_10) := by decide +kernel

theorem node371_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node371 x = (((1384567 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x + ((-1536421 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x) := by
  rw [node371_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node372 : Integer.Sparse (Fin 2886) := [(843, 277226208), (844, 264840768), (849, 397261152), (851, 415839312), (951, 415839312), (952, 397261152), (1028, -397261152), (1030, -415839312), (1047, -397261152), (1083, -264840768), (1093, -415839312), (1110, -277226208)]

theorem node372_check : node372 =
    Integer.Sparse.merge (Integer.Sparse.scale (919586) entry_14_11) (Integer.Sparse.scale (962591) entry_14_12) := by decide +kernel

theorem node372_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node372 x = (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x + ((962591 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x) := by
  rw [node372_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node373 : Integer.Sparse (Fin 2886) := [(17, 221244624), (27, -221244624), (39, 884978496), (64, 221244624), (99, -884978496), (118, -221244624), (843, 277226208), (844, 264840768), (849, 397261152), (851, 415839312), (863, 199377648), (870, -199377648), (897, 199377648), (905, -199377648), (951, 415839312), (952, 397261152), (972, 598132944), (989, 199377648), (1016, 199377648), (1028, -397261152), (1030, -415839312), (1047, -397261152), (1083, -264840768), (1093, -415839312), (1097, -598132944), (1100, -199377648), (1107, -199377648), (1110, -277226208)]

theorem node373_check : node373 =
    Integer.Sparse.merge node371 node372 := by decide +kernel

theorem node373_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node373 x = ((((1384567 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x + ((-1536421 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x) + (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x + ((962591 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x)) := by
  rw [node373_check, Integer.Sparse.eval_merge]
  rw [node371_eval, node372_eval]

def node374 : Integer.Sparse (Fin 2886) := [(17, 221244624), (27, -221244624), (37, -330572160), (39, 884978496), (42, -661144320), (64, 221244624), (66, -330572160), (91, 330572160), (94, 330572160), (99, -884978496), (102, 330572160), (118, -221244624), (121, 330572160), (185, -330572160), (191, 330572160), (333, -330572160), (380, -330572160), (400, -330572160), (423, 661144320), (427, 330572160), (843, 277226208), (844, 264840768), (845, -394678800), (849, 397261152), (851, 415839312), (863, 419879664), (870, 241626384), (884, 441004032), (897, -21124368), (905, -640381680), (937, -441004032), (951, 415839312), (952, 397261152), (972, 598132944), (989, 640381680), (1016, -241626384), (1026, 394678800), (1028, -397261152), (1030, -415839312), (1047, -397261152), (1083, -264840768), (1093, -415839312), (1097, -598132944), (1100, 21124368), (1107, -419879664), (1110, -277226208)]

theorem node374_check : node374 =
    Integer.Sparse.merge node370 node373 := by decide +kernel

theorem node374_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node374 x = ((((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x + (((-1531264 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x + ((2295640 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x)) + ((((1384567 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x + ((-1536421 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x) + (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x + ((962591 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x))) := by
  rw [node374_check, Integer.Sparse.eval_merge]
  rw [node370_eval, node373_eval]

def node375 : Integer.Sparse (Fin 2886) := [(1, -333424512), (3, -40865760), (7, -1333698048), (17, 221244624), (27, -221244624), (37, -330572160), (39, 884978496), (42, -661144320), (64, 221244624), (66, -330572160), (76, 333424512), (91, 330572160), (94, 330572160), (99, -884978496), (102, 330572160), (118, -221244624), (121, 330572160), (129, 40865760), (167, 1000273536), (176, 333424512), (185, -330572160), (191, 330572160), (333, -330572160), (380, -330572160), (400, -330572160), (423, 661144320), (427, 330572160), (843, 56480688), (844, 264840768), (845, -394678800), (848, 256574880), (849, 397261152), (851, -467142768), (855, -256574880), (863, 419879664), (865, -389772576), (870, 98289072), (880, 389772576), (884, 584341344), (897, -164461680), (899, -1559090304), (905, -1070393616), (933, -389772576), (937, -584341344), (951, 636584832), (952, 397261152), (956, 1026299520), (972, 741470256), (985, 1559090304), (989, 1070393616), (1012, 389772576), (1016, -98289072), (1026, 394678800), (1028, -397261152), (1030, 467142768), (1035, 256574880), (1047, -397261152), (1049, -1026299520), (1083, -264840768), (1085, -256574880), (1093, -636584832), (1097, -741470256), (1100, 164461680), (1107, -419879664), (1110, -56480688)]

theorem node375_check : node375 =
    Integer.Sparse.merge node368 node374 := by decide +kernel

theorem node375_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node375 x = (((((1781770 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_0 x + (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x + ((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x)) + (((2706754 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + (((1532955 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x + ((995398 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x))) + ((((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x + (((-1531264 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x + ((2295640 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x)) + ((((1384567 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x + ((-1536421 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x) + (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x + ((962591 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x)))) := by
  rw [node375_check, Integer.Sparse.eval_merge]
  rw [node368_eval, node374_eval]

def node376 : Integer.Sparse (Fin 2886) := [(1, 923294016), (7, 1384941024), (76, 1384941024), (167, -2769882048), (176, -923294016), (844, -397708128), (849, -1590832512), (952, 397708128), (1028, 1590832512), (1047, -397708128), (1083, 397708128)]

theorem node376_check : node376 =
    Integer.Sparse.merge (Integer.Sparse.scale (3205882) entry_14_14) (Integer.Sparse.scale (2761862) entry_14_15) := by decide +kernel

theorem node376_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node376 x = (((3205882 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x + ((2761862 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x) := by
  rw [node376_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node377 : Integer.Sparse (Fin 2886) := [(1, 923294016), (7, 1384941024), (76, 1384941024), (167, -2769882048), (176, -923294016), (624, 70202304), (626, 280809216), (775, -70202304), (798, 70202304), (836, -280809216), (839, -70202304), (844, -397708128), (849, -1590832512), (952, 397708128), (1028, 1590832512), (1047, -397708128), (1083, 397708128)]

theorem node377_check : node377 =
    Integer.Sparse.merge (Integer.Sparse.scale (-487516) entry_14_13) node376 := by decide +kernel

theorem node377_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node377 x = (((-487516 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_13 x + (((3205882 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x + ((2761862 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x)) := by
  rw [node377_check, Integer.Sparse.eval_merge]
  rw [node376_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node378 : Integer.Sparse (Fin 2886) := [(865, -838522368), (875, -557001936), (880, -559014912), (888, 557001936), (899, 838522368), (902, -1114003872), (910, -1114003872), (933, 559014912), (942, -557001936), (977, 1114003872), (985, -838522368), (993, 1114003872), (1012, 838522368), (1021, 557001936), (1058, -1114003872), (1064, 1114003872)]

theorem node378_check : node378 =
    Integer.Sparse.merge (Integer.Sparse.scale (1941024) entry_14_16) (Integer.Sparse.scale (3868069) entry_14_17) := by decide +kernel

theorem node378_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node378 x = (((1941024 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + ((3868069 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x) := by
  rw [node378_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node379 : Integer.Sparse (Fin 2886) := [(8, 353171520), (12, -353171520), (80, 706343040), (84, 706343040), (86, 353171520), (89, -353171520), (135, 353171520), (138, 353171520), (142, -706343040), (146, -353171520), (148, -706343040), (163, -353171520), (918, 720293760), (1004, -720293760)]

theorem node379_check : node379 =
    Integer.Sparse.merge (Integer.Sparse.scale (2452580) entry_14_18) (Integer.Sparse.scale (-1000408) entry_14_19) := by decide +kernel

theorem node379_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node379 x = (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x + ((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x) := by
  rw [node379_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node380 : Integer.Sparse (Fin 2886) := [(8, 353171520), (12, -353171520), (80, 706343040), (84, 706343040), (86, 353171520), (89, -353171520), (135, 353171520), (138, 353171520), (142, -706343040), (146, -353171520), (148, -706343040), (163, -353171520), (865, -838522368), (875, -557001936), (880, -559014912), (888, 557001936), (899, 838522368), (902, -1114003872), (910, -1114003872), (918, 720293760), (933, 559014912), (942, -557001936), (977, 1114003872), (985, -838522368), (993, 1114003872), (1004, -720293760), (1012, 838522368), (1021, 557001936), (1058, -1114003872), (1064, 1114003872)]

theorem node380_check : node380 =
    Integer.Sparse.merge node378 node379 := by decide +kernel

theorem node380_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node380 x = ((((1941024 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + ((3868069 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x) + (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x + ((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x)) := by
  rw [node380_check, Integer.Sparse.eval_merge]
  rw [node378_eval, node379_eval]

def node381 : Integer.Sparse (Fin 2886) := [(1, 923294016), (7, 1384941024), (8, 353171520), (12, -353171520), (76, 1384941024), (80, 706343040), (84, 706343040), (86, 353171520), (89, -353171520), (135, 353171520), (138, 353171520), (142, -706343040), (146, -353171520), (148, -706343040), (163, -353171520), (167, -2769882048), (176, -923294016), (624, 70202304), (626, 280809216), (775, -70202304), (798, 70202304), (836, -280809216), (839, -70202304), (844, -397708128), (849, -1590832512), (865, -838522368), (875, -557001936), (880, -559014912), (888, 557001936), (899, 838522368), (902, -1114003872), (910, -1114003872), (918, 720293760), (933, 559014912), (942, -557001936), (952, 397708128), (977, 1114003872), (985, -838522368), (993, 1114003872), (1004, -720293760), (1012, 838522368), (1021, 557001936), (1028, 1590832512), (1047, -397708128), (1058, -1114003872), (1064, 1114003872), (1083, 397708128)]

theorem node381_check : node381 =
    Integer.Sparse.merge node377 node380 := by decide +kernel

theorem node381_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node381 x = ((((-487516 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_13 x + (((3205882 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x + ((2761862 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x)) + ((((1941024 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + ((3868069 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x) + (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x + ((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x))) := by
  rw [node381_check, Integer.Sparse.eval_merge]
  rw [node377_eval, node380_eval]

def node382 : Integer.Sparse (Fin 2886) := [(864, 517682448), (868, -398489616), (882, -119192832), (898, 636875280), (903, -160103952), (935, 119192832), (973, 1433854512), (987, 160103952), (1014, 398489616), (1056, -1433854512), (1062, -636875280), (1075, -517682448)]

theorem node382_check : node382 =
    Integer.Sparse.merge (Integer.Sparse.scale (3595017) entry_14_21) (Integer.Sparse.scale (-827728) entry_14_22) := by decide +kernel

theorem node382_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node382 x = (((3595017 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_21 x + ((-827728 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_22 x) := by
  rw [node382_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node383 : Integer.Sparse (Fin 2886) := [(538, 282892320), (561, -282892320), (864, 517682448), (868, -398489616), (882, -119192832), (898, 636875280), (903, -160103952), (935, 119192832), (973, 1433854512), (987, 160103952), (1014, 398489616), (1056, -1433854512), (1062, -636875280), (1075, -517682448)]

theorem node383_check : node383 =
    Integer.Sparse.merge (Integer.Sparse.scale (392906) entry_14_20) node382 := by decide +kernel

theorem node383_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node383 x = (((392906 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_20 x + (((3595017 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_21 x + ((-827728 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_22 x)) := by
  rw [node383_check, Integer.Sparse.eval_merge]
  rw [node382_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block3

end OAI
