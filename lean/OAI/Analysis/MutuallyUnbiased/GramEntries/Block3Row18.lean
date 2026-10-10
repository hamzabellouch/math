import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block101
import OAI.Analysis.MutuallyUnbiased.GramRows.Block102
import OAI.Analysis.MutuallyUnbiased.GramRows.Block103
import OAI.Analysis.MutuallyUnbiased.GramRows.Block104
import OAI.Analysis.MutuallyUnbiased.GramRows.Block105

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows18_0 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row9933, row9934, row9935, row9936, row9937, row9938, row9939, row9940, row9941, row9942, row9943, row9944, row9945, row9946, row9947, row9948, row9949, row9950, row9951, row9952, row9953, row9954, row9955, row9956]

theorem entryCheck18_0 : entry18_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_0 k)) := by decide +kernel

theorem rowsSound18_0 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval9933 x
  · exact rowEval9934 x
  · exact rowEval9935 x
  · exact rowEval9936 x
  · exact rowEval9937 x
  · exact rowEval9938 x
  · exact rowEval9939 x
  · exact rowEval9940 x
  · exact rowEval9941 x
  · exact rowEval9942 x
  · exact rowEval9943 x
  · exact rowEval9944 x
  · exact rowEval9945 x
  · exact rowEval9946 x
  · exact rowEval9947 x
  · exact rowEval9948 x
  · exact rowEval9949 x
  · exact rowEval9950 x
  · exact rowEval9951 x
  · exact rowEval9952 x
  · exact rowEval9953 x
  · exact rowEval9954 x
  · exact rowEval9955 x
  · exact rowEval9956 x

theorem entryEval18_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_0 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck18_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_0]

def rows18_1 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row9957, row9958, row9959, row9960, row9961, row9962, row9963, row9964, row9965, row9966, row9967, row9968, row9969, row9970, row9971, row9972, row9973, row9974, row9975, row9976, row9977, row9978, row9979, row9980]

theorem entryCheck18_1 : entry18_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_1 k)) := by decide +kernel

theorem rowsSound18_1 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval9957 x
  · exact rowEval9958 x
  · exact rowEval9959 x
  · exact rowEval9960 x
  · exact rowEval9961 x
  · exact rowEval9962 x
  · exact rowEval9963 x
  · exact rowEval9964 x
  · exact rowEval9965 x
  · exact rowEval9966 x
  · exact rowEval9967 x
  · exact rowEval9968 x
  · exact rowEval9969 x
  · exact rowEval9970 x
  · exact rowEval9971 x
  · exact rowEval9972 x
  · exact rowEval9973 x
  · exact rowEval9974 x
  · exact rowEval9975 x
  · exact rowEval9976 x
  · exact rowEval9977 x
  · exact rowEval9978 x
  · exact rowEval9979 x
  · exact rowEval9980 x

theorem entryEval18_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_1 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck18_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_1]

def rows18_2 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row9981, row9982, row9983, row9984, row9985, row9986, row9987, row9988, row9989, row9990, row9991, row9992, row9993, row9994, row9995, row9996, row9997, row9998, row9999, row10000, row10001, row10002, row10003, row10004]

theorem entryCheck18_2 : entry18_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_2 k)) := by decide +kernel

theorem rowsSound18_2 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval9981 x
  · exact rowEval9982 x
  · exact rowEval9983 x
  · exact rowEval9984 x
  · exact rowEval9985 x
  · exact rowEval9986 x
  · exact rowEval9987 x
  · exact rowEval9988 x
  · exact rowEval9989 x
  · exact rowEval9990 x
  · exact rowEval9991 x
  · exact rowEval9992 x
  · exact rowEval9993 x
  · exact rowEval9994 x
  · exact rowEval9995 x
  · exact rowEval9996 x
  · exact rowEval9997 x
  · exact rowEval9998 x
  · exact rowEval9999 x
  · exact rowEval10000 x
  · exact rowEval10001 x
  · exact rowEval10002 x
  · exact rowEval10003 x
  · exact rowEval10004 x

theorem entryEval18_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_2 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck18_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_2]

def rows18_3 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10005, row10006, row10007, row10008, row10009, row10010, row10011, row10012, row10013, row10014, row10015, row10016, row10017, row10018, row10019, row10020, row10021, row10022, row10023, row10024, row10025, row10026, row10027, row10028]

theorem entryCheck18_3 : entry18_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_3 k)) := by decide +kernel

theorem rowsSound18_3 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval10005 x
  · exact rowEval10006 x
  · exact rowEval10007 x
  · exact rowEval10008 x
  · exact rowEval10009 x
  · exact rowEval10010 x
  · exact rowEval10011 x
  · exact rowEval10012 x
  · exact rowEval10013 x
  · exact rowEval10014 x
  · exact rowEval10015 x
  · exact rowEval10016 x
  · exact rowEval10017 x
  · exact rowEval10018 x
  · exact rowEval10019 x
  · exact rowEval10020 x
  · exact rowEval10021 x
  · exact rowEval10022 x
  · exact rowEval10023 x
  · exact rowEval10024 x
  · exact rowEval10025 x
  · exact rowEval10026 x
  · exact rowEval10027 x
  · exact rowEval10028 x

theorem entryEval18_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_3 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck18_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_3]

def rows18_4 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10029, row10030, row10031, row10032, row10033, row10034, row10035, row10036, row10037, row10038, row10039, row10040, row10041, row10042, row10043, row10044, row10045, row10046, row10047, row10048, row10049, row10050, row10051, row10052]

theorem entryCheck18_4 : entry18_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_4 k)) := by decide +kernel

theorem rowsSound18_4 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval10029 x
  · exact rowEval10030 x
  · exact rowEval10031 x
  · exact rowEval10032 x
  · exact rowEval10033 x
  · exact rowEval10034 x
  · exact rowEval10035 x
  · exact rowEval10036 x
  · exact rowEval10037 x
  · exact rowEval10038 x
  · exact rowEval10039 x
  · exact rowEval10040 x
  · exact rowEval10041 x
  · exact rowEval10042 x
  · exact rowEval10043 x
  · exact rowEval10044 x
  · exact rowEval10045 x
  · exact rowEval10046 x
  · exact rowEval10047 x
  · exact rowEval10048 x
  · exact rowEval10049 x
  · exact rowEval10050 x
  · exact rowEval10051 x
  · exact rowEval10052 x

theorem entryEval18_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_4 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck18_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_4]

def rows18_5 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10053, row10054, row10055, row10056, row10057, row10058, row10059, row10060, row10061, row10062, row10063, row10064, row10065, row10066, row10067, row10068, row10069, row10070, row10071, row10072, row10073, row10074, row10075, row10076]

theorem entryCheck18_5 : entry18_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_5 k)) := by decide +kernel

theorem rowsSound18_5 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval10053 x
  · exact rowEval10054 x
  · exact rowEval10055 x
  · exact rowEval10056 x
  · exact rowEval10057 x
  · exact rowEval10058 x
  · exact rowEval10059 x
  · exact rowEval10060 x
  · exact rowEval10061 x
  · exact rowEval10062 x
  · exact rowEval10063 x
  · exact rowEval10064 x
  · exact rowEval10065 x
  · exact rowEval10066 x
  · exact rowEval10067 x
  · exact rowEval10068 x
  · exact rowEval10069 x
  · exact rowEval10070 x
  · exact rowEval10071 x
  · exact rowEval10072 x
  · exact rowEval10073 x
  · exact rowEval10074 x
  · exact rowEval10075 x
  · exact rowEval10076 x

theorem entryEval18_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_5 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck18_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_5]

def rows18_6 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10077, row10078, row10079, row10080, row10081, row10082, row10083, row10084, row10085, row10086, row10087, row10088, row10089, row10090, row10091, row10092, row10093, row10094, row10095, row10096, row10097, row10098, row10099, row10100]

theorem entryCheck18_6 : entry18_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_6 k)) := by decide +kernel

theorem rowsSound18_6 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval10077 x
  · exact rowEval10078 x
  · exact rowEval10079 x
  · exact rowEval10080 x
  · exact rowEval10081 x
  · exact rowEval10082 x
  · exact rowEval10083 x
  · exact rowEval10084 x
  · exact rowEval10085 x
  · exact rowEval10086 x
  · exact rowEval10087 x
  · exact rowEval10088 x
  · exact rowEval10089 x
  · exact rowEval10090 x
  · exact rowEval10091 x
  · exact rowEval10092 x
  · exact rowEval10093 x
  · exact rowEval10094 x
  · exact rowEval10095 x
  · exact rowEval10096 x
  · exact rowEval10097 x
  · exact rowEval10098 x
  · exact rowEval10099 x
  · exact rowEval10100 x

theorem entryEval18_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_6 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck18_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_6]

def rows18_7 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10101, row10102, row10103, row10104, row10105, row10106, row10107, row10108, row10109, row10110, row10111, row10112, row10113, row10114, row10115, row10116, row10117, row10118, row10119, row10120, row10121, row10122, row10123, row10124]

theorem entryCheck18_7 : entry18_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_7 k)) := by decide +kernel

theorem rowsSound18_7 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval10101 x
  · exact rowEval10102 x
  · exact rowEval10103 x
  · exact rowEval10104 x
  · exact rowEval10105 x
  · exact rowEval10106 x
  · exact rowEval10107 x
  · exact rowEval10108 x
  · exact rowEval10109 x
  · exact rowEval10110 x
  · exact rowEval10111 x
  · exact rowEval10112 x
  · exact rowEval10113 x
  · exact rowEval10114 x
  · exact rowEval10115 x
  · exact rowEval10116 x
  · exact rowEval10117 x
  · exact rowEval10118 x
  · exact rowEval10119 x
  · exact rowEval10120 x
  · exact rowEval10121 x
  · exact rowEval10122 x
  · exact rowEval10123 x
  · exact rowEval10124 x

theorem entryEval18_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_7 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck18_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_7]

def rows18_8 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10125, row10126, row10127, row10128, row10129, row10130, row10131, row10132, row10133, row10134, row10135, row10136, row10137, row10138, row10139, row10140, row10141, row10142, row10143, row10144, row10145, row10146, row10147, row10148]

theorem entryCheck18_8 : entry18_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_8 k)) := by decide +kernel

theorem rowsSound18_8 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval10125 x
  · exact rowEval10126 x
  · exact rowEval10127 x
  · exact rowEval10128 x
  · exact rowEval10129 x
  · exact rowEval10130 x
  · exact rowEval10131 x
  · exact rowEval10132 x
  · exact rowEval10133 x
  · exact rowEval10134 x
  · exact rowEval10135 x
  · exact rowEval10136 x
  · exact rowEval10137 x
  · exact rowEval10138 x
  · exact rowEval10139 x
  · exact rowEval10140 x
  · exact rowEval10141 x
  · exact rowEval10142 x
  · exact rowEval10143 x
  · exact rowEval10144 x
  · exact rowEval10145 x
  · exact rowEval10146 x
  · exact rowEval10147 x
  · exact rowEval10148 x

theorem entryEval18_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_8 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck18_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_8]

def rows18_9 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10149, row10150, row10151, row10152, row10153, row10154, row10155, row10156, row10157, row10158, row10159, row10160, row10161, row10162, row10163, row10164, row10165, row10166, row10167, row10168, row10169, row10170, row10171, row10172]

theorem entryCheck18_9 : entry18_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_9 k)) := by decide +kernel

theorem rowsSound18_9 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval10149 x
  · exact rowEval10150 x
  · exact rowEval10151 x
  · exact rowEval10152 x
  · exact rowEval10153 x
  · exact rowEval10154 x
  · exact rowEval10155 x
  · exact rowEval10156 x
  · exact rowEval10157 x
  · exact rowEval10158 x
  · exact rowEval10159 x
  · exact rowEval10160 x
  · exact rowEval10161 x
  · exact rowEval10162 x
  · exact rowEval10163 x
  · exact rowEval10164 x
  · exact rowEval10165 x
  · exact rowEval10166 x
  · exact rowEval10167 x
  · exact rowEval10168 x
  · exact rowEval10169 x
  · exact rowEval10170 x
  · exact rowEval10171 x
  · exact rowEval10172 x

theorem entryEval18_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_9 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck18_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_9]

def rows18_10 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10173, row10174, row10175, row10176, row10177, row10178, row10179, row10180, row10181, row10182, row10183, row10184, row10185, row10186, row10187, row10188, row10189, row10190, row10191, row10192, row10193, row10194, row10195, row10196]

theorem entryCheck18_10 : entry18_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_10 k)) := by decide +kernel

theorem rowsSound18_10 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval10173 x
  · exact rowEval10174 x
  · exact rowEval10175 x
  · exact rowEval10176 x
  · exact rowEval10177 x
  · exact rowEval10178 x
  · exact rowEval10179 x
  · exact rowEval10180 x
  · exact rowEval10181 x
  · exact rowEval10182 x
  · exact rowEval10183 x
  · exact rowEval10184 x
  · exact rowEval10185 x
  · exact rowEval10186 x
  · exact rowEval10187 x
  · exact rowEval10188 x
  · exact rowEval10189 x
  · exact rowEval10190 x
  · exact rowEval10191 x
  · exact rowEval10192 x
  · exact rowEval10193 x
  · exact rowEval10194 x
  · exact rowEval10195 x
  · exact rowEval10196 x

theorem entryEval18_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_10 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck18_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_10]

def rows18_11 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10197, row10198, row10199, row10200, row10201, row10202, row10203, row10204, row10205, row10206, row10207, row10208, row10209, row10210, row10211, row10212, row10213, row10214, row10215, row10216, row10217, row10218, row10219, row10220]

theorem entryCheck18_11 : entry18_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_11 k)) := by decide +kernel

theorem rowsSound18_11 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval10197 x
  · exact rowEval10198 x
  · exact rowEval10199 x
  · exact rowEval10200 x
  · exact rowEval10201 x
  · exact rowEval10202 x
  · exact rowEval10203 x
  · exact rowEval10204 x
  · exact rowEval10205 x
  · exact rowEval10206 x
  · exact rowEval10207 x
  · exact rowEval10208 x
  · exact rowEval10209 x
  · exact rowEval10210 x
  · exact rowEval10211 x
  · exact rowEval10212 x
  · exact rowEval10213 x
  · exact rowEval10214 x
  · exact rowEval10215 x
  · exact rowEval10216 x
  · exact rowEval10217 x
  · exact rowEval10218 x
  · exact rowEval10219 x
  · exact rowEval10220 x

theorem entryEval18_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_11 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck18_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_11]

def rows18_12 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10221, row10222, row10223, row10224, row10225, row10226, row10227, row10228, row10229, row10230, row10231, row10232, row10233, row10234, row10235, row10236, row10237, row10238, row10239, row10240, row10241, row10242, row10243, row10244]

theorem entryCheck18_12 : entry18_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_12 k)) := by decide +kernel

theorem rowsSound18_12 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval10221 x
  · exact rowEval10222 x
  · exact rowEval10223 x
  · exact rowEval10224 x
  · exact rowEval10225 x
  · exact rowEval10226 x
  · exact rowEval10227 x
  · exact rowEval10228 x
  · exact rowEval10229 x
  · exact rowEval10230 x
  · exact rowEval10231 x
  · exact rowEval10232 x
  · exact rowEval10233 x
  · exact rowEval10234 x
  · exact rowEval10235 x
  · exact rowEval10236 x
  · exact rowEval10237 x
  · exact rowEval10238 x
  · exact rowEval10239 x
  · exact rowEval10240 x
  · exact rowEval10241 x
  · exact rowEval10242 x
  · exact rowEval10243 x
  · exact rowEval10244 x

theorem entryEval18_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_12 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck18_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_12]

def rows18_13 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10245, row10246, row10247, row10248, row10249, row10250, row10251, row10252, row10253, row10254, row10255, row10256, row10257, row10258, row10259, row10260, row10261, row10262, row10263, row10264, row10265, row10266, row10267, row10268]

theorem entryCheck18_13 : entry18_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_13 k)) := by decide +kernel

theorem rowsSound18_13 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval10245 x
  · exact rowEval10246 x
  · exact rowEval10247 x
  · exact rowEval10248 x
  · exact rowEval10249 x
  · exact rowEval10250 x
  · exact rowEval10251 x
  · exact rowEval10252 x
  · exact rowEval10253 x
  · exact rowEval10254 x
  · exact rowEval10255 x
  · exact rowEval10256 x
  · exact rowEval10257 x
  · exact rowEval10258 x
  · exact rowEval10259 x
  · exact rowEval10260 x
  · exact rowEval10261 x
  · exact rowEval10262 x
  · exact rowEval10263 x
  · exact rowEval10264 x
  · exact rowEval10265 x
  · exact rowEval10266 x
  · exact rowEval10267 x
  · exact rowEval10268 x

theorem entryEval18_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_13 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck18_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_13]

def rows18_14 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10269, row10270, row10271, row10272, row10273, row10274, row10275, row10276, row10277, row10278, row10279, row10280, row10281, row10282, row10283, row10284, row10285, row10286, row10287, row10288, row10289, row10290, row10291, row10292]

theorem entryCheck18_14 : entry18_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_14 k)) := by decide +kernel

theorem rowsSound18_14 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval10269 x
  · exact rowEval10270 x
  · exact rowEval10271 x
  · exact rowEval10272 x
  · exact rowEval10273 x
  · exact rowEval10274 x
  · exact rowEval10275 x
  · exact rowEval10276 x
  · exact rowEval10277 x
  · exact rowEval10278 x
  · exact rowEval10279 x
  · exact rowEval10280 x
  · exact rowEval10281 x
  · exact rowEval10282 x
  · exact rowEval10283 x
  · exact rowEval10284 x
  · exact rowEval10285 x
  · exact rowEval10286 x
  · exact rowEval10287 x
  · exact rowEval10288 x
  · exact rowEval10289 x
  · exact rowEval10290 x
  · exact rowEval10291 x
  · exact rowEval10292 x

theorem entryEval18_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_14 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck18_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_14]

def rows18_15 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10293, row10294, row10295, row10296, row10297, row10298, row10299, row10300, row10301, row10302, row10303, row10304, row10305, row10306, row10307, row10308, row10309, row10310, row10311, row10312, row10313, row10314, row10315, row10316]

theorem entryCheck18_15 : entry18_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_15 k)) := by decide +kernel

theorem rowsSound18_15 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval10293 x
  · exact rowEval10294 x
  · exact rowEval10295 x
  · exact rowEval10296 x
  · exact rowEval10297 x
  · exact rowEval10298 x
  · exact rowEval10299 x
  · exact rowEval10300 x
  · exact rowEval10301 x
  · exact rowEval10302 x
  · exact rowEval10303 x
  · exact rowEval10304 x
  · exact rowEval10305 x
  · exact rowEval10306 x
  · exact rowEval10307 x
  · exact rowEval10308 x
  · exact rowEval10309 x
  · exact rowEval10310 x
  · exact rowEval10311 x
  · exact rowEval10312 x
  · exact rowEval10313 x
  · exact rowEval10314 x
  · exact rowEval10315 x
  · exact rowEval10316 x

theorem entryEval18_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_15 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck18_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_15]

def rows18_16 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10317, row10318, row10319, row10320, row10321, row10322, row10323, row10324, row10325, row10326, row10327, row10328, row10329, row10330, row10331, row10332, row10333, row10334, row10335, row10336, row10337, row10338, row10339, row10340]

theorem entryCheck18_16 : entry18_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_16 k)) := by decide +kernel

theorem rowsSound18_16 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval10317 x
  · exact rowEval10318 x
  · exact rowEval10319 x
  · exact rowEval10320 x
  · exact rowEval10321 x
  · exact rowEval10322 x
  · exact rowEval10323 x
  · exact rowEval10324 x
  · exact rowEval10325 x
  · exact rowEval10326 x
  · exact rowEval10327 x
  · exact rowEval10328 x
  · exact rowEval10329 x
  · exact rowEval10330 x
  · exact rowEval10331 x
  · exact rowEval10332 x
  · exact rowEval10333 x
  · exact rowEval10334 x
  · exact rowEval10335 x
  · exact rowEval10336 x
  · exact rowEval10337 x
  · exact rowEval10338 x
  · exact rowEval10339 x
  · exact rowEval10340 x

theorem entryEval18_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_16 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck18_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_16]

def rows18_17 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10341, row10342, row10343, row10344, row10345, row10346, row10347, row10348, row10349, row10350, row10351, row10352, row10353, row10354, row10355, row10356, row10357, row10358, row10359, row10360, row10361, row10362, row10363, row10364]

theorem entryCheck18_17 : entry18_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_17 k)) := by decide +kernel

theorem rowsSound18_17 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval10341 x
  · exact rowEval10342 x
  · exact rowEval10343 x
  · exact rowEval10344 x
  · exact rowEval10345 x
  · exact rowEval10346 x
  · exact rowEval10347 x
  · exact rowEval10348 x
  · exact rowEval10349 x
  · exact rowEval10350 x
  · exact rowEval10351 x
  · exact rowEval10352 x
  · exact rowEval10353 x
  · exact rowEval10354 x
  · exact rowEval10355 x
  · exact rowEval10356 x
  · exact rowEval10357 x
  · exact rowEval10358 x
  · exact rowEval10359 x
  · exact rowEval10360 x
  · exact rowEval10361 x
  · exact rowEval10362 x
  · exact rowEval10363 x
  · exact rowEval10364 x

theorem entryEval18_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_17 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck18_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_17]

def rows18_18 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10365, row10366, row10367, row10368, row10369, row10370, row10371, row10372, row10373, row10374, row10375, row10376, row10377, row10378, row10379, row10380, row10381, row10382, row10383, row10384, row10385, row10386, row10387, row10388]

theorem entryCheck18_18 : entry18_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form18.terms k).coefficient) (rows18_18 k)) := by decide +kernel

theorem rowsSound18_18 (k : Fin GramFunctions.Block3.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form18.terms k).tag (GramFunctions.Block3.form18.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval10365 x
  · exact rowEval10366 x
  · exact rowEval10367 x
  · exact rowEval10368 x
  · exact rowEval10369 x
  · exact rowEval10370 x
  · exact rowEval10371 x
  · exact rowEval10372 x
  · exact rowEval10373 x
  · exact rowEval10374 x
  · exact rowEval10375 x
  · exact rowEval10376 x
  · exact rowEval10377 x
  · exact rowEval10378 x
  · exact rowEval10379 x
  · exact rowEval10380 x
  · exact rowEval10381 x
  · exact rowEval10382 x
  · exact rowEval10383 x
  · exact rowEval10384 x
  · exact rowEval10385 x
  · exact rowEval10386 x
  · exact rowEval10387 x
  · exact rowEval10388 x

theorem entryEval18_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_18 (GramNormalization.eval B) = GramFunctions.Block3.form18.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck18_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form18 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_18]

end MUB6.Certificate.GramEntries.Block3

end OAI
