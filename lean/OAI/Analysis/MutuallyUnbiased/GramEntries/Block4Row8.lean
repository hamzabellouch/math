import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block132
import OAI.Analysis.MutuallyUnbiased.GramRows.Block133
import OAI.Analysis.MutuallyUnbiased.GramRows.Block134

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows8_0 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row13925, row13926, row13927, row13928, row13929, row13930, row13931, row13932, row13933, row13934, row13935, row13936, row13937, row13938, row13939, row13940, row13941, row13942, row13943, row13944]

theorem entryCheck8_0 : entry8_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_0 k)) := by decide +kernel

theorem rowsSound8_0 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13925 x
  · exact rowEval13926 x
  · exact rowEval13927 x
  · exact rowEval13928 x
  · exact rowEval13929 x
  · exact rowEval13930 x
  · exact rowEval13931 x
  · exact rowEval13932 x
  · exact rowEval13933 x
  · exact rowEval13934 x
  · exact rowEval13935 x
  · exact rowEval13936 x
  · exact rowEval13937 x
  · exact rowEval13938 x
  · exact rowEval13939 x
  · exact rowEval13940 x
  · exact rowEval13941 x
  · exact rowEval13942 x
  · exact rowEval13943 x
  · exact rowEval13944 x

theorem entryEval8_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_0 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck8_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_0]

def rows8_1 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row13945, row13946, row13947, row13948, row13949, row13950, row13951, row13952, row13953, row13954, row13955, row13956, row13957, row13958, row13959, row13960, row13961, row13962, row13963, row13964]

theorem entryCheck8_1 : entry8_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_1 k)) := by decide +kernel

theorem rowsSound8_1 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13945 x
  · exact rowEval13946 x
  · exact rowEval13947 x
  · exact rowEval13948 x
  · exact rowEval13949 x
  · exact rowEval13950 x
  · exact rowEval13951 x
  · exact rowEval13952 x
  · exact rowEval13953 x
  · exact rowEval13954 x
  · exact rowEval13955 x
  · exact rowEval13956 x
  · exact rowEval13957 x
  · exact rowEval13958 x
  · exact rowEval13959 x
  · exact rowEval13960 x
  · exact rowEval13961 x
  · exact rowEval13962 x
  · exact rowEval13963 x
  · exact rowEval13964 x

theorem entryEval8_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_1 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck8_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_1]

def rows8_2 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row13965, row13966, row13967, row13968, row13969, row13970, row13971, row13972, row13973, row13974, row13975, row13976, row13977, row13978, row13979, row13980, row13981, row13982, row13983, row13984]

theorem entryCheck8_2 : entry8_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_2 k)) := by decide +kernel

theorem rowsSound8_2 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval13965 x
  · exact rowEval13966 x
  · exact rowEval13967 x
  · exact rowEval13968 x
  · exact rowEval13969 x
  · exact rowEval13970 x
  · exact rowEval13971 x
  · exact rowEval13972 x
  · exact rowEval13973 x
  · exact rowEval13974 x
  · exact rowEval13975 x
  · exact rowEval13976 x
  · exact rowEval13977 x
  · exact rowEval13978 x
  · exact rowEval13979 x
  · exact rowEval13980 x
  · exact rowEval13981 x
  · exact rowEval13982 x
  · exact rowEval13983 x
  · exact rowEval13984 x

theorem entryEval8_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_2 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck8_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_2]

def rows8_3 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row13985, row13986, row13987, row13988, row13989, row13990, row13991, row13992, row13993, row13994, row13995, row13996, row13997, row13998, row13999, row14000, row14001, row14002, row14003, row14004]

theorem entryCheck8_3 : entry8_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_3 k)) := by decide +kernel

theorem rowsSound8_3 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval13985 x
  · exact rowEval13986 x
  · exact rowEval13987 x
  · exact rowEval13988 x
  · exact rowEval13989 x
  · exact rowEval13990 x
  · exact rowEval13991 x
  · exact rowEval13992 x
  · exact rowEval13993 x
  · exact rowEval13994 x
  · exact rowEval13995 x
  · exact rowEval13996 x
  · exact rowEval13997 x
  · exact rowEval13998 x
  · exact rowEval13999 x
  · exact rowEval14000 x
  · exact rowEval14001 x
  · exact rowEval14002 x
  · exact rowEval14003 x
  · exact rowEval14004 x

theorem entryEval8_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_3 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck8_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_3]

def rows8_4 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row14005, row14006, row14007, row14008, row14009, row14010, row14011, row14012, row14013, row14014, row14015, row14016, row14017, row14018, row14019, row14020, row14021, row14022, row14023, row14024]

theorem entryCheck8_4 : entry8_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_4 k)) := by decide +kernel

theorem rowsSound8_4 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval14005 x
  · exact rowEval14006 x
  · exact rowEval14007 x
  · exact rowEval14008 x
  · exact rowEval14009 x
  · exact rowEval14010 x
  · exact rowEval14011 x
  · exact rowEval14012 x
  · exact rowEval14013 x
  · exact rowEval14014 x
  · exact rowEval14015 x
  · exact rowEval14016 x
  · exact rowEval14017 x
  · exact rowEval14018 x
  · exact rowEval14019 x
  · exact rowEval14020 x
  · exact rowEval14021 x
  · exact rowEval14022 x
  · exact rowEval14023 x
  · exact rowEval14024 x

theorem entryEval8_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_4 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck8_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_4]

def rows8_5 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row14025, row14026, row14027, row14028, row14029, row14030, row14031, row14032, row14033, row14034, row14035, row14036, row14037, row14038, row14039, row14040, row14041, row14042, row14043, row14044]

theorem entryCheck8_5 : entry8_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_5 k)) := by decide +kernel

theorem rowsSound8_5 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval14025 x
  · exact rowEval14026 x
  · exact rowEval14027 x
  · exact rowEval14028 x
  · exact rowEval14029 x
  · exact rowEval14030 x
  · exact rowEval14031 x
  · exact rowEval14032 x
  · exact rowEval14033 x
  · exact rowEval14034 x
  · exact rowEval14035 x
  · exact rowEval14036 x
  · exact rowEval14037 x
  · exact rowEval14038 x
  · exact rowEval14039 x
  · exact rowEval14040 x
  · exact rowEval14041 x
  · exact rowEval14042 x
  · exact rowEval14043 x
  · exact rowEval14044 x

theorem entryEval8_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_5 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck8_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_5]

def rows8_6 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row14045, row14046, row14047, row14048, row14049, row14050, row14051, row14052, row14053, row14054, row14055, row14056, row14057, row14058, row14059, row14060, row14061, row14062, row14063, row14064]

theorem entryCheck8_6 : entry8_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_6 k)) := by decide +kernel

theorem rowsSound8_6 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval14045 x
  · exact rowEval14046 x
  · exact rowEval14047 x
  · exact rowEval14048 x
  · exact rowEval14049 x
  · exact rowEval14050 x
  · exact rowEval14051 x
  · exact rowEval14052 x
  · exact rowEval14053 x
  · exact rowEval14054 x
  · exact rowEval14055 x
  · exact rowEval14056 x
  · exact rowEval14057 x
  · exact rowEval14058 x
  · exact rowEval14059 x
  · exact rowEval14060 x
  · exact rowEval14061 x
  · exact rowEval14062 x
  · exact rowEval14063 x
  · exact rowEval14064 x

theorem entryEval8_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_6 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck8_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_6]

def rows8_7 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row14065, row14066, row14067, row14068, row14069, row14070, row14071, row14072, row14073, row14074, row14075, row14076, row14077, row14078, row14079, row14080, row14081, row14082, row14083, row14084]

theorem entryCheck8_7 : entry8_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_7 k)) := by decide +kernel

theorem rowsSound8_7 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval14065 x
  · exact rowEval14066 x
  · exact rowEval14067 x
  · exact rowEval14068 x
  · exact rowEval14069 x
  · exact rowEval14070 x
  · exact rowEval14071 x
  · exact rowEval14072 x
  · exact rowEval14073 x
  · exact rowEval14074 x
  · exact rowEval14075 x
  · exact rowEval14076 x
  · exact rowEval14077 x
  · exact rowEval14078 x
  · exact rowEval14079 x
  · exact rowEval14080 x
  · exact rowEval14081 x
  · exact rowEval14082 x
  · exact rowEval14083 x
  · exact rowEval14084 x

theorem entryEval8_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_7 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck8_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_7]

def rows8_8 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row14085, row14086, row14087, row14088, row14089, row14090, row14091, row14092, row14093, row14094, row14095, row14096, row14097, row14098, row14099, row14100, row14101, row14102, row14103, row14104]

theorem entryCheck8_8 : entry8_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_8 k)) := by decide +kernel

theorem rowsSound8_8 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval14085 x
  · exact rowEval14086 x
  · exact rowEval14087 x
  · exact rowEval14088 x
  · exact rowEval14089 x
  · exact rowEval14090 x
  · exact rowEval14091 x
  · exact rowEval14092 x
  · exact rowEval14093 x
  · exact rowEval14094 x
  · exact rowEval14095 x
  · exact rowEval14096 x
  · exact rowEval14097 x
  · exact rowEval14098 x
  · exact rowEval14099 x
  · exact rowEval14100 x
  · exact rowEval14101 x
  · exact rowEval14102 x
  · exact rowEval14103 x
  · exact rowEval14104 x

theorem entryEval8_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_8 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck8_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_8]

end MUB6.Certificate.GramEntries.Block4

end OAI
