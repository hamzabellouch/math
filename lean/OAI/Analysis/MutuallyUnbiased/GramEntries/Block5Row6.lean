import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramRows.Block171
import OAI.Analysis.MutuallyUnbiased.GramRows.Block172
import OAI.Analysis.MutuallyUnbiased.GramRows.Block173

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows6_0 : Fin GramFunctions.Block5.form6.size → Integer.Sparse Key := ![row18939, row18940, row18941, row18942, row18943, row18944, row18945, row18946, row18947, row18948, row18949, row18950, row18951, row18952, row18953, row18954, row18955, row18956, row18957, row18958]

theorem entryCheck6_0 : entry6_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_0 k)) := by decide +kernel

theorem rowsSound6_0 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18939 x
  · exact rowEval18940 x
  · exact rowEval18941 x
  · exact rowEval18942 x
  · exact rowEval18943 x
  · exact rowEval18944 x
  · exact rowEval18945 x
  · exact rowEval18946 x
  · exact rowEval18947 x
  · exact rowEval18948 x
  · exact rowEval18949 x
  · exact rowEval18950 x
  · exact rowEval18951 x
  · exact rowEval18952 x
  · exact rowEval18953 x
  · exact rowEval18954 x
  · exact rowEval18955 x
  · exact rowEval18956 x
  · exact rowEval18957 x
  · exact rowEval18958 x

theorem entryEval6_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_0 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck6_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_0]

def rows6_1 : Fin GramFunctions.Block5.form6.size → Integer.Sparse Key := ![row18959, row18960, row18961, row18962, row18963, row18964, row18965, row18966, row18967, row18968, row18969, row18970, row18971, row18972, row18973, row18974, row18975, row18976, row18977, row18978]

theorem entryCheck6_1 : entry6_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_1 k)) := by decide +kernel

theorem rowsSound6_1 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval18959 x
  · exact rowEval18960 x
  · exact rowEval18961 x
  · exact rowEval18962 x
  · exact rowEval18963 x
  · exact rowEval18964 x
  · exact rowEval18965 x
  · exact rowEval18966 x
  · exact rowEval18967 x
  · exact rowEval18968 x
  · exact rowEval18969 x
  · exact rowEval18970 x
  · exact rowEval18971 x
  · exact rowEval18972 x
  · exact rowEval18973 x
  · exact rowEval18974 x
  · exact rowEval18975 x
  · exact rowEval18976 x
  · exact rowEval18977 x
  · exact rowEval18978 x

theorem entryEval6_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_1 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck6_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_1]

def rows6_2 : Fin GramFunctions.Block5.form6.size → Integer.Sparse Key := ![row18979, row18980, row18981, row18982, row18983, row18984, row18985, row18986, row18987, row18988, row18989, row18990, row18991, row18992, row18993, row18994, row18995, row18996, row18997, row18998]

theorem entryCheck6_2 : entry6_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_2 k)) := by decide +kernel

theorem rowsSound6_2 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval18979 x
  · exact rowEval18980 x
  · exact rowEval18981 x
  · exact rowEval18982 x
  · exact rowEval18983 x
  · exact rowEval18984 x
  · exact rowEval18985 x
  · exact rowEval18986 x
  · exact rowEval18987 x
  · exact rowEval18988 x
  · exact rowEval18989 x
  · exact rowEval18990 x
  · exact rowEval18991 x
  · exact rowEval18992 x
  · exact rowEval18993 x
  · exact rowEval18994 x
  · exact rowEval18995 x
  · exact rowEval18996 x
  · exact rowEval18997 x
  · exact rowEval18998 x

theorem entryEval6_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_2 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck6_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_2]

def rows6_3 : Fin GramFunctions.Block5.form6.size → Integer.Sparse Key := ![row18999, row19000, row19001, row19002, row19003, row19004, row19005, row19006, row19007, row19008, row19009, row19010, row19011, row19012, row19013, row19014, row19015, row19016, row19017, row19018]

theorem entryCheck6_3 : entry6_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_3 k)) := by decide +kernel

theorem rowsSound6_3 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval18999 x
  · exact rowEval19000 x
  · exact rowEval19001 x
  · exact rowEval19002 x
  · exact rowEval19003 x
  · exact rowEval19004 x
  · exact rowEval19005 x
  · exact rowEval19006 x
  · exact rowEval19007 x
  · exact rowEval19008 x
  · exact rowEval19009 x
  · exact rowEval19010 x
  · exact rowEval19011 x
  · exact rowEval19012 x
  · exact rowEval19013 x
  · exact rowEval19014 x
  · exact rowEval19015 x
  · exact rowEval19016 x
  · exact rowEval19017 x
  · exact rowEval19018 x

theorem entryEval6_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_3 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck6_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_3]

def rows6_4 : Fin GramFunctions.Block5.form6.size → Integer.Sparse Key := ![row19019, row19020, row19021, row19022, row19023, row19024, row19025, row19026, row19027, row19028, row19029, row19030, row19031, row19032, row19033, row19034, row19035, row19036, row19037, row19038]

theorem entryCheck6_4 : entry6_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_4 k)) := by decide +kernel

theorem rowsSound6_4 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval19019 x
  · exact rowEval19020 x
  · exact rowEval19021 x
  · exact rowEval19022 x
  · exact rowEval19023 x
  · exact rowEval19024 x
  · exact rowEval19025 x
  · exact rowEval19026 x
  · exact rowEval19027 x
  · exact rowEval19028 x
  · exact rowEval19029 x
  · exact rowEval19030 x
  · exact rowEval19031 x
  · exact rowEval19032 x
  · exact rowEval19033 x
  · exact rowEval19034 x
  · exact rowEval19035 x
  · exact rowEval19036 x
  · exact rowEval19037 x
  · exact rowEval19038 x

theorem entryEval6_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_4 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck6_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_4]

def rows6_5 : Fin GramFunctions.Block5.form6.size → Integer.Sparse Key := ![row19039, row19040, row19041, row19042, row19043, row19044, row19045, row19046, row19047, row19048, row19049, row19050, row19051, row19052, row19053, row19054, row19055, row19056, row19057, row19058]

theorem entryCheck6_5 : entry6_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_5 k)) := by decide +kernel

theorem rowsSound6_5 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form5) x := by
  fin_cases k
  · exact rowEval19039 x
  · exact rowEval19040 x
  · exact rowEval19041 x
  · exact rowEval19042 x
  · exact rowEval19043 x
  · exact rowEval19044 x
  · exact rowEval19045 x
  · exact rowEval19046 x
  · exact rowEval19047 x
  · exact rowEval19048 x
  · exact rowEval19049 x
  · exact rowEval19050 x
  · exact rowEval19051 x
  · exact rowEval19052 x
  · exact rowEval19053 x
  · exact rowEval19054 x
  · exact rowEval19055 x
  · exact rowEval19056 x
  · exact rowEval19057 x
  · exact rowEval19058 x

theorem entryEval6_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_5 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form5 B := by
  rw [entryCheck6_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_5]

def rows6_6 : Fin GramFunctions.Block5.form6.size → Integer.Sparse Key := ![row19059, row19060, row19061, row19062, row19063, row19064, row19065, row19066, row19067, row19068, row19069, row19070, row19071, row19072, row19073, row19074, row19075, row19076, row19077, row19078]

theorem entryCheck6_6 : entry6_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_6 k)) := by decide +kernel

theorem rowsSound6_6 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form6) x := by
  fin_cases k
  · exact rowEval19059 x
  · exact rowEval19060 x
  · exact rowEval19061 x
  · exact rowEval19062 x
  · exact rowEval19063 x
  · exact rowEval19064 x
  · exact rowEval19065 x
  · exact rowEval19066 x
  · exact rowEval19067 x
  · exact rowEval19068 x
  · exact rowEval19069 x
  · exact rowEval19070 x
  · exact rowEval19071 x
  · exact rowEval19072 x
  · exact rowEval19073 x
  · exact rowEval19074 x
  · exact rowEval19075 x
  · exact rowEval19076 x
  · exact rowEval19077 x
  · exact rowEval19078 x

theorem entryEval6_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_6 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form6 B := by
  rw [entryCheck6_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_6]

end MUB6.Certificate.GramEntries.Block5

end OAI
