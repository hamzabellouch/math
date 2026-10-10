import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block81
import OAI.Analysis.MutuallyUnbiased.GramRows.Block94
import OAI.Analysis.MutuallyUnbiased.GramRows.Block95

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows14_0 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row7382, row7383, row7384, row7385, row9065, row9066, row9067, row9068]

theorem entryCheck14_0 : entry14_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_0 k)) := by decide +kernel

theorem rowsSound14_0 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7382 x
  · exact rowEval7383 x
  · exact rowEval7384 x
  · exact rowEval7385 x
  · exact rowEval9065 x
  · exact rowEval9066 x
  · exact rowEval9067 x
  · exact rowEval9068 x

theorem entryEval14_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_0 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck14_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_0]

def rows14_1 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row7398, row7399, row7400, row7401, row9069, row9070, row9071, row9072]

theorem entryCheck14_1 : entry14_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_1 k)) := by decide +kernel

theorem rowsSound14_1 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7398 x
  · exact rowEval7399 x
  · exact rowEval7400 x
  · exact rowEval7401 x
  · exact rowEval9069 x
  · exact rowEval9070 x
  · exact rowEval9071 x
  · exact rowEval9072 x

theorem entryEval14_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_1 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck14_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_1]

def rows14_2 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row7414, row7415, row7416, row7417, row9073, row9074, row9075, row9076]

theorem entryCheck14_2 : entry14_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_2 k)) := by decide +kernel

theorem rowsSound14_2 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7414 x
  · exact rowEval7415 x
  · exact rowEval7416 x
  · exact rowEval7417 x
  · exact rowEval9073 x
  · exact rowEval9074 x
  · exact rowEval9075 x
  · exact rowEval9076 x

theorem entryEval14_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_2 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck14_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_2]

def rows14_3 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9077, row9078, row9079, row9080, row9081, row9082, row9083, row9084]

theorem entryCheck14_3 : entry14_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_3 k)) := by decide +kernel

theorem rowsSound14_3 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval9077 x
  · exact rowEval9078 x
  · exact rowEval9079 x
  · exact rowEval9080 x
  · exact rowEval9081 x
  · exact rowEval9082 x
  · exact rowEval9083 x
  · exact rowEval9084 x

theorem entryEval14_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_3 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck14_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_3]

def rows14_4 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9085, row9086, row9087, row9088, row9089, row9090, row9091, row9092]

theorem entryCheck14_4 : entry14_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_4 k)) := by decide +kernel

theorem rowsSound14_4 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval9085 x
  · exact rowEval9086 x
  · exact rowEval9087 x
  · exact rowEval9088 x
  · exact rowEval9089 x
  · exact rowEval9090 x
  · exact rowEval9091 x
  · exact rowEval9092 x

theorem entryEval14_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_4 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck14_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_4]

def rows14_5 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9093, row9094, row9095, row9096, row9097, row9098, row9099, row9100]

theorem entryCheck14_5 : entry14_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_5 k)) := by decide +kernel

theorem rowsSound14_5 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval9093 x
  · exact rowEval9094 x
  · exact rowEval9095 x
  · exact rowEval9096 x
  · exact rowEval9097 x
  · exact rowEval9098 x
  · exact rowEval9099 x
  · exact rowEval9100 x

theorem entryEval14_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_5 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck14_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_5]

def rows14_6 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9101, row9102, row9103, row9104, row9105, row9106, row9107, row9108]

theorem entryCheck14_6 : entry14_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_6 k)) := by decide +kernel

theorem rowsSound14_6 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval9101 x
  · exact rowEval9102 x
  · exact rowEval9103 x
  · exact rowEval9104 x
  · exact rowEval9105 x
  · exact rowEval9106 x
  · exact rowEval9107 x
  · exact rowEval9108 x

theorem entryEval14_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_6 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck14_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_6]

def rows14_7 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9109, row9110, row9111, row9112, row9113, row9114, row9115, row9116]

theorem entryCheck14_7 : entry14_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_7 k)) := by decide +kernel

theorem rowsSound14_7 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval9109 x
  · exact rowEval9110 x
  · exact rowEval9111 x
  · exact rowEval9112 x
  · exact rowEval9113 x
  · exact rowEval9114 x
  · exact rowEval9115 x
  · exact rowEval9116 x

theorem entryEval14_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_7 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck14_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_7]

def rows14_8 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9117, row9118, row9119, row9120, row9121, row9122, row9123, row9124]

theorem entryCheck14_8 : entry14_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_8 k)) := by decide +kernel

theorem rowsSound14_8 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval9117 x
  · exact rowEval9118 x
  · exact rowEval9119 x
  · exact rowEval9120 x
  · exact rowEval9121 x
  · exact rowEval9122 x
  · exact rowEval9123 x
  · exact rowEval9124 x

theorem entryEval14_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_8 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck14_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_8]

def rows14_9 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9125, row9126, row9127, row9128, row9129, row9130, row9131, row9132]

theorem entryCheck14_9 : entry14_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_9 k)) := by decide +kernel

theorem rowsSound14_9 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval9125 x
  · exact rowEval9126 x
  · exact rowEval9127 x
  · exact rowEval9128 x
  · exact rowEval9129 x
  · exact rowEval9130 x
  · exact rowEval9131 x
  · exact rowEval9132 x

theorem entryEval14_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_9 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck14_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_9]

def rows14_10 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9133, row9134, row9135, row9136, row9137, row9138, row9139, row9140]

theorem entryCheck14_10 : entry14_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_10 k)) := by decide +kernel

theorem rowsSound14_10 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval9133 x
  · exact rowEval9134 x
  · exact rowEval9135 x
  · exact rowEval9136 x
  · exact rowEval9137 x
  · exact rowEval9138 x
  · exact rowEval9139 x
  · exact rowEval9140 x

theorem entryEval14_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_10 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck14_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_10]

def rows14_11 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9141, row9142, row9143, row9144, row9145, row9146, row9147, row9148]

theorem entryCheck14_11 : entry14_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_11 k)) := by decide +kernel

theorem rowsSound14_11 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval9141 x
  · exact rowEval9142 x
  · exact rowEval9143 x
  · exact rowEval9144 x
  · exact rowEval9145 x
  · exact rowEval9146 x
  · exact rowEval9147 x
  · exact rowEval9148 x

theorem entryEval14_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_11 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck14_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_11]

def rows14_12 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9149, row9150, row9151, row9152, row9153, row9154, row9155, row9156]

theorem entryCheck14_12 : entry14_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_12 k)) := by decide +kernel

theorem rowsSound14_12 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval9149 x
  · exact rowEval9150 x
  · exact rowEval9151 x
  · exact rowEval9152 x
  · exact rowEval9153 x
  · exact rowEval9154 x
  · exact rowEval9155 x
  · exact rowEval9156 x

theorem entryEval14_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_12 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck14_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_12]

def rows14_13 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9157, row9158, row9159, row9160, row9161, row9162, row9163, row9164]

theorem entryCheck14_13 : entry14_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_13 k)) := by decide +kernel

theorem rowsSound14_13 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval9157 x
  · exact rowEval9158 x
  · exact rowEval9159 x
  · exact rowEval9160 x
  · exact rowEval9161 x
  · exact rowEval9162 x
  · exact rowEval9163 x
  · exact rowEval9164 x

theorem entryEval14_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_13 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck14_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_13]

def rows14_14 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9165, row9166, row9167, row9168, row9169, row9170, row9171, row9172]

theorem entryCheck14_14 : entry14_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form14.terms k).coefficient) (rows14_14 k)) := by decide +kernel

theorem rowsSound14_14 (k : Fin GramFunctions.Block3.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form14.terms k).tag (GramFunctions.Block3.form14.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval9165 x
  · exact rowEval9166 x
  · exact rowEval9167 x
  · exact rowEval9168 x
  · exact rowEval9169 x
  · exact rowEval9170 x
  · exact rowEval9171 x
  · exact rowEval9172 x

theorem entryEval14_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_14 (GramNormalization.eval B) = GramFunctions.Block3.form14.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck14_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form14 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_14]

end MUB6.Certificate.GramEntries.Block3

end OAI
