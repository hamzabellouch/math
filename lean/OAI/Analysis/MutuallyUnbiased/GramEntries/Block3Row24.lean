import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block119
import OAI.Analysis.MutuallyUnbiased.GramRows.Block120

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows24_0 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12206, row12207, row12208, row12209, row12210]

theorem entryCheck24_0 : entry24_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_0 k)) := by decide +kernel

theorem rowsSound24_0 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval12206 x
  · exact rowEval12207 x
  · exact rowEval12208 x
  · exact rowEval12209 x
  · exact rowEval12210 x

theorem entryEval24_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_0 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck24_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_0]

def rows24_1 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12211, row12212, row12213, row12214, row12215]

theorem entryCheck24_1 : entry24_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_1 k)) := by decide +kernel

theorem rowsSound24_1 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval12211 x
  · exact rowEval12212 x
  · exact rowEval12213 x
  · exact rowEval12214 x
  · exact rowEval12215 x

theorem entryEval24_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_1 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck24_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_1]

def rows24_2 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12216, row12217, row12218, row12219, row12220]

theorem entryCheck24_2 : entry24_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_2 k)) := by decide +kernel

theorem rowsSound24_2 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval12216 x
  · exact rowEval12217 x
  · exact rowEval12218 x
  · exact rowEval12219 x
  · exact rowEval12220 x

theorem entryEval24_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_2 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck24_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_2]

def rows24_3 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12221, row12222, row12223, row12224, row12225]

theorem entryCheck24_3 : entry24_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_3 k)) := by decide +kernel

theorem rowsSound24_3 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval12221 x
  · exact rowEval12222 x
  · exact rowEval12223 x
  · exact rowEval12224 x
  · exact rowEval12225 x

theorem entryEval24_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_3 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck24_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_3]

def rows24_4 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12226, row12227, row12228, row12229, row12230]

theorem entryCheck24_4 : entry24_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_4 k)) := by decide +kernel

theorem rowsSound24_4 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval12226 x
  · exact rowEval12227 x
  · exact rowEval12228 x
  · exact rowEval12229 x
  · exact rowEval12230 x

theorem entryEval24_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_4 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck24_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_4]

def rows24_5 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12231, row12232, row12233, row12234, row12235]

theorem entryCheck24_5 : entry24_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_5 k)) := by decide +kernel

theorem rowsSound24_5 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval12231 x
  · exact rowEval12232 x
  · exact rowEval12233 x
  · exact rowEval12234 x
  · exact rowEval12235 x

theorem entryEval24_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_5 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck24_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_5]

def rows24_6 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12236, row12237, row12238, row12239, row12240]

theorem entryCheck24_6 : entry24_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_6 k)) := by decide +kernel

theorem rowsSound24_6 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval12236 x
  · exact rowEval12237 x
  · exact rowEval12238 x
  · exact rowEval12239 x
  · exact rowEval12240 x

theorem entryEval24_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_6 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck24_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_6]

def rows24_7 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12241, row12242, row12243, row12244, row12245]

theorem entryCheck24_7 : entry24_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_7 k)) := by decide +kernel

theorem rowsSound24_7 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval12241 x
  · exact rowEval12242 x
  · exact rowEval12243 x
  · exact rowEval12244 x
  · exact rowEval12245 x

theorem entryEval24_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_7 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck24_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_7]

def rows24_8 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12246, row12247, row12248, row12249, row12250]

theorem entryCheck24_8 : entry24_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_8 k)) := by decide +kernel

theorem rowsSound24_8 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval12246 x
  · exact rowEval12247 x
  · exact rowEval12248 x
  · exact rowEval12249 x
  · exact rowEval12250 x

theorem entryEval24_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_8 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck24_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_8]

def rows24_9 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12251, row12252, row12253, row12254, row12255]

theorem entryCheck24_9 : entry24_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_9 k)) := by decide +kernel

theorem rowsSound24_9 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval12251 x
  · exact rowEval12252 x
  · exact rowEval12253 x
  · exact rowEval12254 x
  · exact rowEval12255 x

theorem entryEval24_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_9 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck24_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_9]

def rows24_10 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12256, row12257, row12258, row12259, row12260]

theorem entryCheck24_10 : entry24_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_10 k)) := by decide +kernel

theorem rowsSound24_10 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval12256 x
  · exact rowEval12257 x
  · exact rowEval12258 x
  · exact rowEval12259 x
  · exact rowEval12260 x

theorem entryEval24_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_10 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck24_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_10]

def rows24_11 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12261, row12262, row12263, row12264, row12265]

theorem entryCheck24_11 : entry24_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_11 k)) := by decide +kernel

theorem rowsSound24_11 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval12261 x
  · exact rowEval12262 x
  · exact rowEval12263 x
  · exact rowEval12264 x
  · exact rowEval12265 x

theorem entryEval24_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_11 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck24_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_11]

def rows24_12 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12266, row12267, row12268, row12269, row12270]

theorem entryCheck24_12 : entry24_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_12 k)) := by decide +kernel

theorem rowsSound24_12 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval12266 x
  · exact rowEval12267 x
  · exact rowEval12268 x
  · exact rowEval12269 x
  · exact rowEval12270 x

theorem entryEval24_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_12 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck24_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_12]

def rows24_13 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12271, row12272, row12273, row12274, row12275]

theorem entryCheck24_13 : entry24_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_13 k)) := by decide +kernel

theorem rowsSound24_13 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval12271 x
  · exact rowEval12272 x
  · exact rowEval12273 x
  · exact rowEval12274 x
  · exact rowEval12275 x

theorem entryEval24_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_13 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck24_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_13]

def rows24_14 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12276, row12277, row12278, row12279, row12280]

theorem entryCheck24_14 : entry24_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_14 k)) := by decide +kernel

theorem rowsSound24_14 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval12276 x
  · exact rowEval12277 x
  · exact rowEval12278 x
  · exact rowEval12279 x
  · exact rowEval12280 x

theorem entryEval24_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_14 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck24_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_14]

def rows24_15 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12281, row12282, row12283, row12284, row12285]

theorem entryCheck24_15 : entry24_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_15 k)) := by decide +kernel

theorem rowsSound24_15 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval12281 x
  · exact rowEval12282 x
  · exact rowEval12283 x
  · exact rowEval12284 x
  · exact rowEval12285 x

theorem entryEval24_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_15 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck24_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_15]

def rows24_16 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12286, row12287, row12288, row12289, row12290]

theorem entryCheck24_16 : entry24_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_16 k)) := by decide +kernel

theorem rowsSound24_16 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval12286 x
  · exact rowEval12287 x
  · exact rowEval12288 x
  · exact rowEval12289 x
  · exact rowEval12290 x

theorem entryEval24_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_16 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck24_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_16]

def rows24_17 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12291, row12292, row12293, row12294, row12295]

theorem entryCheck24_17 : entry24_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_17 k)) := by decide +kernel

theorem rowsSound24_17 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval12291 x
  · exact rowEval12292 x
  · exact rowEval12293 x
  · exact rowEval12294 x
  · exact rowEval12295 x

theorem entryEval24_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_17 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck24_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_17]

def rows24_18 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12296, row12297, row12298, row12299, row12300]

theorem entryCheck24_18 : entry24_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_18 k)) := by decide +kernel

theorem rowsSound24_18 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval12296 x
  · exact rowEval12297 x
  · exact rowEval12298 x
  · exact rowEval12299 x
  · exact rowEval12300 x

theorem entryEval24_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_18 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck24_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_18]

def rows24_19 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12301, row12302, row12303, row12304, row12305]

theorem entryCheck24_19 : entry24_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_19 k)) := by decide +kernel

theorem rowsSound24_19 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval12301 x
  · exact rowEval12302 x
  · exact rowEval12303 x
  · exact rowEval12304 x
  · exact rowEval12305 x

theorem entryEval24_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_19 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck24_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_19]

def rows24_20 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12306, row12307, row12308, row12309, row12310]

theorem entryCheck24_20 : entry24_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_20 k)) := by decide +kernel

theorem rowsSound24_20 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval12306 x
  · exact rowEval12307 x
  · exact rowEval12308 x
  · exact rowEval12309 x
  · exact rowEval12310 x

theorem entryEval24_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_20 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck24_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_20]

def rows24_21 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12311, row12312, row12313, row12314, row12315]

theorem entryCheck24_21 : entry24_21 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_21 k)) := by decide +kernel

theorem rowsSound24_21 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_21 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form21) x := by
  fin_cases k
  · exact rowEval12311 x
  · exact rowEval12312 x
  · exact rowEval12313 x
  · exact rowEval12314 x
  · exact rowEval12315 x

theorem entryEval24_21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_21 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form21 B := by
  rw [entryCheck24_21, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form21 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_21]

def rows24_22 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12316, row12317, row12318, row12319, row12320]

theorem entryCheck24_22 : entry24_22 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_22 k)) := by decide +kernel

theorem rowsSound24_22 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_22 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form22) x := by
  fin_cases k
  · exact rowEval12316 x
  · exact rowEval12317 x
  · exact rowEval12318 x
  · exact rowEval12319 x
  · exact rowEval12320 x

theorem entryEval24_22 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_22 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form22 B := by
  rw [entryCheck24_22, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form22 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_22]

def rows24_23 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12321, row12322, row12323, row12324, row12325]

theorem entryCheck24_23 : entry24_23 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_23 k)) := by decide +kernel

theorem rowsSound24_23 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_23 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form23) x := by
  fin_cases k
  · exact rowEval12321 x
  · exact rowEval12322 x
  · exact rowEval12323 x
  · exact rowEval12324 x
  · exact rowEval12325 x

theorem entryEval24_23 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_23 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form23 B := by
  rw [entryCheck24_23, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form23 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_23]

def rows24_24 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12326, row12327, row12328, row12329, row12330]

theorem entryCheck24_24 : entry24_24 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_24 k)) := by decide +kernel

theorem rowsSound24_24 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_24 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form24) x := by
  fin_cases k
  · exact rowEval12326 x
  · exact rowEval12327 x
  · exact rowEval12328 x
  · exact rowEval12329 x
  · exact rowEval12330 x

theorem entryEval24_24 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_24 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form24 B := by
  rw [entryCheck24_24, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form24 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_24]

end MUB6.Certificate.GramEntries.Block3

end OAI
