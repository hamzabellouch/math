import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramRows.Block174
import OAI.Analysis.MutuallyUnbiased.GramRows.Block175

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows9_0 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19284, row19285, row19286, row19287, row19288, row19289, row19290, row19291, row19292, row19293]

theorem entryCheck9_0 : entry9_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_0 k)) := by decide +kernel

theorem rowsSound9_0 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval19284 x
  · exact rowEval19285 x
  · exact rowEval19286 x
  · exact rowEval19287 x
  · exact rowEval19288 x
  · exact rowEval19289 x
  · exact rowEval19290 x
  · exact rowEval19291 x
  · exact rowEval19292 x
  · exact rowEval19293 x

theorem entryEval9_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_0 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck9_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_0]

def rows9_1 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19294, row19295, row19296, row19297, row19298, row19299, row19300, row19301, row19302, row19303]

theorem entryCheck9_1 : entry9_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_1 k)) := by decide +kernel

theorem rowsSound9_1 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval19294 x
  · exact rowEval19295 x
  · exact rowEval19296 x
  · exact rowEval19297 x
  · exact rowEval19298 x
  · exact rowEval19299 x
  · exact rowEval19300 x
  · exact rowEval19301 x
  · exact rowEval19302 x
  · exact rowEval19303 x

theorem entryEval9_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_1 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck9_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_1]

def rows9_2 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19304, row19305, row19306, row19307, row19308, row19309, row19310, row19311, row19312, row19313]

theorem entryCheck9_2 : entry9_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_2 k)) := by decide +kernel

theorem rowsSound9_2 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval19304 x
  · exact rowEval19305 x
  · exact rowEval19306 x
  · exact rowEval19307 x
  · exact rowEval19308 x
  · exact rowEval19309 x
  · exact rowEval19310 x
  · exact rowEval19311 x
  · exact rowEval19312 x
  · exact rowEval19313 x

theorem entryEval9_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_2 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck9_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_2]

def rows9_3 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19314, row19315, row19316, row19317, row19318, row19319, row19320, row19321, row19322, row19323]

theorem entryCheck9_3 : entry9_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_3 k)) := by decide +kernel

theorem rowsSound9_3 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval19314 x
  · exact rowEval19315 x
  · exact rowEval19316 x
  · exact rowEval19317 x
  · exact rowEval19318 x
  · exact rowEval19319 x
  · exact rowEval19320 x
  · exact rowEval19321 x
  · exact rowEval19322 x
  · exact rowEval19323 x

theorem entryEval9_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_3 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck9_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_3]

def rows9_4 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19324, row19325, row19326, row19327, row19328, row19329, row19330, row19331, row19332, row19333]

theorem entryCheck9_4 : entry9_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_4 k)) := by decide +kernel

theorem rowsSound9_4 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval19324 x
  · exact rowEval19325 x
  · exact rowEval19326 x
  · exact rowEval19327 x
  · exact rowEval19328 x
  · exact rowEval19329 x
  · exact rowEval19330 x
  · exact rowEval19331 x
  · exact rowEval19332 x
  · exact rowEval19333 x

theorem entryEval9_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_4 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck9_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_4]

def rows9_5 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19334, row19335, row19336, row19337, row19338, row19339, row19340, row19341, row19342, row19343]

theorem entryCheck9_5 : entry9_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_5 k)) := by decide +kernel

theorem rowsSound9_5 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form5) x := by
  fin_cases k
  · exact rowEval19334 x
  · exact rowEval19335 x
  · exact rowEval19336 x
  · exact rowEval19337 x
  · exact rowEval19338 x
  · exact rowEval19339 x
  · exact rowEval19340 x
  · exact rowEval19341 x
  · exact rowEval19342 x
  · exact rowEval19343 x

theorem entryEval9_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_5 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form5 B := by
  rw [entryCheck9_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_5]

def rows9_6 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19344, row19345, row19346, row19347, row19348, row19349, row19350, row19351, row19352, row19353]

theorem entryCheck9_6 : entry9_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_6 k)) := by decide +kernel

theorem rowsSound9_6 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form6) x := by
  fin_cases k
  · exact rowEval19344 x
  · exact rowEval19345 x
  · exact rowEval19346 x
  · exact rowEval19347 x
  · exact rowEval19348 x
  · exact rowEval19349 x
  · exact rowEval19350 x
  · exact rowEval19351 x
  · exact rowEval19352 x
  · exact rowEval19353 x

theorem entryEval9_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_6 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form6 B := by
  rw [entryCheck9_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_6]

def rows9_7 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19354, row19355, row19356, row19357, row19358, row19359, row19360, row19361, row19362, row19363]

theorem entryCheck9_7 : entry9_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_7 k)) := by decide +kernel

theorem rowsSound9_7 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form7) x := by
  fin_cases k
  · exact rowEval19354 x
  · exact rowEval19355 x
  · exact rowEval19356 x
  · exact rowEval19357 x
  · exact rowEval19358 x
  · exact rowEval19359 x
  · exact rowEval19360 x
  · exact rowEval19361 x
  · exact rowEval19362 x
  · exact rowEval19363 x

theorem entryEval9_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_7 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form7 B := by
  rw [entryCheck9_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_7]

def rows9_8 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19364, row19365, row19366, row19367, row19368, row19369, row19370, row19371, row19372, row19373]

theorem entryCheck9_8 : entry9_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_8 k)) := by decide +kernel

theorem rowsSound9_8 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form8) x := by
  fin_cases k
  · exact rowEval19364 x
  · exact rowEval19365 x
  · exact rowEval19366 x
  · exact rowEval19367 x
  · exact rowEval19368 x
  · exact rowEval19369 x
  · exact rowEval19370 x
  · exact rowEval19371 x
  · exact rowEval19372 x
  · exact rowEval19373 x

theorem entryEval9_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_8 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form8 B := by
  rw [entryCheck9_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_8]

def rows9_9 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19374, row19375, row19376, row19377, row19378, row19379, row19380, row19381, row19382, row19383]

theorem entryCheck9_9 : entry9_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_9 k)) := by decide +kernel

theorem rowsSound9_9 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form9) x := by
  fin_cases k
  · exact rowEval19374 x
  · exact rowEval19375 x
  · exact rowEval19376 x
  · exact rowEval19377 x
  · exact rowEval19378 x
  · exact rowEval19379 x
  · exact rowEval19380 x
  · exact rowEval19381 x
  · exact rowEval19382 x
  · exact rowEval19383 x

theorem entryEval9_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_9 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form9 B := by
  rw [entryCheck9_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_9]

end MUB6.Certificate.GramEntries.Block5

end OAI
