import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block82
import OAI.Analysis.MutuallyUnbiased.GramRows.Block97
import OAI.Analysis.MutuallyUnbiased.GramRows.Block98

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows16_0 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9381, row9382, row9383, row9384, row7430, row7431, row7432, row7433]

theorem entryCheck16_0 : entry16_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_0 k)) := by decide +kernel

theorem rowsSound16_0 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval9381 x
  · exact rowEval9382 x
  · exact rowEval9383 x
  · exact rowEval9384 x
  · exact rowEval7430 x
  · exact rowEval7431 x
  · exact rowEval7432 x
  · exact rowEval7433 x

theorem entryEval16_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_0 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck16_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_0]

def rows16_1 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9385, row9386, row9387, row9388, row7446, row7447, row7448, row7449]

theorem entryCheck16_1 : entry16_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_1 k)) := by decide +kernel

theorem rowsSound16_1 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval9385 x
  · exact rowEval9386 x
  · exact rowEval9387 x
  · exact rowEval9388 x
  · exact rowEval7446 x
  · exact rowEval7447 x
  · exact rowEval7448 x
  · exact rowEval7449 x

theorem entryEval16_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_1 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck16_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_1]

def rows16_2 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9389, row9390, row9391, row9392, row7462, row7463, row7464, row7465]

theorem entryCheck16_2 : entry16_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_2 k)) := by decide +kernel

theorem rowsSound16_2 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval9389 x
  · exact rowEval9390 x
  · exact rowEval9391 x
  · exact rowEval9392 x
  · exact rowEval7462 x
  · exact rowEval7463 x
  · exact rowEval7464 x
  · exact rowEval7465 x

theorem entryEval16_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_2 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck16_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_2]

def rows16_3 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9393, row9394, row9395, row9396, row7478, row7479, row7480, row7481]

theorem entryCheck16_3 : entry16_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_3 k)) := by decide +kernel

theorem rowsSound16_3 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval9393 x
  · exact rowEval9394 x
  · exact rowEval9395 x
  · exact rowEval9396 x
  · exact rowEval7478 x
  · exact rowEval7479 x
  · exact rowEval7480 x
  · exact rowEval7481 x

theorem entryEval16_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_3 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck16_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_3]

def rows16_4 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9397, row9398, row9399, row9400, row9401, row9402, row9403, row9404]

theorem entryCheck16_4 : entry16_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_4 k)) := by decide +kernel

theorem rowsSound16_4 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval9397 x
  · exact rowEval9398 x
  · exact rowEval9399 x
  · exact rowEval9400 x
  · exact rowEval9401 x
  · exact rowEval9402 x
  · exact rowEval9403 x
  · exact rowEval9404 x

theorem entryEval16_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_4 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck16_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_4]

def rows16_5 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9405, row9406, row9407, row9408, row9409, row9410, row9411, row9412]

theorem entryCheck16_5 : entry16_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_5 k)) := by decide +kernel

theorem rowsSound16_5 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval9405 x
  · exact rowEval9406 x
  · exact rowEval9407 x
  · exact rowEval9408 x
  · exact rowEval9409 x
  · exact rowEval9410 x
  · exact rowEval9411 x
  · exact rowEval9412 x

theorem entryEval16_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_5 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck16_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_5]

def rows16_6 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9413, row9414, row9415, row9416, row9417, row9418, row9419, row9420]

theorem entryCheck16_6 : entry16_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_6 k)) := by decide +kernel

theorem rowsSound16_6 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval9413 x
  · exact rowEval9414 x
  · exact rowEval9415 x
  · exact rowEval9416 x
  · exact rowEval9417 x
  · exact rowEval9418 x
  · exact rowEval9419 x
  · exact rowEval9420 x

theorem entryEval16_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_6 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck16_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_6]

def rows16_7 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9421, row9422, row9423, row9424, row9425, row9426, row9427, row9428]

theorem entryCheck16_7 : entry16_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_7 k)) := by decide +kernel

theorem rowsSound16_7 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval9421 x
  · exact rowEval9422 x
  · exact rowEval9423 x
  · exact rowEval9424 x
  · exact rowEval9425 x
  · exact rowEval9426 x
  · exact rowEval9427 x
  · exact rowEval9428 x

theorem entryEval16_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_7 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck16_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_7]

def rows16_8 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9429, row9430, row9431, row9432, row9433, row9434, row9435, row9436]

theorem entryCheck16_8 : entry16_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_8 k)) := by decide +kernel

theorem rowsSound16_8 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval9429 x
  · exact rowEval9430 x
  · exact rowEval9431 x
  · exact rowEval9432 x
  · exact rowEval9433 x
  · exact rowEval9434 x
  · exact rowEval9435 x
  · exact rowEval9436 x

theorem entryEval16_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_8 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck16_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_8]

def rows16_9 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9437, row9438, row9439, row9440, row9441, row9442, row9443, row9444]

theorem entryCheck16_9 : entry16_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_9 k)) := by decide +kernel

theorem rowsSound16_9 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval9437 x
  · exact rowEval9438 x
  · exact rowEval9439 x
  · exact rowEval9440 x
  · exact rowEval9441 x
  · exact rowEval9442 x
  · exact rowEval9443 x
  · exact rowEval9444 x

theorem entryEval16_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_9 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck16_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_9]

def rows16_10 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9445, row9446, row9447, row9448, row9449, row9450, row9451, row9452]

theorem entryCheck16_10 : entry16_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_10 k)) := by decide +kernel

theorem rowsSound16_10 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval9445 x
  · exact rowEval9446 x
  · exact rowEval9447 x
  · exact rowEval9448 x
  · exact rowEval9449 x
  · exact rowEval9450 x
  · exact rowEval9451 x
  · exact rowEval9452 x

theorem entryEval16_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_10 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck16_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_10]

def rows16_11 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9453, row9454, row9455, row9456, row9457, row9458, row9459, row9460]

theorem entryCheck16_11 : entry16_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_11 k)) := by decide +kernel

theorem rowsSound16_11 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval9453 x
  · exact rowEval9454 x
  · exact rowEval9455 x
  · exact rowEval9456 x
  · exact rowEval9457 x
  · exact rowEval9458 x
  · exact rowEval9459 x
  · exact rowEval9460 x

theorem entryEval16_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_11 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck16_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_11]

def rows16_12 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9461, row9462, row9463, row9464, row9465, row9466, row9467, row9468]

theorem entryCheck16_12 : entry16_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_12 k)) := by decide +kernel

theorem rowsSound16_12 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval9461 x
  · exact rowEval9462 x
  · exact rowEval9463 x
  · exact rowEval9464 x
  · exact rowEval9465 x
  · exact rowEval9466 x
  · exact rowEval9467 x
  · exact rowEval9468 x

theorem entryEval16_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_12 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck16_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_12]

def rows16_13 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9469, row9470, row9471, row9472, row9473, row9474, row9475, row9476]

theorem entryCheck16_13 : entry16_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_13 k)) := by decide +kernel

theorem rowsSound16_13 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval9469 x
  · exact rowEval9470 x
  · exact rowEval9471 x
  · exact rowEval9472 x
  · exact rowEval9473 x
  · exact rowEval9474 x
  · exact rowEval9475 x
  · exact rowEval9476 x

theorem entryEval16_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_13 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck16_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_13]

def rows16_14 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9477, row9478, row9479, row9480, row9481, row9482, row9483, row9484]

theorem entryCheck16_14 : entry16_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_14 k)) := by decide +kernel

theorem rowsSound16_14 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval9477 x
  · exact rowEval9478 x
  · exact rowEval9479 x
  · exact rowEval9480 x
  · exact rowEval9481 x
  · exact rowEval9482 x
  · exact rowEval9483 x
  · exact rowEval9484 x

theorem entryEval16_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_14 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck16_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_14]

def rows16_15 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9485, row9486, row9487, row9488, row9489, row9490, row9491, row9492]

theorem entryCheck16_15 : entry16_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_15 k)) := by decide +kernel

theorem rowsSound16_15 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval9485 x
  · exact rowEval9486 x
  · exact rowEval9487 x
  · exact rowEval9488 x
  · exact rowEval9489 x
  · exact rowEval9490 x
  · exact rowEval9491 x
  · exact rowEval9492 x

theorem entryEval16_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_15 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck16_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_15]

def rows16_16 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9493, row9494, row9495, row9496, row9497, row9498, row9499, row9500]

theorem entryCheck16_16 : entry16_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form16.terms k).coefficient) (rows16_16 k)) := by decide +kernel

theorem rowsSound16_16 (k : Fin GramFunctions.Block3.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form16.terms k).tag (GramFunctions.Block3.form16.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval9493 x
  · exact rowEval9494 x
  · exact rowEval9495 x
  · exact rowEval9496 x
  · exact rowEval9497 x
  · exact rowEval9498 x
  · exact rowEval9499 x
  · exact rowEval9500 x

theorem entryEval16_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_16 (GramNormalization.eval B) = GramFunctions.Block3.form16.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck16_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form16 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_16]

end MUB6.Certificate.GramEntries.Block3

end OAI
