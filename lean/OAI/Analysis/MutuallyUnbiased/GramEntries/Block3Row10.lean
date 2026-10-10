import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block90
import OAI.Analysis.MutuallyUnbiased.GramRows.Block91

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows10_0 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8485, row8486, row8487, row8488, row8489, row8490, row8491, row8492, row8493, row8494, row8495, row8496, row8497, row8498, row8499, row8500]

theorem entryCheck10_0 : entry10_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_0 k)) := by decide +kernel

theorem rowsSound10_0 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval8485 x
  · exact rowEval8486 x
  · exact rowEval8487 x
  · exact rowEval8488 x
  · exact rowEval8489 x
  · exact rowEval8490 x
  · exact rowEval8491 x
  · exact rowEval8492 x
  · exact rowEval8493 x
  · exact rowEval8494 x
  · exact rowEval8495 x
  · exact rowEval8496 x
  · exact rowEval8497 x
  · exact rowEval8498 x
  · exact rowEval8499 x
  · exact rowEval8500 x

theorem entryEval10_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_0 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck10_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_0]

def rows10_1 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8501, row8502, row8503, row8504, row8505, row8506, row8507, row8508, row8509, row8510, row8511, row8512, row8513, row8514, row8515, row8516]

theorem entryCheck10_1 : entry10_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_1 k)) := by decide +kernel

theorem rowsSound10_1 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval8501 x
  · exact rowEval8502 x
  · exact rowEval8503 x
  · exact rowEval8504 x
  · exact rowEval8505 x
  · exact rowEval8506 x
  · exact rowEval8507 x
  · exact rowEval8508 x
  · exact rowEval8509 x
  · exact rowEval8510 x
  · exact rowEval8511 x
  · exact rowEval8512 x
  · exact rowEval8513 x
  · exact rowEval8514 x
  · exact rowEval8515 x
  · exact rowEval8516 x

theorem entryEval10_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_1 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck10_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_1]

def rows10_2 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8517, row8518, row8519, row8520, row8521, row8522, row8523, row8524, row8525, row8526, row8527, row8528, row8529, row8530, row8531, row8532]

theorem entryCheck10_2 : entry10_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_2 k)) := by decide +kernel

theorem rowsSound10_2 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval8517 x
  · exact rowEval8518 x
  · exact rowEval8519 x
  · exact rowEval8520 x
  · exact rowEval8521 x
  · exact rowEval8522 x
  · exact rowEval8523 x
  · exact rowEval8524 x
  · exact rowEval8525 x
  · exact rowEval8526 x
  · exact rowEval8527 x
  · exact rowEval8528 x
  · exact rowEval8529 x
  · exact rowEval8530 x
  · exact rowEval8531 x
  · exact rowEval8532 x

theorem entryEval10_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_2 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck10_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_2]

def rows10_3 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8533, row8534, row8535, row8536, row8537, row8538, row8539, row8540, row8541, row8542, row8543, row8544, row8545, row8546, row8547, row8548]

theorem entryCheck10_3 : entry10_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_3 k)) := by decide +kernel

theorem rowsSound10_3 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval8533 x
  · exact rowEval8534 x
  · exact rowEval8535 x
  · exact rowEval8536 x
  · exact rowEval8537 x
  · exact rowEval8538 x
  · exact rowEval8539 x
  · exact rowEval8540 x
  · exact rowEval8541 x
  · exact rowEval8542 x
  · exact rowEval8543 x
  · exact rowEval8544 x
  · exact rowEval8545 x
  · exact rowEval8546 x
  · exact rowEval8547 x
  · exact rowEval8548 x

theorem entryEval10_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_3 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck10_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_3]

def rows10_4 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8549, row8550, row8551, row8552, row8553, row8554, row8555, row8556, row8557, row8558, row8559, row8560, row8561, row8562, row8563, row8564]

theorem entryCheck10_4 : entry10_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_4 k)) := by decide +kernel

theorem rowsSound10_4 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval8549 x
  · exact rowEval8550 x
  · exact rowEval8551 x
  · exact rowEval8552 x
  · exact rowEval8553 x
  · exact rowEval8554 x
  · exact rowEval8555 x
  · exact rowEval8556 x
  · exact rowEval8557 x
  · exact rowEval8558 x
  · exact rowEval8559 x
  · exact rowEval8560 x
  · exact rowEval8561 x
  · exact rowEval8562 x
  · exact rowEval8563 x
  · exact rowEval8564 x

theorem entryEval10_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_4 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck10_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_4]

def rows10_5 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8565, row8566, row8567, row8568, row8569, row8570, row8571, row8572, row8573, row8574, row8575, row8576, row8577, row8578, row8579, row8580]

theorem entryCheck10_5 : entry10_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_5 k)) := by decide +kernel

theorem rowsSound10_5 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval8565 x
  · exact rowEval8566 x
  · exact rowEval8567 x
  · exact rowEval8568 x
  · exact rowEval8569 x
  · exact rowEval8570 x
  · exact rowEval8571 x
  · exact rowEval8572 x
  · exact rowEval8573 x
  · exact rowEval8574 x
  · exact rowEval8575 x
  · exact rowEval8576 x
  · exact rowEval8577 x
  · exact rowEval8578 x
  · exact rowEval8579 x
  · exact rowEval8580 x

theorem entryEval10_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_5 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck10_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_5]

def rows10_6 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8581, row8582, row8583, row8584, row8585, row8586, row8587, row8588, row8589, row8590, row8591, row8592, row8593, row8594, row8595, row8596]

theorem entryCheck10_6 : entry10_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_6 k)) := by decide +kernel

theorem rowsSound10_6 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval8581 x
  · exact rowEval8582 x
  · exact rowEval8583 x
  · exact rowEval8584 x
  · exact rowEval8585 x
  · exact rowEval8586 x
  · exact rowEval8587 x
  · exact rowEval8588 x
  · exact rowEval8589 x
  · exact rowEval8590 x
  · exact rowEval8591 x
  · exact rowEval8592 x
  · exact rowEval8593 x
  · exact rowEval8594 x
  · exact rowEval8595 x
  · exact rowEval8596 x

theorem entryEval10_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_6 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck10_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_6]

def rows10_7 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8597, row8598, row8599, row8600, row8601, row8602, row8603, row8604, row8605, row8606, row8607, row8608, row8609, row8610, row8611, row8612]

theorem entryCheck10_7 : entry10_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_7 k)) := by decide +kernel

theorem rowsSound10_7 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval8597 x
  · exact rowEval8598 x
  · exact rowEval8599 x
  · exact rowEval8600 x
  · exact rowEval8601 x
  · exact rowEval8602 x
  · exact rowEval8603 x
  · exact rowEval8604 x
  · exact rowEval8605 x
  · exact rowEval8606 x
  · exact rowEval8607 x
  · exact rowEval8608 x
  · exact rowEval8609 x
  · exact rowEval8610 x
  · exact rowEval8611 x
  · exact rowEval8612 x

theorem entryEval10_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_7 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck10_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_7]

def rows10_8 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8613, row8614, row8615, row8616, row8617, row8618, row8619, row8620, row8621, row8622, row8623, row8624, row8625, row8626, row8627, row8628]

theorem entryCheck10_8 : entry10_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_8 k)) := by decide +kernel

theorem rowsSound10_8 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval8613 x
  · exact rowEval8614 x
  · exact rowEval8615 x
  · exact rowEval8616 x
  · exact rowEval8617 x
  · exact rowEval8618 x
  · exact rowEval8619 x
  · exact rowEval8620 x
  · exact rowEval8621 x
  · exact rowEval8622 x
  · exact rowEval8623 x
  · exact rowEval8624 x
  · exact rowEval8625 x
  · exact rowEval8626 x
  · exact rowEval8627 x
  · exact rowEval8628 x

theorem entryEval10_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_8 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck10_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_8]

def rows10_9 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8629, row8630, row8631, row8632, row8633, row8634, row8635, row8636, row8637, row8638, row8639, row8640, row8641, row8642, row8643, row8644]

theorem entryCheck10_9 : entry10_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_9 k)) := by decide +kernel

theorem rowsSound10_9 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval8629 x
  · exact rowEval8630 x
  · exact rowEval8631 x
  · exact rowEval8632 x
  · exact rowEval8633 x
  · exact rowEval8634 x
  · exact rowEval8635 x
  · exact rowEval8636 x
  · exact rowEval8637 x
  · exact rowEval8638 x
  · exact rowEval8639 x
  · exact rowEval8640 x
  · exact rowEval8641 x
  · exact rowEval8642 x
  · exact rowEval8643 x
  · exact rowEval8644 x

theorem entryEval10_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_9 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck10_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_9]

def rows10_10 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8645, row8646, row8647, row8648, row8649, row8650, row8651, row8652, row8653, row8654, row8655, row8656, row8657, row8658, row8659, row8660]

theorem entryCheck10_10 : entry10_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form10.terms k).coefficient) (rows10_10 k)) := by decide +kernel

theorem rowsSound10_10 (k : Fin GramFunctions.Block3.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form10.terms k).tag (GramFunctions.Block3.form10.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval8645 x
  · exact rowEval8646 x
  · exact rowEval8647 x
  · exact rowEval8648 x
  · exact rowEval8649 x
  · exact rowEval8650 x
  · exact rowEval8651 x
  · exact rowEval8652 x
  · exact rowEval8653 x
  · exact rowEval8654 x
  · exact rowEval8655 x
  · exact rowEval8656 x
  · exact rowEval8657 x
  · exact rowEval8658 x
  · exact rowEval8659 x
  · exact rowEval8660 x

theorem entryEval10_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_10 (GramNormalization.eval B) = GramFunctions.Block3.form10.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck10_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form10 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_10]

end MUB6.Certificate.GramEntries.Block3

end OAI
