import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block106
import OAI.Analysis.MutuallyUnbiased.GramRows.Block107

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows20_0 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10589, row10590, row10591, row10592, row10593]

theorem entryCheck20_0 : entry20_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_0 k)) := by decide +kernel

theorem rowsSound20_0 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval10589 x
  · exact rowEval10590 x
  · exact rowEval10591 x
  · exact rowEval10592 x
  · exact rowEval10593 x

theorem entryEval20_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_0 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck20_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_0]

def rows20_1 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10594, row10595, row10596, row10597, row10598]

theorem entryCheck20_1 : entry20_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_1 k)) := by decide +kernel

theorem rowsSound20_1 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval10594 x
  · exact rowEval10595 x
  · exact rowEval10596 x
  · exact rowEval10597 x
  · exact rowEval10598 x

theorem entryEval20_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_1 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck20_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_1]

def rows20_2 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10599, row10600, row10601, row10602, row10603]

theorem entryCheck20_2 : entry20_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_2 k)) := by decide +kernel

theorem rowsSound20_2 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval10599 x
  · exact rowEval10600 x
  · exact rowEval10601 x
  · exact rowEval10602 x
  · exact rowEval10603 x

theorem entryEval20_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_2 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck20_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_2]

def rows20_3 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10604, row10605, row10606, row10607, row10608]

theorem entryCheck20_3 : entry20_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_3 k)) := by decide +kernel

theorem rowsSound20_3 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval10604 x
  · exact rowEval10605 x
  · exact rowEval10606 x
  · exact rowEval10607 x
  · exact rowEval10608 x

theorem entryEval20_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_3 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck20_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_3]

def rows20_4 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10609, row10610, row10611, row10612, row10613]

theorem entryCheck20_4 : entry20_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_4 k)) := by decide +kernel

theorem rowsSound20_4 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval10609 x
  · exact rowEval10610 x
  · exact rowEval10611 x
  · exact rowEval10612 x
  · exact rowEval10613 x

theorem entryEval20_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_4 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck20_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_4]

def rows20_5 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10614, row10615, row10616, row10617, row10618]

theorem entryCheck20_5 : entry20_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_5 k)) := by decide +kernel

theorem rowsSound20_5 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval10614 x
  · exact rowEval10615 x
  · exact rowEval10616 x
  · exact rowEval10617 x
  · exact rowEval10618 x

theorem entryEval20_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_5 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck20_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_5]

def rows20_6 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10619, row10620, row10621, row10622, row10623]

theorem entryCheck20_6 : entry20_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_6 k)) := by decide +kernel

theorem rowsSound20_6 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval10619 x
  · exact rowEval10620 x
  · exact rowEval10621 x
  · exact rowEval10622 x
  · exact rowEval10623 x

theorem entryEval20_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_6 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck20_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_6]

def rows20_7 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10624, row10625, row10626, row10627, row10628]

theorem entryCheck20_7 : entry20_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_7 k)) := by decide +kernel

theorem rowsSound20_7 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval10624 x
  · exact rowEval10625 x
  · exact rowEval10626 x
  · exact rowEval10627 x
  · exact rowEval10628 x

theorem entryEval20_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_7 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck20_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_7]

def rows20_8 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10629, row10630, row10631, row10632, row10633]

theorem entryCheck20_8 : entry20_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_8 k)) := by decide +kernel

theorem rowsSound20_8 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval10629 x
  · exact rowEval10630 x
  · exact rowEval10631 x
  · exact rowEval10632 x
  · exact rowEval10633 x

theorem entryEval20_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_8 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck20_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_8]

def rows20_9 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10634, row10635, row10636, row10637, row10638]

theorem entryCheck20_9 : entry20_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_9 k)) := by decide +kernel

theorem rowsSound20_9 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval10634 x
  · exact rowEval10635 x
  · exact rowEval10636 x
  · exact rowEval10637 x
  · exact rowEval10638 x

theorem entryEval20_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_9 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck20_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_9]

def rows20_10 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10639, row10640, row10641, row10642, row10643]

theorem entryCheck20_10 : entry20_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_10 k)) := by decide +kernel

theorem rowsSound20_10 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval10639 x
  · exact rowEval10640 x
  · exact rowEval10641 x
  · exact rowEval10642 x
  · exact rowEval10643 x

theorem entryEval20_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_10 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck20_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_10]

def rows20_11 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10644, row10645, row10646, row10647, row10648]

theorem entryCheck20_11 : entry20_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_11 k)) := by decide +kernel

theorem rowsSound20_11 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval10644 x
  · exact rowEval10645 x
  · exact rowEval10646 x
  · exact rowEval10647 x
  · exact rowEval10648 x

theorem entryEval20_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_11 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck20_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_11]

def rows20_12 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10649, row10650, row10651, row10652, row10653]

theorem entryCheck20_12 : entry20_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_12 k)) := by decide +kernel

theorem rowsSound20_12 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval10649 x
  · exact rowEval10650 x
  · exact rowEval10651 x
  · exact rowEval10652 x
  · exact rowEval10653 x

theorem entryEval20_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_12 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck20_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_12]

def rows20_13 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10654, row10655, row10656, row10657, row10658]

theorem entryCheck20_13 : entry20_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_13 k)) := by decide +kernel

theorem rowsSound20_13 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval10654 x
  · exact rowEval10655 x
  · exact rowEval10656 x
  · exact rowEval10657 x
  · exact rowEval10658 x

theorem entryEval20_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_13 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck20_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_13]

def rows20_14 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10659, row10660, row10661, row10662, row10663]

theorem entryCheck20_14 : entry20_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_14 k)) := by decide +kernel

theorem rowsSound20_14 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval10659 x
  · exact rowEval10660 x
  · exact rowEval10661 x
  · exact rowEval10662 x
  · exact rowEval10663 x

theorem entryEval20_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_14 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck20_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_14]

def rows20_15 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10664, row10665, row10666, row10667, row10668]

theorem entryCheck20_15 : entry20_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_15 k)) := by decide +kernel

theorem rowsSound20_15 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval10664 x
  · exact rowEval10665 x
  · exact rowEval10666 x
  · exact rowEval10667 x
  · exact rowEval10668 x

theorem entryEval20_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_15 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck20_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_15]

def rows20_16 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10669, row10670, row10671, row10672, row10673]

theorem entryCheck20_16 : entry20_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_16 k)) := by decide +kernel

theorem rowsSound20_16 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval10669 x
  · exact rowEval10670 x
  · exact rowEval10671 x
  · exact rowEval10672 x
  · exact rowEval10673 x

theorem entryEval20_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_16 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck20_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_16]

def rows20_17 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10674, row10675, row10676, row10677, row10678]

theorem entryCheck20_17 : entry20_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_17 k)) := by decide +kernel

theorem rowsSound20_17 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval10674 x
  · exact rowEval10675 x
  · exact rowEval10676 x
  · exact rowEval10677 x
  · exact rowEval10678 x

theorem entryEval20_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_17 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck20_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_17]

def rows20_18 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10679, row10680, row10681, row10682, row10683]

theorem entryCheck20_18 : entry20_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_18 k)) := by decide +kernel

theorem rowsSound20_18 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval10679 x
  · exact rowEval10680 x
  · exact rowEval10681 x
  · exact rowEval10682 x
  · exact rowEval10683 x

theorem entryEval20_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_18 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck20_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_18]

def rows20_19 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10684, row10685, row10686, row10687, row10688]

theorem entryCheck20_19 : entry20_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_19 k)) := by decide +kernel

theorem rowsSound20_19 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval10684 x
  · exact rowEval10685 x
  · exact rowEval10686 x
  · exact rowEval10687 x
  · exact rowEval10688 x

theorem entryEval20_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_19 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck20_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_19]

def rows20_20 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10689, row10690, row10691, row10692, row10693]

theorem entryCheck20_20 : entry20_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form20.terms k).coefficient) (rows20_20 k)) := by decide +kernel

theorem rowsSound20_20 (k : Fin GramFunctions.Block3.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form20.terms k).tag (GramFunctions.Block3.form20.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval10689 x
  · exact rowEval10690 x
  · exact rowEval10691 x
  · exact rowEval10692 x
  · exact rowEval10693 x

theorem entryEval20_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_20 (GramNormalization.eval B) = GramFunctions.Block3.form20.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck20_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form20 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_20]

end MUB6.Certificate.GramEntries.Block3

end OAI
