import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block82
import OAI.Analysis.MutuallyUnbiased.GramRows.Block83
import OAI.Analysis.MutuallyUnbiased.GramRows.Block92
import OAI.Analysis.MutuallyUnbiased.GramRows.Block93

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows12_0 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row7494, row7495, row7496, row7497, row8757, row8758, row8759, row8760]

theorem entryCheck12_0 : entry12_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_0 k)) := by decide +kernel

theorem rowsSound12_0 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7494 x
  · exact rowEval7495 x
  · exact rowEval7496 x
  · exact rowEval7497 x
  · exact rowEval8757 x
  · exact rowEval8758 x
  · exact rowEval8759 x
  · exact rowEval8760 x

theorem entryEval12_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_0 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck12_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_0]

def rows12_1 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row7510, row7511, row7512, row7513, row8761, row8762, row8763, row8764]

theorem entryCheck12_1 : entry12_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_1 k)) := by decide +kernel

theorem rowsSound12_1 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7510 x
  · exact rowEval7511 x
  · exact rowEval7512 x
  · exact rowEval7513 x
  · exact rowEval8761 x
  · exact rowEval8762 x
  · exact rowEval8763 x
  · exact rowEval8764 x

theorem entryEval12_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_1 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck12_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_1]

def rows12_2 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row7526, row7527, row7528, row7529, row8765, row8766, row8767, row8768]

theorem entryCheck12_2 : entry12_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_2 k)) := by decide +kernel

theorem rowsSound12_2 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7526 x
  · exact rowEval7527 x
  · exact rowEval7528 x
  · exact rowEval7529 x
  · exact rowEval8765 x
  · exact rowEval8766 x
  · exact rowEval8767 x
  · exact rowEval8768 x

theorem entryEval12_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_2 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck12_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_2]

def rows12_3 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row7542, row7543, row7544, row7545, row8769, row8770, row8771, row8772]

theorem entryCheck12_3 : entry12_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_3 k)) := by decide +kernel

theorem rowsSound12_3 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval7542 x
  · exact rowEval7543 x
  · exact rowEval7544 x
  · exact rowEval7545 x
  · exact rowEval8769 x
  · exact rowEval8770 x
  · exact rowEval8771 x
  · exact rowEval8772 x

theorem entryEval12_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_3 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck12_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_3]

def rows12_4 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row7558, row7559, row7560, row7561, row8773, row8774, row8775, row8776]

theorem entryCheck12_4 : entry12_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_4 k)) := by decide +kernel

theorem rowsSound12_4 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval7558 x
  · exact rowEval7559 x
  · exact rowEval7560 x
  · exact rowEval7561 x
  · exact rowEval8773 x
  · exact rowEval8774 x
  · exact rowEval8775 x
  · exact rowEval8776 x

theorem entryEval12_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_4 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck12_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_4]

def rows12_5 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8777, row8778, row8779, row8780, row8781, row8782, row8783, row8784]

theorem entryCheck12_5 : entry12_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_5 k)) := by decide +kernel

theorem rowsSound12_5 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval8777 x
  · exact rowEval8778 x
  · exact rowEval8779 x
  · exact rowEval8780 x
  · exact rowEval8781 x
  · exact rowEval8782 x
  · exact rowEval8783 x
  · exact rowEval8784 x

theorem entryEval12_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_5 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck12_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_5]

def rows12_6 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8785, row8786, row8787, row8788, row8789, row8790, row8791, row8792]

theorem entryCheck12_6 : entry12_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_6 k)) := by decide +kernel

theorem rowsSound12_6 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval8785 x
  · exact rowEval8786 x
  · exact rowEval8787 x
  · exact rowEval8788 x
  · exact rowEval8789 x
  · exact rowEval8790 x
  · exact rowEval8791 x
  · exact rowEval8792 x

theorem entryEval12_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_6 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck12_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_6]

def rows12_7 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8793, row8794, row8795, row8796, row8797, row8798, row8799, row8800]

theorem entryCheck12_7 : entry12_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_7 k)) := by decide +kernel

theorem rowsSound12_7 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval8793 x
  · exact rowEval8794 x
  · exact rowEval8795 x
  · exact rowEval8796 x
  · exact rowEval8797 x
  · exact rowEval8798 x
  · exact rowEval8799 x
  · exact rowEval8800 x

theorem entryEval12_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_7 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck12_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_7]

def rows12_8 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8801, row8802, row8803, row8804, row8805, row8806, row8807, row8808]

theorem entryCheck12_8 : entry12_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_8 k)) := by decide +kernel

theorem rowsSound12_8 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval8801 x
  · exact rowEval8802 x
  · exact rowEval8803 x
  · exact rowEval8804 x
  · exact rowEval8805 x
  · exact rowEval8806 x
  · exact rowEval8807 x
  · exact rowEval8808 x

theorem entryEval12_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_8 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck12_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_8]

def rows12_9 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8809, row8810, row8811, row8812, row8813, row8814, row8815, row8816]

theorem entryCheck12_9 : entry12_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_9 k)) := by decide +kernel

theorem rowsSound12_9 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval8809 x
  · exact rowEval8810 x
  · exact rowEval8811 x
  · exact rowEval8812 x
  · exact rowEval8813 x
  · exact rowEval8814 x
  · exact rowEval8815 x
  · exact rowEval8816 x

theorem entryEval12_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_9 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck12_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_9]

def rows12_10 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8817, row8818, row8819, row8820, row8821, row8822, row8823, row8824]

theorem entryCheck12_10 : entry12_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_10 k)) := by decide +kernel

theorem rowsSound12_10 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval8817 x
  · exact rowEval8818 x
  · exact rowEval8819 x
  · exact rowEval8820 x
  · exact rowEval8821 x
  · exact rowEval8822 x
  · exact rowEval8823 x
  · exact rowEval8824 x

theorem entryEval12_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_10 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck12_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_10]

def rows12_11 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8825, row8826, row8827, row8828, row8829, row8830, row8831, row8832]

theorem entryCheck12_11 : entry12_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_11 k)) := by decide +kernel

theorem rowsSound12_11 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval8825 x
  · exact rowEval8826 x
  · exact rowEval8827 x
  · exact rowEval8828 x
  · exact rowEval8829 x
  · exact rowEval8830 x
  · exact rowEval8831 x
  · exact rowEval8832 x

theorem entryEval12_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_11 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck12_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_11]

def rows12_12 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8833, row8834, row8835, row8836, row8837, row8838, row8839, row8840]

theorem entryCheck12_12 : entry12_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form12.terms k).coefficient) (rows12_12 k)) := by decide +kernel

theorem rowsSound12_12 (k : Fin GramFunctions.Block3.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form12.terms k).tag (GramFunctions.Block3.form12.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval8833 x
  · exact rowEval8834 x
  · exact rowEval8835 x
  · exact rowEval8836 x
  · exact rowEval8837 x
  · exact rowEval8838 x
  · exact rowEval8839 x
  · exact rowEval8840 x

theorem entryEval12_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_12 (GramNormalization.eval B) = GramFunctions.Block3.form12.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck12_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form12 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_12]

end MUB6.Certificate.GramEntries.Block3

end OAI
