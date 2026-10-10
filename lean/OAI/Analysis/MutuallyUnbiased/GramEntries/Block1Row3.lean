import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block21
import OAI.Analysis.MutuallyUnbiased.GramRows.Block22
import OAI.Analysis.MutuallyUnbiased.GramRows.Block23

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block1.form3.size → Integer.Sparse Key := ![row778, row779, row780, row781, row782, row783, row784, row785, row786, row787, row788, row789, row790, row791]

theorem entryCheck3_0 : entry3_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form3.terms k).coefficient) (rows3_0 k)) := by decide +kernel

theorem rowsSound3_0 (k : Fin GramFunctions.Block1.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form3.terms k).tag (GramFunctions.Block1.form3.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval778 x
  · exact rowEval779 x
  · exact rowEval780 x
  · exact rowEval781 x
  · exact rowEval782 x
  · exact rowEval783 x
  · exact rowEval784 x
  · exact rowEval785 x
  · exact rowEval786 x
  · exact rowEval787 x
  · exact rowEval788 x
  · exact rowEval789 x
  · exact rowEval790 x
  · exact rowEval791 x

theorem entryEval3_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_0 (GramNormalization.eval B) = GramFunctions.Block1.form3.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck3_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form3 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_0]

def rows3_1 : Fin GramFunctions.Block1.form3.size → Integer.Sparse Key := ![row792, row793, row794, row795, row796, row797, row798, row799, row800, row801, row802, row803, row804, row805]

theorem entryCheck3_1 : entry3_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form3.terms k).coefficient) (rows3_1 k)) := by decide +kernel

theorem rowsSound3_1 (k : Fin GramFunctions.Block1.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form3.terms k).tag (GramFunctions.Block1.form3.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval792 x
  · exact rowEval793 x
  · exact rowEval794 x
  · exact rowEval795 x
  · exact rowEval796 x
  · exact rowEval797 x
  · exact rowEval798 x
  · exact rowEval799 x
  · exact rowEval800 x
  · exact rowEval801 x
  · exact rowEval802 x
  · exact rowEval803 x
  · exact rowEval804 x
  · exact rowEval805 x

theorem entryEval3_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_1 (GramNormalization.eval B) = GramFunctions.Block1.form3.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck3_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form3 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_1]

def rows3_2 : Fin GramFunctions.Block1.form3.size → Integer.Sparse Key := ![row806, row807, row808, row809, row810, row811, row812, row813, row814, row815, row816, row817, row818, row819]

theorem entryCheck3_2 : entry3_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form3.terms k).coefficient) (rows3_2 k)) := by decide +kernel

theorem rowsSound3_2 (k : Fin GramFunctions.Block1.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form3.terms k).tag (GramFunctions.Block1.form3.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval806 x
  · exact rowEval807 x
  · exact rowEval808 x
  · exact rowEval809 x
  · exact rowEval810 x
  · exact rowEval811 x
  · exact rowEval812 x
  · exact rowEval813 x
  · exact rowEval814 x
  · exact rowEval815 x
  · exact rowEval816 x
  · exact rowEval817 x
  · exact rowEval818 x
  · exact rowEval819 x

theorem entryEval3_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_2 (GramNormalization.eval B) = GramFunctions.Block1.form3.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck3_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form3 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_2]

def rows3_3 : Fin GramFunctions.Block1.form3.size → Integer.Sparse Key := ![row820, row821, row822, row823, row824, row825, row826, row827, row828, row829, row830, row831, row832, row833]

theorem entryCheck3_3 : entry3_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form3.terms k).coefficient) (rows3_3 k)) := by decide +kernel

theorem rowsSound3_3 (k : Fin GramFunctions.Block1.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form3.terms k).tag (GramFunctions.Block1.form3.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval820 x
  · exact rowEval821 x
  · exact rowEval822 x
  · exact rowEval823 x
  · exact rowEval824 x
  · exact rowEval825 x
  · exact rowEval826 x
  · exact rowEval827 x
  · exact rowEval828 x
  · exact rowEval829 x
  · exact rowEval830 x
  · exact rowEval831 x
  · exact rowEval832 x
  · exact rowEval833 x

theorem entryEval3_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_3 (GramNormalization.eval B) = GramFunctions.Block1.form3.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck3_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form3 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_3]

end MUB6.Certificate.GramEntries.Block1

end OAI
