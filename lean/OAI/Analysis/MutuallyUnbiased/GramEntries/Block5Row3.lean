import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramRows.Block169

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block5.form3.size → Integer.Sparse Key := ![row18639, row18640, row18641, row18642, row18643]

theorem entryCheck3_0 : entry3_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form3.terms k).coefficient) (rows3_0 k)) := by decide +kernel

theorem rowsSound3_0 (k : Fin GramFunctions.Block5.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form3.terms k).tag (GramFunctions.Block5.form3.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18639 x
  · exact rowEval18640 x
  · exact rowEval18641 x
  · exact rowEval18642 x
  · exact rowEval18643 x

theorem entryEval3_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_0 (GramNormalization.eval B) = GramFunctions.Block5.form3.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck3_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form3 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_0]

def rows3_1 : Fin GramFunctions.Block5.form3.size → Integer.Sparse Key := ![row18644, row18645, row18646, row18647, row18648]

theorem entryCheck3_1 : entry3_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form3.terms k).coefficient) (rows3_1 k)) := by decide +kernel

theorem rowsSound3_1 (k : Fin GramFunctions.Block5.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form3.terms k).tag (GramFunctions.Block5.form3.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval18644 x
  · exact rowEval18645 x
  · exact rowEval18646 x
  · exact rowEval18647 x
  · exact rowEval18648 x

theorem entryEval3_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_1 (GramNormalization.eval B) = GramFunctions.Block5.form3.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck3_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form3 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_1]

def rows3_2 : Fin GramFunctions.Block5.form3.size → Integer.Sparse Key := ![row18649, row18650, row18651, row18652, row18653]

theorem entryCheck3_2 : entry3_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form3.terms k).coefficient) (rows3_2 k)) := by decide +kernel

theorem rowsSound3_2 (k : Fin GramFunctions.Block5.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form3.terms k).tag (GramFunctions.Block5.form3.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval18649 x
  · exact rowEval18650 x
  · exact rowEval18651 x
  · exact rowEval18652 x
  · exact rowEval18653 x

theorem entryEval3_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_2 (GramNormalization.eval B) = GramFunctions.Block5.form3.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck3_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form3 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_2]

def rows3_3 : Fin GramFunctions.Block5.form3.size → Integer.Sparse Key := ![row18654, row18655, row18656, row18657, row18658]

theorem entryCheck3_3 : entry3_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form3.terms k).coefficient) (rows3_3 k)) := by decide +kernel

theorem rowsSound3_3 (k : Fin GramFunctions.Block5.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form3.terms k).tag (GramFunctions.Block5.form3.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval18654 x
  · exact rowEval18655 x
  · exact rowEval18656 x
  · exact rowEval18657 x
  · exact rowEval18658 x

theorem entryEval3_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_3 (GramNormalization.eval B) = GramFunctions.Block5.form3.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck3_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form3 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_3]

end MUB6.Certificate.GramEntries.Block5

end OAI
