import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block81

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block3.form1.size → Integer.Sparse Key := ![row7372, row7373, row7374, row7375, row7376]

theorem entryCheck1_0 : entry1_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form1.terms k).coefficient) (rows1_0 k)) := by decide +kernel

theorem rowsSound1_0 (k : Fin GramFunctions.Block3.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form1.terms k).tag (GramFunctions.Block3.form1.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7372 x
  · exact rowEval7373 x
  · exact rowEval7374 x
  · exact rowEval7375 x
  · exact rowEval7376 x

theorem entryEval1_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_0 (GramNormalization.eval B) = GramFunctions.Block3.form1.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck1_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form1 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_0]

def rows1_1 : Fin GramFunctions.Block3.form1.size → Integer.Sparse Key := ![row7377, row7378, row7379, row7380, row7381]

theorem entryCheck1_1 : entry1_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form1.terms k).coefficient) (rows1_1 k)) := by decide +kernel

theorem rowsSound1_1 (k : Fin GramFunctions.Block3.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form1.terms k).tag (GramFunctions.Block3.form1.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7377 x
  · exact rowEval7378 x
  · exact rowEval7379 x
  · exact rowEval7380 x
  · exact rowEval7381 x

theorem entryEval1_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_1 (GramNormalization.eval B) = GramFunctions.Block3.form1.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck1_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form1 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_1]

end MUB6.Certificate.GramEntries.Block3

end OAI
