import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramRows.Block168

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block5.form1.size → Integer.Sparse Key := ![row18449, row18450, row18451, row18452, row18453]

theorem entryCheck1_0 : entry1_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form1.terms k).coefficient) (rows1_0 k)) := by decide +kernel

theorem rowsSound1_0 (k : Fin GramFunctions.Block5.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form1.terms k).tag (GramFunctions.Block5.form1.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18449 x
  · exact rowEval18450 x
  · exact rowEval18451 x
  · exact rowEval18452 x
  · exact rowEval18453 x

theorem entryEval1_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_0 (GramNormalization.eval B) = GramFunctions.Block5.form1.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck1_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form1 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_0]

def rows1_1 : Fin GramFunctions.Block5.form1.size → Integer.Sparse Key := ![row18454, row18455, row18456, row18457, row18458]

theorem entryCheck1_1 : entry1_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form1.terms k).coefficient) (rows1_1 k)) := by decide +kernel

theorem rowsSound1_1 (k : Fin GramFunctions.Block5.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form1.terms k).tag (GramFunctions.Block5.form1.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval18454 x
  · exact rowEval18455 x
  · exact rowEval18456 x
  · exact rowEval18457 x
  · exact rowEval18458 x

theorem entryEval1_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_1 (GramNormalization.eval B) = GramFunctions.Block5.form1.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck1_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form1 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_1]

end MUB6.Certificate.GramEntries.Block5

end OAI
