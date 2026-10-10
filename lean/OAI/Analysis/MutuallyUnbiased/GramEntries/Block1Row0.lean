import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block16
import OAI.Analysis.MutuallyUnbiased.GramRows.Block17

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block1.form0.size → Integer.Sparse Key := ![row630, row631, row632, row633, row634, row635, row636, row637, row638, row639, row640, row641, row642, row643, row644, row645, row646, row647, row648, row649, row650, row651, row652, row653, row654, row655, row656, row657, row658, row659]

theorem entryCheck0_0 : entry0_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form0.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form0.terms k).coefficient) (rows0_0 k)) := by decide +kernel

theorem rowsSound0_0 (k : Fin GramFunctions.Block1.form0.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows0_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form0.terms k).tag (GramFunctions.Block1.form0.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval630 x
  · exact rowEval631 x
  · exact rowEval632 x
  · exact rowEval633 x
  · exact rowEval634 x
  · exact rowEval635 x
  · exact rowEval636 x
  · exact rowEval637 x
  · exact rowEval638 x
  · exact rowEval639 x
  · exact rowEval640 x
  · exact rowEval641 x
  · exact rowEval642 x
  · exact rowEval643 x
  · exact rowEval644 x
  · exact rowEval645 x
  · exact rowEval646 x
  · exact rowEval647 x
  · exact rowEval648 x
  · exact rowEval649 x
  · exact rowEval650 x
  · exact rowEval651 x
  · exact rowEval652 x
  · exact rowEval653 x
  · exact rowEval654 x
  · exact rowEval655 x
  · exact rowEval656 x
  · exact rowEval657 x
  · exact rowEval658 x
  · exact rowEval659 x

theorem entryEval0_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry0_0 (GramNormalization.eval B) = GramFunctions.Block1.form0.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck0_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form0 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound0_0]

end MUB6.Certificate.GramEntries.Block1

end OAI
