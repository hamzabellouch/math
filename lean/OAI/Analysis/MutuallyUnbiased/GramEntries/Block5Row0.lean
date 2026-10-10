import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramRows.Block167
import OAI.Analysis.MutuallyUnbiased.GramRows.Block168

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block5.form0.size → Integer.Sparse Key := ![row18429, row18430, row18431, row18432, row18433, row18434, row18435, row18436, row18437, row18438, row18439, row18440, row18441, row18442, row18443, row18444, row18445, row18446, row18447, row18448]

theorem entryCheck0_0 : entry0_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form0.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form0.terms k).coefficient) (rows0_0 k)) := by decide +kernel

theorem rowsSound0_0 (k : Fin GramFunctions.Block5.form0.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows0_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form0.terms k).tag (GramFunctions.Block5.form0.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18429 x
  · exact rowEval18430 x
  · exact rowEval18431 x
  · exact rowEval18432 x
  · exact rowEval18433 x
  · exact rowEval18434 x
  · exact rowEval18435 x
  · exact rowEval18436 x
  · exact rowEval18437 x
  · exact rowEval18438 x
  · exact rowEval18439 x
  · exact rowEval18440 x
  · exact rowEval18441 x
  · exact rowEval18442 x
  · exact rowEval18443 x
  · exact rowEval18444 x
  · exact rowEval18445 x
  · exact rowEval18446 x
  · exact rowEval18447 x
  · exact rowEval18448 x

theorem entryEval0_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry0_0 (GramNormalization.eval B) = GramFunctions.Block5.form0.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck0_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form0 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound0_0]

end MUB6.Certificate.GramEntries.Block5

end OAI
