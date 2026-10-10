import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block81

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block3.form0.size → Integer.Sparse Key := ![row7348, row7349, row7350, row7351, row7352, row7353, row7354, row7355, row7356, row7357, row7358, row7359, row7360, row7361, row7362, row7363, row7364, row7365, row7366, row7367, row7368, row7369, row7370, row7371]

theorem entryCheck0_0 : entry0_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form0.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form0.terms k).coefficient) (rows0_0 k)) := by decide +kernel

theorem rowsSound0_0 (k : Fin GramFunctions.Block3.form0.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows0_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form0.terms k).tag (GramFunctions.Block3.form0.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7348 x
  · exact rowEval7349 x
  · exact rowEval7350 x
  · exact rowEval7351 x
  · exact rowEval7352 x
  · exact rowEval7353 x
  · exact rowEval7354 x
  · exact rowEval7355 x
  · exact rowEval7356 x
  · exact rowEval7357 x
  · exact rowEval7358 x
  · exact rowEval7359 x
  · exact rowEval7360 x
  · exact rowEval7361 x
  · exact rowEval7362 x
  · exact rowEval7363 x
  · exact rowEval7364 x
  · exact rowEval7365 x
  · exact rowEval7366 x
  · exact rowEval7367 x
  · exact rowEval7368 x
  · exact rowEval7369 x
  · exact rowEval7370 x
  · exact rowEval7371 x

theorem entryEval0_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry0_0 (GramNormalization.eval B) = GramFunctions.Block3.form0.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck0_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form0 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound0_0]

end MUB6.Certificate.GramEntries.Block3

end OAI
