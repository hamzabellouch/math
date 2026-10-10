import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block127

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block4.form0.size → Integer.Sparse Key := ![row13187, row13188, row13189, row13190, row13191, row13192, row13193, row13194, row13195, row13196, row13197, row13198, row13199, row13200, row13201, row13202, row13203, row13204]

theorem entryCheck0_0 : entry0_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form0.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form0.terms k).coefficient) (rows0_0 k)) := by decide +kernel

theorem rowsSound0_0 (k : Fin GramFunctions.Block4.form0.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows0_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form0.terms k).tag (GramFunctions.Block4.form0.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13187 x
  · exact rowEval13188 x
  · exact rowEval13189 x
  · exact rowEval13190 x
  · exact rowEval13191 x
  · exact rowEval13192 x
  · exact rowEval13193 x
  · exact rowEval13194 x
  · exact rowEval13195 x
  · exact rowEval13196 x
  · exact rowEval13197 x
  · exact rowEval13198 x
  · exact rowEval13199 x
  · exact rowEval13200 x
  · exact rowEval13201 x
  · exact rowEval13202 x
  · exact rowEval13203 x
  · exact rowEval13204 x

theorem entryEval0_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry0_0 (GramNormalization.eval B) = GramFunctions.Block4.form0.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck0_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form0 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound0_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
