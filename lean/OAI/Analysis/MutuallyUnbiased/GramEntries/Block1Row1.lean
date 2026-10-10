import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block17
import OAI.Analysis.MutuallyUnbiased.GramRows.Block18

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block1.form1.size → Integer.Sparse Key := ![row660, row661, row662, row663, row664, row665, row666, row667, row668, row669, row670, row671, row672, row673]

theorem entryCheck1_0 : entry1_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form1.terms k).coefficient) (rows1_0 k)) := by decide +kernel

theorem rowsSound1_0 (k : Fin GramFunctions.Block1.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form1.terms k).tag (GramFunctions.Block1.form1.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval660 x
  · exact rowEval661 x
  · exact rowEval662 x
  · exact rowEval663 x
  · exact rowEval664 x
  · exact rowEval665 x
  · exact rowEval666 x
  · exact rowEval667 x
  · exact rowEval668 x
  · exact rowEval669 x
  · exact rowEval670 x
  · exact rowEval671 x
  · exact rowEval672 x
  · exact rowEval673 x

theorem entryEval1_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_0 (GramNormalization.eval B) = GramFunctions.Block1.form1.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck1_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form1 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_0]

def rows1_1 : Fin GramFunctions.Block1.form1.size → Integer.Sparse Key := ![row674, row675, row676, row677, row678, row679, row680, row681, row682, row683, row684, row685, row686, row687]

theorem entryCheck1_1 : entry1_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form1.terms k).coefficient) (rows1_1 k)) := by decide +kernel

theorem rowsSound1_1 (k : Fin GramFunctions.Block1.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form1.terms k).tag (GramFunctions.Block1.form1.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval674 x
  · exact rowEval675 x
  · exact rowEval676 x
  · exact rowEval677 x
  · exact rowEval678 x
  · exact rowEval679 x
  · exact rowEval680 x
  · exact rowEval681 x
  · exact rowEval682 x
  · exact rowEval683 x
  · exact rowEval684 x
  · exact rowEval685 x
  · exact rowEval686 x
  · exact rowEval687 x

theorem entryEval1_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_1 (GramNormalization.eval B) = GramFunctions.Block1.form1.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck1_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form1 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_1]

end MUB6.Certificate.GramEntries.Block1

end OAI
