import OAI.Analysis.MutuallyUnbiased.GramEntries.Block0Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramRows.Block0

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block0.form0.size → Integer.Sparse Key := ![row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23, row24, row25, row26, row27, row28, row29, row30, row31, row32, row33, row34, row35, row36, row37, row38, row39, row40, row41]

theorem entryCheck0_0 : entry0_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form0.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form0.terms k).coefficient) (rows0_0 k)) := by decide +kernel

theorem rowsSound0_0 (k : Fin GramFunctions.Block0.form0.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows0_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form0.terms k).tag (GramFunctions.Block0.form0.terms k).charge GramFunctions.Block0.form0) x := by
  fin_cases k
  · exact rowEval0 x
  · exact rowEval1 x
  · exact rowEval2 x
  · exact rowEval3 x
  · exact rowEval4 x
  · exact rowEval5 x
  · exact rowEval6 x
  · exact rowEval7 x
  · exact rowEval8 x
  · exact rowEval9 x
  · exact rowEval10 x
  · exact rowEval11 x
  · exact rowEval12 x
  · exact rowEval13 x
  · exact rowEval14 x
  · exact rowEval15 x
  · exact rowEval16 x
  · exact rowEval17 x
  · exact rowEval18 x
  · exact rowEval19 x
  · exact rowEval20 x
  · exact rowEval21 x
  · exact rowEval22 x
  · exact rowEval23 x
  · exact rowEval24 x
  · exact rowEval25 x
  · exact rowEval26 x
  · exact rowEval27 x
  · exact rowEval28 x
  · exact rowEval29 x
  · exact rowEval30 x
  · exact rowEval31 x
  · exact rowEval32 x
  · exact rowEval33 x
  · exact rowEval34 x
  · exact rowEval35 x
  · exact rowEval36 x
  · exact rowEval37 x
  · exact rowEval38 x
  · exact rowEval39 x
  · exact rowEval40 x
  · exact rowEval41 x

theorem entryEval0_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry0_0 (GramNormalization.eval B) = GramFunctions.Block0.form0.mixedGram GramFunctions.Block0.form0 B := by
  rw [entryCheck0_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form0 GramFunctions.Block0.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound0_0]

end MUB6.Certificate.GramEntries.Block0

end OAI
