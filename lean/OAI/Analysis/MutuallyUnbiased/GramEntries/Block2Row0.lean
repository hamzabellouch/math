import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramRows.Block64

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block2.form0.size → Integer.Sparse Key := ![row5148, row5149, row5150, row5151, row5152, row5153, row5154, row5155, row5156, row5157, row5158, row5159, row5160, row5161, row5162, row5163, row5164, row5165, row5166, row5167, row5168, row5169, row5170, row5171, row5172, row5173, row5174, row5175, row5176, row5177, row5178, row5179, row5180, row5181, row5182, row5183, row5184, row5185, row5186, row5187]

theorem entryCheck0_0 : entry0_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form0.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form0.terms k).coefficient) (rows0_0 k)) := by decide +kernel

theorem rowsSound0_0 (k : Fin GramFunctions.Block2.form0.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows0_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form0.terms k).tag (GramFunctions.Block2.form0.terms k).charge GramFunctions.Block2.form0) x := by
  fin_cases k
  · exact rowEval5148 x
  · exact rowEval5149 x
  · exact rowEval5150 x
  · exact rowEval5151 x
  · exact rowEval5152 x
  · exact rowEval5153 x
  · exact rowEval5154 x
  · exact rowEval5155 x
  · exact rowEval5156 x
  · exact rowEval5157 x
  · exact rowEval5158 x
  · exact rowEval5159 x
  · exact rowEval5160 x
  · exact rowEval5161 x
  · exact rowEval5162 x
  · exact rowEval5163 x
  · exact rowEval5164 x
  · exact rowEval5165 x
  · exact rowEval5166 x
  · exact rowEval5167 x
  · exact rowEval5168 x
  · exact rowEval5169 x
  · exact rowEval5170 x
  · exact rowEval5171 x
  · exact rowEval5172 x
  · exact rowEval5173 x
  · exact rowEval5174 x
  · exact rowEval5175 x
  · exact rowEval5176 x
  · exact rowEval5177 x
  · exact rowEval5178 x
  · exact rowEval5179 x
  · exact rowEval5180 x
  · exact rowEval5181 x
  · exact rowEval5182 x
  · exact rowEval5183 x
  · exact rowEval5184 x
  · exact rowEval5185 x
  · exact rowEval5186 x
  · exact rowEval5187 x

theorem entryEval0_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry0_0 (GramNormalization.eval B) = GramFunctions.Block2.form0.mixedGram GramFunctions.Block2.form0 B := by
  rw [entryCheck0_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form0 GramFunctions.Block2.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound0_0]

end MUB6.Certificate.GramEntries.Block2

end OAI
