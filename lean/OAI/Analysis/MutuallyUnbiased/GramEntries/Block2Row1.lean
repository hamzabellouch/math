import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramRows.Block64
import OAI.Analysis.MutuallyUnbiased.GramRows.Block65

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block2.form1.size → Integer.Sparse Key := ![row5188, row5189, row5190, row5191, row5192, row5193, row5194, row5195, row5196, row5197, row5198, row5199, row5200, row5201, row5202, row5203, row5204, row5205, row5206, row5207, row5208, row5209, row5210, row5211, row5212, row5213, row5214, row5215, row5216, row5217, row5218, row5219, row5220, row5221, row5222, row5223, row5224, row5225, row5226, row5227]

theorem entryCheck1_0 : entry1_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form1.terms k).coefficient) (rows1_0 k)) := by decide +kernel

theorem rowsSound1_0 (k : Fin GramFunctions.Block2.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form1.terms k).tag (GramFunctions.Block2.form1.terms k).charge GramFunctions.Block2.form0) x := by
  fin_cases k
  · exact rowEval5188 x
  · exact rowEval5189 x
  · exact rowEval5190 x
  · exact rowEval5191 x
  · exact rowEval5192 x
  · exact rowEval5193 x
  · exact rowEval5194 x
  · exact rowEval5195 x
  · exact rowEval5196 x
  · exact rowEval5197 x
  · exact rowEval5198 x
  · exact rowEval5199 x
  · exact rowEval5200 x
  · exact rowEval5201 x
  · exact rowEval5202 x
  · exact rowEval5203 x
  · exact rowEval5204 x
  · exact rowEval5205 x
  · exact rowEval5206 x
  · exact rowEval5207 x
  · exact rowEval5208 x
  · exact rowEval5209 x
  · exact rowEval5210 x
  · exact rowEval5211 x
  · exact rowEval5212 x
  · exact rowEval5213 x
  · exact rowEval5214 x
  · exact rowEval5215 x
  · exact rowEval5216 x
  · exact rowEval5217 x
  · exact rowEval5218 x
  · exact rowEval5219 x
  · exact rowEval5220 x
  · exact rowEval5221 x
  · exact rowEval5222 x
  · exact rowEval5223 x
  · exact rowEval5224 x
  · exact rowEval5225 x
  · exact rowEval5226 x
  · exact rowEval5227 x

theorem entryEval1_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_0 (GramNormalization.eval B) = GramFunctions.Block2.form1.mixedGram GramFunctions.Block2.form0 B := by
  rw [entryCheck1_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form1 GramFunctions.Block2.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_0]

def rows1_1 : Fin GramFunctions.Block2.form1.size → Integer.Sparse Key := ![row5228, row5229, row5230, row5231, row5232, row5233, row5234, row5235, row5236, row5237, row5238, row5239, row5240, row5241, row5242, row5243, row5244, row5245, row5246, row5247, row5248, row5249, row5250, row5251, row5252, row5253, row5254, row5255, row5256, row5257, row5258, row5259, row5260, row5261, row5262, row5263, row5264, row5265, row5266, row5267]

theorem entryCheck1_1 : entry1_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form1.terms k).coefficient) (rows1_1 k)) := by decide +kernel

theorem rowsSound1_1 (k : Fin GramFunctions.Block2.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form1.terms k).tag (GramFunctions.Block2.form1.terms k).charge GramFunctions.Block2.form1) x := by
  fin_cases k
  · exact rowEval5228 x
  · exact rowEval5229 x
  · exact rowEval5230 x
  · exact rowEval5231 x
  · exact rowEval5232 x
  · exact rowEval5233 x
  · exact rowEval5234 x
  · exact rowEval5235 x
  · exact rowEval5236 x
  · exact rowEval5237 x
  · exact rowEval5238 x
  · exact rowEval5239 x
  · exact rowEval5240 x
  · exact rowEval5241 x
  · exact rowEval5242 x
  · exact rowEval5243 x
  · exact rowEval5244 x
  · exact rowEval5245 x
  · exact rowEval5246 x
  · exact rowEval5247 x
  · exact rowEval5248 x
  · exact rowEval5249 x
  · exact rowEval5250 x
  · exact rowEval5251 x
  · exact rowEval5252 x
  · exact rowEval5253 x
  · exact rowEval5254 x
  · exact rowEval5255 x
  · exact rowEval5256 x
  · exact rowEval5257 x
  · exact rowEval5258 x
  · exact rowEval5259 x
  · exact rowEval5260 x
  · exact rowEval5261 x
  · exact rowEval5262 x
  · exact rowEval5263 x
  · exact rowEval5264 x
  · exact rowEval5265 x
  · exact rowEval5266 x
  · exact rowEval5267 x

theorem entryEval1_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_1 (GramNormalization.eval B) = GramFunctions.Block2.form1.mixedGram GramFunctions.Block2.form1 B := by
  rw [entryCheck1_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form1 GramFunctions.Block2.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_1]

end MUB6.Certificate.GramEntries.Block2

end OAI
