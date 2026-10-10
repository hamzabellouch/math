import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramRows.Block65
import OAI.Analysis.MutuallyUnbiased.GramRows.Block66

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block2.form2.size → Integer.Sparse Key := ![row5268, row5269, row5270, row5271, row5272, row5273, row5274, row5275, row5276, row5277, row5278, row5279, row5280, row5281, row5282, row5283, row5284, row5285, row5286, row5287, row5288, row5289, row5290, row5291, row5292, row5293, row5294, row5295, row5296, row5297, row5298, row5299, row5300, row5301, row5302, row5303, row5304, row5305, row5306, row5307]

theorem entryCheck2_0 : entry2_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form2.terms k).coefficient) (rows2_0 k)) := by decide +kernel

theorem rowsSound2_0 (k : Fin GramFunctions.Block2.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form2.terms k).tag (GramFunctions.Block2.form2.terms k).charge GramFunctions.Block2.form0) x := by
  fin_cases k
  · exact rowEval5268 x
  · exact rowEval5269 x
  · exact rowEval5270 x
  · exact rowEval5271 x
  · exact rowEval5272 x
  · exact rowEval5273 x
  · exact rowEval5274 x
  · exact rowEval5275 x
  · exact rowEval5276 x
  · exact rowEval5277 x
  · exact rowEval5278 x
  · exact rowEval5279 x
  · exact rowEval5280 x
  · exact rowEval5281 x
  · exact rowEval5282 x
  · exact rowEval5283 x
  · exact rowEval5284 x
  · exact rowEval5285 x
  · exact rowEval5286 x
  · exact rowEval5287 x
  · exact rowEval5288 x
  · exact rowEval5289 x
  · exact rowEval5290 x
  · exact rowEval5291 x
  · exact rowEval5292 x
  · exact rowEval5293 x
  · exact rowEval5294 x
  · exact rowEval5295 x
  · exact rowEval5296 x
  · exact rowEval5297 x
  · exact rowEval5298 x
  · exact rowEval5299 x
  · exact rowEval5300 x
  · exact rowEval5301 x
  · exact rowEval5302 x
  · exact rowEval5303 x
  · exact rowEval5304 x
  · exact rowEval5305 x
  · exact rowEval5306 x
  · exact rowEval5307 x

theorem entryEval2_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_0 (GramNormalization.eval B) = GramFunctions.Block2.form2.mixedGram GramFunctions.Block2.form0 B := by
  rw [entryCheck2_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form2 GramFunctions.Block2.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_0]

def rows2_1 : Fin GramFunctions.Block2.form2.size → Integer.Sparse Key := ![row5308, row5309, row5310, row5311, row5312, row5313, row5314, row5315, row5316, row5317, row5318, row5319, row5320, row5321, row5322, row5323, row5324, row5325, row5326, row5327, row5328, row5329, row5330, row5331, row5332, row5333, row5334, row5335, row5336, row5337, row5338, row5339, row5340, row5341, row5342, row5343, row5344, row5345, row5346, row5347]

theorem entryCheck2_1 : entry2_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form2.terms k).coefficient) (rows2_1 k)) := by decide +kernel

theorem rowsSound2_1 (k : Fin GramFunctions.Block2.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form2.terms k).tag (GramFunctions.Block2.form2.terms k).charge GramFunctions.Block2.form1) x := by
  fin_cases k
  · exact rowEval5308 x
  · exact rowEval5309 x
  · exact rowEval5310 x
  · exact rowEval5311 x
  · exact rowEval5312 x
  · exact rowEval5313 x
  · exact rowEval5314 x
  · exact rowEval5315 x
  · exact rowEval5316 x
  · exact rowEval5317 x
  · exact rowEval5318 x
  · exact rowEval5319 x
  · exact rowEval5320 x
  · exact rowEval5321 x
  · exact rowEval5322 x
  · exact rowEval5323 x
  · exact rowEval5324 x
  · exact rowEval5325 x
  · exact rowEval5326 x
  · exact rowEval5327 x
  · exact rowEval5328 x
  · exact rowEval5329 x
  · exact rowEval5330 x
  · exact rowEval5331 x
  · exact rowEval5332 x
  · exact rowEval5333 x
  · exact rowEval5334 x
  · exact rowEval5335 x
  · exact rowEval5336 x
  · exact rowEval5337 x
  · exact rowEval5338 x
  · exact rowEval5339 x
  · exact rowEval5340 x
  · exact rowEval5341 x
  · exact rowEval5342 x
  · exact rowEval5343 x
  · exact rowEval5344 x
  · exact rowEval5345 x
  · exact rowEval5346 x
  · exact rowEval5347 x

theorem entryEval2_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_1 (GramNormalization.eval B) = GramFunctions.Block2.form2.mixedGram GramFunctions.Block2.form1 B := by
  rw [entryCheck2_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form2 GramFunctions.Block2.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_1]

def rows2_2 : Fin GramFunctions.Block2.form2.size → Integer.Sparse Key := ![row5348, row5349, row5350, row5351, row5352, row5353, row5354, row5355, row5356, row5357, row5358, row5359, row5360, row5361, row5362, row5363, row5364, row5365, row5366, row5367, row5368, row5369, row5370, row5371, row5372, row5373, row5374, row5375, row5376, row5377, row5378, row5379, row5380, row5381, row5382, row5383, row5384, row5385, row5386, row5387]

theorem entryCheck2_2 : entry2_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form2.terms k).coefficient) (rows2_2 k)) := by decide +kernel

theorem rowsSound2_2 (k : Fin GramFunctions.Block2.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form2.terms k).tag (GramFunctions.Block2.form2.terms k).charge GramFunctions.Block2.form2) x := by
  fin_cases k
  · exact rowEval5348 x
  · exact rowEval5349 x
  · exact rowEval5350 x
  · exact rowEval5351 x
  · exact rowEval5352 x
  · exact rowEval5353 x
  · exact rowEval5354 x
  · exact rowEval5355 x
  · exact rowEval5356 x
  · exact rowEval5357 x
  · exact rowEval5358 x
  · exact rowEval5359 x
  · exact rowEval5360 x
  · exact rowEval5361 x
  · exact rowEval5362 x
  · exact rowEval5363 x
  · exact rowEval5364 x
  · exact rowEval5365 x
  · exact rowEval5366 x
  · exact rowEval5367 x
  · exact rowEval5368 x
  · exact rowEval5369 x
  · exact rowEval5370 x
  · exact rowEval5371 x
  · exact rowEval5372 x
  · exact rowEval5373 x
  · exact rowEval5374 x
  · exact rowEval5375 x
  · exact rowEval5376 x
  · exact rowEval5377 x
  · exact rowEval5378 x
  · exact rowEval5379 x
  · exact rowEval5380 x
  · exact rowEval5381 x
  · exact rowEval5382 x
  · exact rowEval5383 x
  · exact rowEval5384 x
  · exact rowEval5385 x
  · exact rowEval5386 x
  · exact rowEval5387 x

theorem entryEval2_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_2 (GramNormalization.eval B) = GramFunctions.Block2.form2.mixedGram GramFunctions.Block2.form2 B := by
  rw [entryCheck2_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form2 GramFunctions.Block2.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_2]

end MUB6.Certificate.GramEntries.Block2

end OAI
