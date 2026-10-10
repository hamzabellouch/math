import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramRows.Block66
import OAI.Analysis.MutuallyUnbiased.GramRows.Block67

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block2.form3.size → Integer.Sparse Key := ![row5388, row5389, row5390, row5391, row5392, row5393, row5394, row5395, row5396, row5397, row5398, row5399, row5400, row5401, row5402, row5403, row5404, row5405, row5406, row5407, row5408, row5409, row5410, row5411, row5412, row5413, row5414, row5415, row5416, row5417]

theorem entryCheck3_0 : entry3_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form3.terms k).coefficient) (rows3_0 k)) := by decide +kernel

theorem rowsSound3_0 (k : Fin GramFunctions.Block2.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form3.terms k).tag (GramFunctions.Block2.form3.terms k).charge GramFunctions.Block2.form0) x := by
  fin_cases k
  · exact rowEval5388 x
  · exact rowEval5389 x
  · exact rowEval5390 x
  · exact rowEval5391 x
  · exact rowEval5392 x
  · exact rowEval5393 x
  · exact rowEval5394 x
  · exact rowEval5395 x
  · exact rowEval5396 x
  · exact rowEval5397 x
  · exact rowEval5398 x
  · exact rowEval5399 x
  · exact rowEval5400 x
  · exact rowEval5401 x
  · exact rowEval5402 x
  · exact rowEval5403 x
  · exact rowEval5404 x
  · exact rowEval5405 x
  · exact rowEval5406 x
  · exact rowEval5407 x
  · exact rowEval5408 x
  · exact rowEval5409 x
  · exact rowEval5410 x
  · exact rowEval5411 x
  · exact rowEval5412 x
  · exact rowEval5413 x
  · exact rowEval5414 x
  · exact rowEval5415 x
  · exact rowEval5416 x
  · exact rowEval5417 x

theorem entryEval3_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_0 (GramNormalization.eval B) = GramFunctions.Block2.form3.mixedGram GramFunctions.Block2.form0 B := by
  rw [entryCheck3_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form3 GramFunctions.Block2.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_0]

def rows3_1 : Fin GramFunctions.Block2.form3.size → Integer.Sparse Key := ![row5418, row5419, row5420, row5421, row5422, row5423, row5424, row5425, row5426, row5427, row5428, row5429, row5430, row5431, row5432, row5433, row5434, row5435, row5436, row5437, row5438, row5439, row5440, row5441, row5442, row5443, row5444, row5445, row5446, row5447]

theorem entryCheck3_1 : entry3_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form3.terms k).coefficient) (rows3_1 k)) := by decide +kernel

theorem rowsSound3_1 (k : Fin GramFunctions.Block2.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form3.terms k).tag (GramFunctions.Block2.form3.terms k).charge GramFunctions.Block2.form1) x := by
  fin_cases k
  · exact rowEval5418 x
  · exact rowEval5419 x
  · exact rowEval5420 x
  · exact rowEval5421 x
  · exact rowEval5422 x
  · exact rowEval5423 x
  · exact rowEval5424 x
  · exact rowEval5425 x
  · exact rowEval5426 x
  · exact rowEval5427 x
  · exact rowEval5428 x
  · exact rowEval5429 x
  · exact rowEval5430 x
  · exact rowEval5431 x
  · exact rowEval5432 x
  · exact rowEval5433 x
  · exact rowEval5434 x
  · exact rowEval5435 x
  · exact rowEval5436 x
  · exact rowEval5437 x
  · exact rowEval5438 x
  · exact rowEval5439 x
  · exact rowEval5440 x
  · exact rowEval5441 x
  · exact rowEval5442 x
  · exact rowEval5443 x
  · exact rowEval5444 x
  · exact rowEval5445 x
  · exact rowEval5446 x
  · exact rowEval5447 x

theorem entryEval3_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_1 (GramNormalization.eval B) = GramFunctions.Block2.form3.mixedGram GramFunctions.Block2.form1 B := by
  rw [entryCheck3_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form3 GramFunctions.Block2.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_1]

def rows3_2 : Fin GramFunctions.Block2.form3.size → Integer.Sparse Key := ![row5448, row5449, row5450, row5451, row5452, row5453, row5454, row5455, row5456, row5457, row5458, row5459, row5460, row5461, row5462, row5463, row5464, row5465, row5466, row5467, row5468, row5469, row5470, row5471, row5472, row5473, row5474, row5475, row5476, row5477]

theorem entryCheck3_2 : entry3_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form3.terms k).coefficient) (rows3_2 k)) := by decide +kernel

theorem rowsSound3_2 (k : Fin GramFunctions.Block2.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form3.terms k).tag (GramFunctions.Block2.form3.terms k).charge GramFunctions.Block2.form2) x := by
  fin_cases k
  · exact rowEval5448 x
  · exact rowEval5449 x
  · exact rowEval5450 x
  · exact rowEval5451 x
  · exact rowEval5452 x
  · exact rowEval5453 x
  · exact rowEval5454 x
  · exact rowEval5455 x
  · exact rowEval5456 x
  · exact rowEval5457 x
  · exact rowEval5458 x
  · exact rowEval5459 x
  · exact rowEval5460 x
  · exact rowEval5461 x
  · exact rowEval5462 x
  · exact rowEval5463 x
  · exact rowEval5464 x
  · exact rowEval5465 x
  · exact rowEval5466 x
  · exact rowEval5467 x
  · exact rowEval5468 x
  · exact rowEval5469 x
  · exact rowEval5470 x
  · exact rowEval5471 x
  · exact rowEval5472 x
  · exact rowEval5473 x
  · exact rowEval5474 x
  · exact rowEval5475 x
  · exact rowEval5476 x
  · exact rowEval5477 x

theorem entryEval3_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_2 (GramNormalization.eval B) = GramFunctions.Block2.form3.mixedGram GramFunctions.Block2.form2 B := by
  rw [entryCheck3_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form3 GramFunctions.Block2.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_2]

def rows3_3 : Fin GramFunctions.Block2.form3.size → Integer.Sparse Key := ![row5478, row5479, row5480, row5481, row5482, row5483, row5484, row5485, row5486, row5487, row5488, row5489, row5490, row5491, row5492, row5493, row5494, row5495, row5496, row5497, row5498, row5499, row5500, row5501, row5502, row5503, row5504, row5505, row5506, row5507]

theorem entryCheck3_3 : entry3_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form3.terms k).coefficient) (rows3_3 k)) := by decide +kernel

theorem rowsSound3_3 (k : Fin GramFunctions.Block2.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form3.terms k).tag (GramFunctions.Block2.form3.terms k).charge GramFunctions.Block2.form3) x := by
  fin_cases k
  · exact rowEval5478 x
  · exact rowEval5479 x
  · exact rowEval5480 x
  · exact rowEval5481 x
  · exact rowEval5482 x
  · exact rowEval5483 x
  · exact rowEval5484 x
  · exact rowEval5485 x
  · exact rowEval5486 x
  · exact rowEval5487 x
  · exact rowEval5488 x
  · exact rowEval5489 x
  · exact rowEval5490 x
  · exact rowEval5491 x
  · exact rowEval5492 x
  · exact rowEval5493 x
  · exact rowEval5494 x
  · exact rowEval5495 x
  · exact rowEval5496 x
  · exact rowEval5497 x
  · exact rowEval5498 x
  · exact rowEval5499 x
  · exact rowEval5500 x
  · exact rowEval5501 x
  · exact rowEval5502 x
  · exact rowEval5503 x
  · exact rowEval5504 x
  · exact rowEval5505 x
  · exact rowEval5506 x
  · exact rowEval5507 x

theorem entryEval3_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_3 (GramNormalization.eval B) = GramFunctions.Block2.form3.mixedGram GramFunctions.Block2.form3 B := by
  rw [entryCheck3_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form3 GramFunctions.Block2.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_3]

end MUB6.Certificate.GramEntries.Block2

end OAI
