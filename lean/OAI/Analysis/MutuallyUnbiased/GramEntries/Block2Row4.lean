import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramRows.Block67
import OAI.Analysis.MutuallyUnbiased.GramRows.Block68

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block2.form4.size → Integer.Sparse Key := ![row5508, row5509, row5510, row5511, row5512, row5513, row5514, row5515, row5516, row5517, row5518, row5519, row5520, row5521, row5522, row5523, row5524, row5525, row5526, row5527, row5528, row5529, row5530, row5531, row5532, row5533, row5534, row5535, row5536, row5537]

theorem entryCheck4_0 : entry4_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form4.terms k).coefficient) (rows4_0 k)) := by decide +kernel

theorem rowsSound4_0 (k : Fin GramFunctions.Block2.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form4.terms k).tag (GramFunctions.Block2.form4.terms k).charge GramFunctions.Block2.form0) x := by
  fin_cases k
  · exact rowEval5508 x
  · exact rowEval5509 x
  · exact rowEval5510 x
  · exact rowEval5511 x
  · exact rowEval5512 x
  · exact rowEval5513 x
  · exact rowEval5514 x
  · exact rowEval5515 x
  · exact rowEval5516 x
  · exact rowEval5517 x
  · exact rowEval5518 x
  · exact rowEval5519 x
  · exact rowEval5520 x
  · exact rowEval5521 x
  · exact rowEval5522 x
  · exact rowEval5523 x
  · exact rowEval5524 x
  · exact rowEval5525 x
  · exact rowEval5526 x
  · exact rowEval5527 x
  · exact rowEval5528 x
  · exact rowEval5529 x
  · exact rowEval5530 x
  · exact rowEval5531 x
  · exact rowEval5532 x
  · exact rowEval5533 x
  · exact rowEval5534 x
  · exact rowEval5535 x
  · exact rowEval5536 x
  · exact rowEval5537 x

theorem entryEval4_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_0 (GramNormalization.eval B) = GramFunctions.Block2.form4.mixedGram GramFunctions.Block2.form0 B := by
  rw [entryCheck4_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form4 GramFunctions.Block2.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_0]

def rows4_1 : Fin GramFunctions.Block2.form4.size → Integer.Sparse Key := ![row5538, row5539, row5540, row5541, row5542, row5543, row5544, row5545, row5546, row5547, row5548, row5549, row5550, row5551, row5552, row5553, row5554, row5555, row5556, row5557, row5558, row5559, row5560, row5561, row5562, row5563, row5564, row5565, row5566, row5567]

theorem entryCheck4_1 : entry4_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form4.terms k).coefficient) (rows4_1 k)) := by decide +kernel

theorem rowsSound4_1 (k : Fin GramFunctions.Block2.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form4.terms k).tag (GramFunctions.Block2.form4.terms k).charge GramFunctions.Block2.form1) x := by
  fin_cases k
  · exact rowEval5538 x
  · exact rowEval5539 x
  · exact rowEval5540 x
  · exact rowEval5541 x
  · exact rowEval5542 x
  · exact rowEval5543 x
  · exact rowEval5544 x
  · exact rowEval5545 x
  · exact rowEval5546 x
  · exact rowEval5547 x
  · exact rowEval5548 x
  · exact rowEval5549 x
  · exact rowEval5550 x
  · exact rowEval5551 x
  · exact rowEval5552 x
  · exact rowEval5553 x
  · exact rowEval5554 x
  · exact rowEval5555 x
  · exact rowEval5556 x
  · exact rowEval5557 x
  · exact rowEval5558 x
  · exact rowEval5559 x
  · exact rowEval5560 x
  · exact rowEval5561 x
  · exact rowEval5562 x
  · exact rowEval5563 x
  · exact rowEval5564 x
  · exact rowEval5565 x
  · exact rowEval5566 x
  · exact rowEval5567 x

theorem entryEval4_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_1 (GramNormalization.eval B) = GramFunctions.Block2.form4.mixedGram GramFunctions.Block2.form1 B := by
  rw [entryCheck4_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form4 GramFunctions.Block2.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_1]

def rows4_2 : Fin GramFunctions.Block2.form4.size → Integer.Sparse Key := ![row5568, row5569, row5570, row5571, row5572, row5573, row5574, row5575, row5576, row5577, row5578, row5579, row5580, row5581, row5582, row5583, row5584, row5585, row5586, row5587, row5588, row5589, row5590, row5591, row5592, row5593, row5594, row5595, row5596, row5597]

theorem entryCheck4_2 : entry4_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form4.terms k).coefficient) (rows4_2 k)) := by decide +kernel

theorem rowsSound4_2 (k : Fin GramFunctions.Block2.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form4.terms k).tag (GramFunctions.Block2.form4.terms k).charge GramFunctions.Block2.form2) x := by
  fin_cases k
  · exact rowEval5568 x
  · exact rowEval5569 x
  · exact rowEval5570 x
  · exact rowEval5571 x
  · exact rowEval5572 x
  · exact rowEval5573 x
  · exact rowEval5574 x
  · exact rowEval5575 x
  · exact rowEval5576 x
  · exact rowEval5577 x
  · exact rowEval5578 x
  · exact rowEval5579 x
  · exact rowEval5580 x
  · exact rowEval5581 x
  · exact rowEval5582 x
  · exact rowEval5583 x
  · exact rowEval5584 x
  · exact rowEval5585 x
  · exact rowEval5586 x
  · exact rowEval5587 x
  · exact rowEval5588 x
  · exact rowEval5589 x
  · exact rowEval5590 x
  · exact rowEval5591 x
  · exact rowEval5592 x
  · exact rowEval5593 x
  · exact rowEval5594 x
  · exact rowEval5595 x
  · exact rowEval5596 x
  · exact rowEval5597 x

theorem entryEval4_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_2 (GramNormalization.eval B) = GramFunctions.Block2.form4.mixedGram GramFunctions.Block2.form2 B := by
  rw [entryCheck4_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form4 GramFunctions.Block2.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_2]

def rows4_3 : Fin GramFunctions.Block2.form4.size → Integer.Sparse Key := ![row5598, row5599, row5600, row5601, row5602, row5603, row5604, row5605, row5606, row5607, row5608, row5609, row5610, row5611, row5612, row5613, row5614, row5615, row5616, row5617, row5618, row5619, row5620, row5621, row5622, row5623, row5624, row5625, row5626, row5627]

theorem entryCheck4_3 : entry4_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form4.terms k).coefficient) (rows4_3 k)) := by decide +kernel

theorem rowsSound4_3 (k : Fin GramFunctions.Block2.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form4.terms k).tag (GramFunctions.Block2.form4.terms k).charge GramFunctions.Block2.form3) x := by
  fin_cases k
  · exact rowEval5598 x
  · exact rowEval5599 x
  · exact rowEval5600 x
  · exact rowEval5601 x
  · exact rowEval5602 x
  · exact rowEval5603 x
  · exact rowEval5604 x
  · exact rowEval5605 x
  · exact rowEval5606 x
  · exact rowEval5607 x
  · exact rowEval5608 x
  · exact rowEval5609 x
  · exact rowEval5610 x
  · exact rowEval5611 x
  · exact rowEval5612 x
  · exact rowEval5613 x
  · exact rowEval5614 x
  · exact rowEval5615 x
  · exact rowEval5616 x
  · exact rowEval5617 x
  · exact rowEval5618 x
  · exact rowEval5619 x
  · exact rowEval5620 x
  · exact rowEval5621 x
  · exact rowEval5622 x
  · exact rowEval5623 x
  · exact rowEval5624 x
  · exact rowEval5625 x
  · exact rowEval5626 x
  · exact rowEval5627 x

theorem entryEval4_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_3 (GramNormalization.eval B) = GramFunctions.Block2.form4.mixedGram GramFunctions.Block2.form3 B := by
  rw [entryCheck4_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form4 GramFunctions.Block2.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_3]

def rows4_4 : Fin GramFunctions.Block2.form4.size → Integer.Sparse Key := ![row5628, row5629, row5630, row5631, row5632, row5633, row5634, row5635, row5636, row5637, row5638, row5639, row5640, row5641, row5642, row5643, row5644, row5645, row5646, row5647, row5648, row5649, row5650, row5651, row5652, row5653, row5654, row5655, row5656, row5657]

theorem entryCheck4_4 : entry4_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form4.terms k).coefficient) (rows4_4 k)) := by decide +kernel

theorem rowsSound4_4 (k : Fin GramFunctions.Block2.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form4.terms k).tag (GramFunctions.Block2.form4.terms k).charge GramFunctions.Block2.form4) x := by
  fin_cases k
  · exact rowEval5628 x
  · exact rowEval5629 x
  · exact rowEval5630 x
  · exact rowEval5631 x
  · exact rowEval5632 x
  · exact rowEval5633 x
  · exact rowEval5634 x
  · exact rowEval5635 x
  · exact rowEval5636 x
  · exact rowEval5637 x
  · exact rowEval5638 x
  · exact rowEval5639 x
  · exact rowEval5640 x
  · exact rowEval5641 x
  · exact rowEval5642 x
  · exact rowEval5643 x
  · exact rowEval5644 x
  · exact rowEval5645 x
  · exact rowEval5646 x
  · exact rowEval5647 x
  · exact rowEval5648 x
  · exact rowEval5649 x
  · exact rowEval5650 x
  · exact rowEval5651 x
  · exact rowEval5652 x
  · exact rowEval5653 x
  · exact rowEval5654 x
  · exact rowEval5655 x
  · exact rowEval5656 x
  · exact rowEval5657 x

theorem entryEval4_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_4 (GramNormalization.eval B) = GramFunctions.Block2.form4.mixedGram GramFunctions.Block2.form4 B := by
  rw [entryCheck4_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form4 GramFunctions.Block2.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_4]

end MUB6.Certificate.GramEntries.Block2

end OAI
