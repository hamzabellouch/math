import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramRows.Block68
import OAI.Analysis.MutuallyUnbiased.GramRows.Block69
import OAI.Analysis.MutuallyUnbiased.GramRows.Block70
import OAI.Analysis.MutuallyUnbiased.GramRows.Block74
import OAI.Analysis.MutuallyUnbiased.GramRows.Block75
import OAI.Analysis.MutuallyUnbiased.GramRows.Block76

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows8_0 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6478, row6479, row6480, row6481, row6482, row6483, row6484, row6485, row6486, row6487, row6488, row6489, row5670, row5671, row5672, row5673, row5674, row5675, row5676, row5677, row5678, row5679, row5680, row5681, row5682, row5683, row6490, row6491, row5686, row5687, row6492, row6493, row6494, row6495, row5692, row5693, row6496, row6497, row5696, row5697]

theorem entryCheck8_0 : entry8_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form8.terms k).coefficient) (rows8_0 k)) := by decide +kernel

theorem rowsSound8_0 (k : Fin GramFunctions.Block2.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form8.terms k).tag (GramFunctions.Block2.form8.terms k).charge GramFunctions.Block2.form0) x := by
  fin_cases k
  · exact rowEval6478 x
  · exact rowEval6479 x
  · exact rowEval6480 x
  · exact rowEval6481 x
  · exact rowEval6482 x
  · exact rowEval6483 x
  · exact rowEval6484 x
  · exact rowEval6485 x
  · exact rowEval6486 x
  · exact rowEval6487 x
  · exact rowEval6488 x
  · exact rowEval6489 x
  · exact rowEval5670 x
  · exact rowEval5671 x
  · exact rowEval5672 x
  · exact rowEval5673 x
  · exact rowEval5674 x
  · exact rowEval5675 x
  · exact rowEval5676 x
  · exact rowEval5677 x
  · exact rowEval5678 x
  · exact rowEval5679 x
  · exact rowEval5680 x
  · exact rowEval5681 x
  · exact rowEval5682 x
  · exact rowEval5683 x
  · exact rowEval6490 x
  · exact rowEval6491 x
  · exact rowEval5686 x
  · exact rowEval5687 x
  · exact rowEval6492 x
  · exact rowEval6493 x
  · exact rowEval6494 x
  · exact rowEval6495 x
  · exact rowEval5692 x
  · exact rowEval5693 x
  · exact rowEval6496 x
  · exact rowEval6497 x
  · exact rowEval5696 x
  · exact rowEval5697 x

theorem entryEval8_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_0 (GramNormalization.eval B) = GramFunctions.Block2.form8.mixedGram GramFunctions.Block2.form0 B := by
  rw [entryCheck8_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form8 GramFunctions.Block2.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_0]

def rows8_1 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6498, row6499, row6500, row6501, row6502, row6503, row6504, row6505, row6506, row6507, row6508, row6509, row5710, row5711, row5712, row5713, row5714, row5715, row5716, row5717, row5718, row5719, row5720, row5721, row5722, row5723, row6510, row6511, row5726, row5727, row6512, row6513, row6514, row6515, row5732, row5733, row6516, row6517, row5736, row5737]

theorem entryCheck8_1 : entry8_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form8.terms k).coefficient) (rows8_1 k)) := by decide +kernel

theorem rowsSound8_1 (k : Fin GramFunctions.Block2.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form8.terms k).tag (GramFunctions.Block2.form8.terms k).charge GramFunctions.Block2.form1) x := by
  fin_cases k
  · exact rowEval6498 x
  · exact rowEval6499 x
  · exact rowEval6500 x
  · exact rowEval6501 x
  · exact rowEval6502 x
  · exact rowEval6503 x
  · exact rowEval6504 x
  · exact rowEval6505 x
  · exact rowEval6506 x
  · exact rowEval6507 x
  · exact rowEval6508 x
  · exact rowEval6509 x
  · exact rowEval5710 x
  · exact rowEval5711 x
  · exact rowEval5712 x
  · exact rowEval5713 x
  · exact rowEval5714 x
  · exact rowEval5715 x
  · exact rowEval5716 x
  · exact rowEval5717 x
  · exact rowEval5718 x
  · exact rowEval5719 x
  · exact rowEval5720 x
  · exact rowEval5721 x
  · exact rowEval5722 x
  · exact rowEval5723 x
  · exact rowEval6510 x
  · exact rowEval6511 x
  · exact rowEval5726 x
  · exact rowEval5727 x
  · exact rowEval6512 x
  · exact rowEval6513 x
  · exact rowEval6514 x
  · exact rowEval6515 x
  · exact rowEval5732 x
  · exact rowEval5733 x
  · exact rowEval6516 x
  · exact rowEval6517 x
  · exact rowEval5736 x
  · exact rowEval5737 x

theorem entryEval8_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_1 (GramNormalization.eval B) = GramFunctions.Block2.form8.mixedGram GramFunctions.Block2.form1 B := by
  rw [entryCheck8_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form8 GramFunctions.Block2.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_1]

def rows8_2 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6518, row6519, row6520, row6521, row6522, row6523, row6524, row6525, row6526, row6527, row6528, row6529, row5750, row5751, row5752, row5753, row5754, row5755, row5756, row5757, row5758, row5759, row5760, row5761, row5762, row5763, row6530, row6531, row5766, row5767, row6532, row6533, row6534, row6535, row5772, row5773, row6536, row6537, row5776, row5777]

theorem entryCheck8_2 : entry8_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form8.terms k).coefficient) (rows8_2 k)) := by decide +kernel

theorem rowsSound8_2 (k : Fin GramFunctions.Block2.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form8.terms k).tag (GramFunctions.Block2.form8.terms k).charge GramFunctions.Block2.form2) x := by
  fin_cases k
  · exact rowEval6518 x
  · exact rowEval6519 x
  · exact rowEval6520 x
  · exact rowEval6521 x
  · exact rowEval6522 x
  · exact rowEval6523 x
  · exact rowEval6524 x
  · exact rowEval6525 x
  · exact rowEval6526 x
  · exact rowEval6527 x
  · exact rowEval6528 x
  · exact rowEval6529 x
  · exact rowEval5750 x
  · exact rowEval5751 x
  · exact rowEval5752 x
  · exact rowEval5753 x
  · exact rowEval5754 x
  · exact rowEval5755 x
  · exact rowEval5756 x
  · exact rowEval5757 x
  · exact rowEval5758 x
  · exact rowEval5759 x
  · exact rowEval5760 x
  · exact rowEval5761 x
  · exact rowEval5762 x
  · exact rowEval5763 x
  · exact rowEval6530 x
  · exact rowEval6531 x
  · exact rowEval5766 x
  · exact rowEval5767 x
  · exact rowEval6532 x
  · exact rowEval6533 x
  · exact rowEval6534 x
  · exact rowEval6535 x
  · exact rowEval5772 x
  · exact rowEval5773 x
  · exact rowEval6536 x
  · exact rowEval6537 x
  · exact rowEval5776 x
  · exact rowEval5777 x

theorem entryEval8_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_2 (GramNormalization.eval B) = GramFunctions.Block2.form8.mixedGram GramFunctions.Block2.form2 B := by
  rw [entryCheck8_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form8 GramFunctions.Block2.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_2]

def rows8_3 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6538, row6539, row6540, row6541, row6542, row6543, row6544, row6545, row6546, row6547, row6548, row6549, row5790, row5791, row5792, row5793, row5794, row5795, row5796, row5797, row5798, row5799, row5800, row5801, row5802, row5803, row6550, row6551, row5806, row5807, row6552, row6553, row6554, row6555, row5812, row5813, row6556, row6557, row5816, row5817]

theorem entryCheck8_3 : entry8_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form8.terms k).coefficient) (rows8_3 k)) := by decide +kernel

theorem rowsSound8_3 (k : Fin GramFunctions.Block2.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form8.terms k).tag (GramFunctions.Block2.form8.terms k).charge GramFunctions.Block2.form3) x := by
  fin_cases k
  · exact rowEval6538 x
  · exact rowEval6539 x
  · exact rowEval6540 x
  · exact rowEval6541 x
  · exact rowEval6542 x
  · exact rowEval6543 x
  · exact rowEval6544 x
  · exact rowEval6545 x
  · exact rowEval6546 x
  · exact rowEval6547 x
  · exact rowEval6548 x
  · exact rowEval6549 x
  · exact rowEval5790 x
  · exact rowEval5791 x
  · exact rowEval5792 x
  · exact rowEval5793 x
  · exact rowEval5794 x
  · exact rowEval5795 x
  · exact rowEval5796 x
  · exact rowEval5797 x
  · exact rowEval5798 x
  · exact rowEval5799 x
  · exact rowEval5800 x
  · exact rowEval5801 x
  · exact rowEval5802 x
  · exact rowEval5803 x
  · exact rowEval6550 x
  · exact rowEval6551 x
  · exact rowEval5806 x
  · exact rowEval5807 x
  · exact rowEval6552 x
  · exact rowEval6553 x
  · exact rowEval6554 x
  · exact rowEval6555 x
  · exact rowEval5812 x
  · exact rowEval5813 x
  · exact rowEval6556 x
  · exact rowEval6557 x
  · exact rowEval5816 x
  · exact rowEval5817 x

theorem entryEval8_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_3 (GramNormalization.eval B) = GramFunctions.Block2.form8.mixedGram GramFunctions.Block2.form3 B := by
  rw [entryCheck8_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form8 GramFunctions.Block2.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_3]

def rows8_4 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6558, row6559, row6560, row6561, row6562, row6563, row6564, row6565, row6566, row6567, row6568, row6569, row5830, row5831, row5832, row5833, row5834, row5835, row5836, row5837, row5838, row5839, row5840, row5841, row5842, row5843, row6570, row6571, row5846, row5847, row6572, row6573, row6574, row6575, row5852, row5853, row6576, row6577, row5856, row5857]

theorem entryCheck8_4 : entry8_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form8.terms k).coefficient) (rows8_4 k)) := by decide +kernel

theorem rowsSound8_4 (k : Fin GramFunctions.Block2.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form8.terms k).tag (GramFunctions.Block2.form8.terms k).charge GramFunctions.Block2.form4) x := by
  fin_cases k
  · exact rowEval6558 x
  · exact rowEval6559 x
  · exact rowEval6560 x
  · exact rowEval6561 x
  · exact rowEval6562 x
  · exact rowEval6563 x
  · exact rowEval6564 x
  · exact rowEval6565 x
  · exact rowEval6566 x
  · exact rowEval6567 x
  · exact rowEval6568 x
  · exact rowEval6569 x
  · exact rowEval5830 x
  · exact rowEval5831 x
  · exact rowEval5832 x
  · exact rowEval5833 x
  · exact rowEval5834 x
  · exact rowEval5835 x
  · exact rowEval5836 x
  · exact rowEval5837 x
  · exact rowEval5838 x
  · exact rowEval5839 x
  · exact rowEval5840 x
  · exact rowEval5841 x
  · exact rowEval5842 x
  · exact rowEval5843 x
  · exact rowEval6570 x
  · exact rowEval6571 x
  · exact rowEval5846 x
  · exact rowEval5847 x
  · exact rowEval6572 x
  · exact rowEval6573 x
  · exact rowEval6574 x
  · exact rowEval6575 x
  · exact rowEval5852 x
  · exact rowEval5853 x
  · exact rowEval6576 x
  · exact rowEval6577 x
  · exact rowEval5856 x
  · exact rowEval5857 x

theorem entryEval8_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_4 (GramNormalization.eval B) = GramFunctions.Block2.form8.mixedGram GramFunctions.Block2.form4 B := by
  rw [entryCheck8_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form8 GramFunctions.Block2.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_4]

def rows8_5 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6578, row6579, row6580, row6581, row6582, row6583, row6584, row6585, row6586, row6587, row6588, row6589, row5870, row5871, row5872, row5873, row5874, row5875, row5876, row5877, row5878, row5879, row5880, row5881, row5882, row5883, row6590, row6591, row5886, row5887, row6592, row6593, row6594, row6595, row5892, row5893, row6596, row6597, row5896, row5897]

theorem entryCheck8_5 : entry8_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form8.terms k).coefficient) (rows8_5 k)) := by decide +kernel

theorem rowsSound8_5 (k : Fin GramFunctions.Block2.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form8.terms k).tag (GramFunctions.Block2.form8.terms k).charge GramFunctions.Block2.form5) x := by
  fin_cases k
  · exact rowEval6578 x
  · exact rowEval6579 x
  · exact rowEval6580 x
  · exact rowEval6581 x
  · exact rowEval6582 x
  · exact rowEval6583 x
  · exact rowEval6584 x
  · exact rowEval6585 x
  · exact rowEval6586 x
  · exact rowEval6587 x
  · exact rowEval6588 x
  · exact rowEval6589 x
  · exact rowEval5870 x
  · exact rowEval5871 x
  · exact rowEval5872 x
  · exact rowEval5873 x
  · exact rowEval5874 x
  · exact rowEval5875 x
  · exact rowEval5876 x
  · exact rowEval5877 x
  · exact rowEval5878 x
  · exact rowEval5879 x
  · exact rowEval5880 x
  · exact rowEval5881 x
  · exact rowEval5882 x
  · exact rowEval5883 x
  · exact rowEval6590 x
  · exact rowEval6591 x
  · exact rowEval5886 x
  · exact rowEval5887 x
  · exact rowEval6592 x
  · exact rowEval6593 x
  · exact rowEval6594 x
  · exact rowEval6595 x
  · exact rowEval5892 x
  · exact rowEval5893 x
  · exact rowEval6596 x
  · exact rowEval6597 x
  · exact rowEval5896 x
  · exact rowEval5897 x

theorem entryEval8_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_5 (GramNormalization.eval B) = GramFunctions.Block2.form8.mixedGram GramFunctions.Block2.form5 B := by
  rw [entryCheck8_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form8 GramFunctions.Block2.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_5]

def rows8_6 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6598, row6599, row6600, row6601, row6602, row6603, row6604, row6605, row6606, row6607, row6608, row6609, row6610, row6611, row6612, row6613, row6614, row6615, row6616, row6617, row6618, row6619, row6620, row6621, row6622, row6623, row6624, row6625, row6626, row6627, row6628, row6629, row6630, row6631, row6632, row6633, row6634, row6635, row6636, row6637]

theorem entryCheck8_6 : entry8_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form8.terms k).coefficient) (rows8_6 k)) := by decide +kernel

theorem rowsSound8_6 (k : Fin GramFunctions.Block2.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form8.terms k).tag (GramFunctions.Block2.form8.terms k).charge GramFunctions.Block2.form6) x := by
  fin_cases k
  · exact rowEval6598 x
  · exact rowEval6599 x
  · exact rowEval6600 x
  · exact rowEval6601 x
  · exact rowEval6602 x
  · exact rowEval6603 x
  · exact rowEval6604 x
  · exact rowEval6605 x
  · exact rowEval6606 x
  · exact rowEval6607 x
  · exact rowEval6608 x
  · exact rowEval6609 x
  · exact rowEval6610 x
  · exact rowEval6611 x
  · exact rowEval6612 x
  · exact rowEval6613 x
  · exact rowEval6614 x
  · exact rowEval6615 x
  · exact rowEval6616 x
  · exact rowEval6617 x
  · exact rowEval6618 x
  · exact rowEval6619 x
  · exact rowEval6620 x
  · exact rowEval6621 x
  · exact rowEval6622 x
  · exact rowEval6623 x
  · exact rowEval6624 x
  · exact rowEval6625 x
  · exact rowEval6626 x
  · exact rowEval6627 x
  · exact rowEval6628 x
  · exact rowEval6629 x
  · exact rowEval6630 x
  · exact rowEval6631 x
  · exact rowEval6632 x
  · exact rowEval6633 x
  · exact rowEval6634 x
  · exact rowEval6635 x
  · exact rowEval6636 x
  · exact rowEval6637 x

theorem entryEval8_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_6 (GramNormalization.eval B) = GramFunctions.Block2.form8.mixedGram GramFunctions.Block2.form6 B := by
  rw [entryCheck8_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form8 GramFunctions.Block2.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_6]

def rows8_7 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6638, row6639, row6640, row6641, row6642, row6643, row6644, row6645, row6646, row6647, row6648, row6649, row6650, row6651, row6652, row6653, row6654, row6655, row6656, row6657, row6658, row6659, row6660, row6661, row6662, row6663, row6664, row6665, row6666, row6667, row6668, row6669, row6670, row6671, row6672, row6673, row6674, row6675, row6676, row6677]

theorem entryCheck8_7 : entry8_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form8.terms k).coefficient) (rows8_7 k)) := by decide +kernel

theorem rowsSound8_7 (k : Fin GramFunctions.Block2.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form8.terms k).tag (GramFunctions.Block2.form8.terms k).charge GramFunctions.Block2.form7) x := by
  fin_cases k
  · exact rowEval6638 x
  · exact rowEval6639 x
  · exact rowEval6640 x
  · exact rowEval6641 x
  · exact rowEval6642 x
  · exact rowEval6643 x
  · exact rowEval6644 x
  · exact rowEval6645 x
  · exact rowEval6646 x
  · exact rowEval6647 x
  · exact rowEval6648 x
  · exact rowEval6649 x
  · exact rowEval6650 x
  · exact rowEval6651 x
  · exact rowEval6652 x
  · exact rowEval6653 x
  · exact rowEval6654 x
  · exact rowEval6655 x
  · exact rowEval6656 x
  · exact rowEval6657 x
  · exact rowEval6658 x
  · exact rowEval6659 x
  · exact rowEval6660 x
  · exact rowEval6661 x
  · exact rowEval6662 x
  · exact rowEval6663 x
  · exact rowEval6664 x
  · exact rowEval6665 x
  · exact rowEval6666 x
  · exact rowEval6667 x
  · exact rowEval6668 x
  · exact rowEval6669 x
  · exact rowEval6670 x
  · exact rowEval6671 x
  · exact rowEval6672 x
  · exact rowEval6673 x
  · exact rowEval6674 x
  · exact rowEval6675 x
  · exact rowEval6676 x
  · exact rowEval6677 x

theorem entryEval8_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_7 (GramNormalization.eval B) = GramFunctions.Block2.form8.mixedGram GramFunctions.Block2.form7 B := by
  rw [entryCheck8_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form8 GramFunctions.Block2.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_7]

def rows8_8 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6678, row6679, row6680, row6681, row6682, row6683, row6684, row6685, row6686, row6687, row6688, row6689, row6690, row6691, row6692, row6693, row6694, row6695, row6696, row6697, row6698, row6699, row6700, row6701, row6702, row6703, row6704, row6705, row6706, row6707, row6708, row6709, row6710, row6711, row6712, row6713, row6714, row6715, row6716, row6717]

theorem entryCheck8_8 : entry8_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form8.terms k).coefficient) (rows8_8 k)) := by decide +kernel

theorem rowsSound8_8 (k : Fin GramFunctions.Block2.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form8.terms k).tag (GramFunctions.Block2.form8.terms k).charge GramFunctions.Block2.form8) x := by
  fin_cases k
  · exact rowEval6678 x
  · exact rowEval6679 x
  · exact rowEval6680 x
  · exact rowEval6681 x
  · exact rowEval6682 x
  · exact rowEval6683 x
  · exact rowEval6684 x
  · exact rowEval6685 x
  · exact rowEval6686 x
  · exact rowEval6687 x
  · exact rowEval6688 x
  · exact rowEval6689 x
  · exact rowEval6690 x
  · exact rowEval6691 x
  · exact rowEval6692 x
  · exact rowEval6693 x
  · exact rowEval6694 x
  · exact rowEval6695 x
  · exact rowEval6696 x
  · exact rowEval6697 x
  · exact rowEval6698 x
  · exact rowEval6699 x
  · exact rowEval6700 x
  · exact rowEval6701 x
  · exact rowEval6702 x
  · exact rowEval6703 x
  · exact rowEval6704 x
  · exact rowEval6705 x
  · exact rowEval6706 x
  · exact rowEval6707 x
  · exact rowEval6708 x
  · exact rowEval6709 x
  · exact rowEval6710 x
  · exact rowEval6711 x
  · exact rowEval6712 x
  · exact rowEval6713 x
  · exact rowEval6714 x
  · exact rowEval6715 x
  · exact rowEval6716 x
  · exact rowEval6717 x

theorem entryEval8_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_8 (GramNormalization.eval B) = GramFunctions.Block2.form8.mixedGram GramFunctions.Block2.form8 B := by
  rw [entryCheck8_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form8 GramFunctions.Block2.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_8]

end MUB6.Certificate.GramEntries.Block2

end OAI
