import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block130
import OAI.Analysis.MutuallyUnbiased.GramRows.Block131
import OAI.Analysis.MutuallyUnbiased.GramRows.Block132

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows6_0 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13593, row13594, row13595, row13596, row13597, row13598, row13599, row13600, row13601, row13602, row13603, row13604, row13605, row13606, row13607, row13608, row13609, row13610, row13611, row13612, row13613, row13614, row13615, row13616, row13617, row13618, row13619, row13620, row13621, row13622, row13623, row13624, row13625, row13626, row13627, row13628]

theorem entryCheck6_0 : entry6_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form6.terms k).coefficient) (rows6_0 k)) := by decide +kernel

theorem rowsSound6_0 (k : Fin GramFunctions.Block4.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form6.terms k).tag (GramFunctions.Block4.form6.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13593 x
  · exact rowEval13594 x
  · exact rowEval13595 x
  · exact rowEval13596 x
  · exact rowEval13597 x
  · exact rowEval13598 x
  · exact rowEval13599 x
  · exact rowEval13600 x
  · exact rowEval13601 x
  · exact rowEval13602 x
  · exact rowEval13603 x
  · exact rowEval13604 x
  · exact rowEval13605 x
  · exact rowEval13606 x
  · exact rowEval13607 x
  · exact rowEval13608 x
  · exact rowEval13609 x
  · exact rowEval13610 x
  · exact rowEval13611 x
  · exact rowEval13612 x
  · exact rowEval13613 x
  · exact rowEval13614 x
  · exact rowEval13615 x
  · exact rowEval13616 x
  · exact rowEval13617 x
  · exact rowEval13618 x
  · exact rowEval13619 x
  · exact rowEval13620 x
  · exact rowEval13621 x
  · exact rowEval13622 x
  · exact rowEval13623 x
  · exact rowEval13624 x
  · exact rowEval13625 x
  · exact rowEval13626 x
  · exact rowEval13627 x
  · exact rowEval13628 x

theorem entryEval6_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_0 (GramNormalization.eval B) = GramFunctions.Block4.form6.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck6_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form6 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_0]

def rows6_1 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13629, row13630, row13631, row13632, row13633, row13634, row13635, row13636, row13637, row13638, row13639, row13640, row13641, row13642, row13643, row13644, row13645, row13646, row13647, row13648, row13649, row13650, row13651, row13652, row13653, row13654, row13655, row13656, row13657, row13658, row13659, row13660, row13661, row13662, row13663, row13664]

theorem entryCheck6_1 : entry6_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form6.terms k).coefficient) (rows6_1 k)) := by decide +kernel

theorem rowsSound6_1 (k : Fin GramFunctions.Block4.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form6.terms k).tag (GramFunctions.Block4.form6.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13629 x
  · exact rowEval13630 x
  · exact rowEval13631 x
  · exact rowEval13632 x
  · exact rowEval13633 x
  · exact rowEval13634 x
  · exact rowEval13635 x
  · exact rowEval13636 x
  · exact rowEval13637 x
  · exact rowEval13638 x
  · exact rowEval13639 x
  · exact rowEval13640 x
  · exact rowEval13641 x
  · exact rowEval13642 x
  · exact rowEval13643 x
  · exact rowEval13644 x
  · exact rowEval13645 x
  · exact rowEval13646 x
  · exact rowEval13647 x
  · exact rowEval13648 x
  · exact rowEval13649 x
  · exact rowEval13650 x
  · exact rowEval13651 x
  · exact rowEval13652 x
  · exact rowEval13653 x
  · exact rowEval13654 x
  · exact rowEval13655 x
  · exact rowEval13656 x
  · exact rowEval13657 x
  · exact rowEval13658 x
  · exact rowEval13659 x
  · exact rowEval13660 x
  · exact rowEval13661 x
  · exact rowEval13662 x
  · exact rowEval13663 x
  · exact rowEval13664 x

theorem entryEval6_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_1 (GramNormalization.eval B) = GramFunctions.Block4.form6.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck6_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form6 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_1]

def rows6_2 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13665, row13666, row13667, row13668, row13669, row13670, row13671, row13672, row13673, row13674, row13675, row13676, row13677, row13678, row13679, row13680, row13681, row13682, row13683, row13684, row13685, row13686, row13687, row13688, row13689, row13690, row13691, row13692, row13693, row13694, row13695, row13696, row13697, row13698, row13699, row13700]

theorem entryCheck6_2 : entry6_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form6.terms k).coefficient) (rows6_2 k)) := by decide +kernel

theorem rowsSound6_2 (k : Fin GramFunctions.Block4.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form6.terms k).tag (GramFunctions.Block4.form6.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval13665 x
  · exact rowEval13666 x
  · exact rowEval13667 x
  · exact rowEval13668 x
  · exact rowEval13669 x
  · exact rowEval13670 x
  · exact rowEval13671 x
  · exact rowEval13672 x
  · exact rowEval13673 x
  · exact rowEval13674 x
  · exact rowEval13675 x
  · exact rowEval13676 x
  · exact rowEval13677 x
  · exact rowEval13678 x
  · exact rowEval13679 x
  · exact rowEval13680 x
  · exact rowEval13681 x
  · exact rowEval13682 x
  · exact rowEval13683 x
  · exact rowEval13684 x
  · exact rowEval13685 x
  · exact rowEval13686 x
  · exact rowEval13687 x
  · exact rowEval13688 x
  · exact rowEval13689 x
  · exact rowEval13690 x
  · exact rowEval13691 x
  · exact rowEval13692 x
  · exact rowEval13693 x
  · exact rowEval13694 x
  · exact rowEval13695 x
  · exact rowEval13696 x
  · exact rowEval13697 x
  · exact rowEval13698 x
  · exact rowEval13699 x
  · exact rowEval13700 x

theorem entryEval6_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_2 (GramNormalization.eval B) = GramFunctions.Block4.form6.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck6_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form6 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_2]

def rows6_3 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13701, row13702, row13703, row13704, row13705, row13706, row13707, row13708, row13709, row13710, row13711, row13712, row13713, row13714, row13715, row13716, row13717, row13718, row13719, row13720, row13721, row13722, row13723, row13724, row13725, row13726, row13727, row13728, row13729, row13730, row13731, row13732, row13733, row13734, row13735, row13736]

theorem entryCheck6_3 : entry6_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form6.terms k).coefficient) (rows6_3 k)) := by decide +kernel

theorem rowsSound6_3 (k : Fin GramFunctions.Block4.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form6.terms k).tag (GramFunctions.Block4.form6.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval13701 x
  · exact rowEval13702 x
  · exact rowEval13703 x
  · exact rowEval13704 x
  · exact rowEval13705 x
  · exact rowEval13706 x
  · exact rowEval13707 x
  · exact rowEval13708 x
  · exact rowEval13709 x
  · exact rowEval13710 x
  · exact rowEval13711 x
  · exact rowEval13712 x
  · exact rowEval13713 x
  · exact rowEval13714 x
  · exact rowEval13715 x
  · exact rowEval13716 x
  · exact rowEval13717 x
  · exact rowEval13718 x
  · exact rowEval13719 x
  · exact rowEval13720 x
  · exact rowEval13721 x
  · exact rowEval13722 x
  · exact rowEval13723 x
  · exact rowEval13724 x
  · exact rowEval13725 x
  · exact rowEval13726 x
  · exact rowEval13727 x
  · exact rowEval13728 x
  · exact rowEval13729 x
  · exact rowEval13730 x
  · exact rowEval13731 x
  · exact rowEval13732 x
  · exact rowEval13733 x
  · exact rowEval13734 x
  · exact rowEval13735 x
  · exact rowEval13736 x

theorem entryEval6_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_3 (GramNormalization.eval B) = GramFunctions.Block4.form6.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck6_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form6 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_3]

def rows6_4 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13737, row13738, row13739, row13740, row13741, row13742, row13743, row13744, row13745, row13746, row13747, row13748, row13749, row13750, row13751, row13752, row13753, row13754, row13755, row13756, row13757, row13758, row13759, row13760, row13761, row13762, row13763, row13764, row13765, row13766, row13767, row13768, row13769, row13770, row13771, row13772]

theorem entryCheck6_4 : entry6_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form6.terms k).coefficient) (rows6_4 k)) := by decide +kernel

theorem rowsSound6_4 (k : Fin GramFunctions.Block4.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form6.terms k).tag (GramFunctions.Block4.form6.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval13737 x
  · exact rowEval13738 x
  · exact rowEval13739 x
  · exact rowEval13740 x
  · exact rowEval13741 x
  · exact rowEval13742 x
  · exact rowEval13743 x
  · exact rowEval13744 x
  · exact rowEval13745 x
  · exact rowEval13746 x
  · exact rowEval13747 x
  · exact rowEval13748 x
  · exact rowEval13749 x
  · exact rowEval13750 x
  · exact rowEval13751 x
  · exact rowEval13752 x
  · exact rowEval13753 x
  · exact rowEval13754 x
  · exact rowEval13755 x
  · exact rowEval13756 x
  · exact rowEval13757 x
  · exact rowEval13758 x
  · exact rowEval13759 x
  · exact rowEval13760 x
  · exact rowEval13761 x
  · exact rowEval13762 x
  · exact rowEval13763 x
  · exact rowEval13764 x
  · exact rowEval13765 x
  · exact rowEval13766 x
  · exact rowEval13767 x
  · exact rowEval13768 x
  · exact rowEval13769 x
  · exact rowEval13770 x
  · exact rowEval13771 x
  · exact rowEval13772 x

theorem entryEval6_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_4 (GramNormalization.eval B) = GramFunctions.Block4.form6.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck6_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form6 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_4]

def rows6_5 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13773, row13774, row13775, row13776, row13777, row13778, row13779, row13780, row13781, row13782, row13783, row13784, row13785, row13786, row13787, row13788, row13789, row13790, row13791, row13792, row13793, row13794, row13795, row13796, row13797, row13798, row13799, row13800, row13801, row13802, row13803, row13804, row13805, row13806, row13807, row13808]

theorem entryCheck6_5 : entry6_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form6.terms k).coefficient) (rows6_5 k)) := by decide +kernel

theorem rowsSound6_5 (k : Fin GramFunctions.Block4.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form6.terms k).tag (GramFunctions.Block4.form6.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval13773 x
  · exact rowEval13774 x
  · exact rowEval13775 x
  · exact rowEval13776 x
  · exact rowEval13777 x
  · exact rowEval13778 x
  · exact rowEval13779 x
  · exact rowEval13780 x
  · exact rowEval13781 x
  · exact rowEval13782 x
  · exact rowEval13783 x
  · exact rowEval13784 x
  · exact rowEval13785 x
  · exact rowEval13786 x
  · exact rowEval13787 x
  · exact rowEval13788 x
  · exact rowEval13789 x
  · exact rowEval13790 x
  · exact rowEval13791 x
  · exact rowEval13792 x
  · exact rowEval13793 x
  · exact rowEval13794 x
  · exact rowEval13795 x
  · exact rowEval13796 x
  · exact rowEval13797 x
  · exact rowEval13798 x
  · exact rowEval13799 x
  · exact rowEval13800 x
  · exact rowEval13801 x
  · exact rowEval13802 x
  · exact rowEval13803 x
  · exact rowEval13804 x
  · exact rowEval13805 x
  · exact rowEval13806 x
  · exact rowEval13807 x
  · exact rowEval13808 x

theorem entryEval6_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_5 (GramNormalization.eval B) = GramFunctions.Block4.form6.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck6_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form6 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_5]

def rows6_6 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13809, row13810, row13811, row13812, row13813, row13814, row13815, row13816, row13817, row13818, row13819, row13820, row13821, row13822, row13823, row13824, row13825, row13826, row13827, row13828, row13829, row13830, row13831, row13832, row13833, row13834, row13835, row13836, row13837, row13838, row13839, row13840, row13841, row13842, row13843, row13844]

theorem entryCheck6_6 : entry6_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form6.terms k).coefficient) (rows6_6 k)) := by decide +kernel

theorem rowsSound6_6 (k : Fin GramFunctions.Block4.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form6.terms k).tag (GramFunctions.Block4.form6.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval13809 x
  · exact rowEval13810 x
  · exact rowEval13811 x
  · exact rowEval13812 x
  · exact rowEval13813 x
  · exact rowEval13814 x
  · exact rowEval13815 x
  · exact rowEval13816 x
  · exact rowEval13817 x
  · exact rowEval13818 x
  · exact rowEval13819 x
  · exact rowEval13820 x
  · exact rowEval13821 x
  · exact rowEval13822 x
  · exact rowEval13823 x
  · exact rowEval13824 x
  · exact rowEval13825 x
  · exact rowEval13826 x
  · exact rowEval13827 x
  · exact rowEval13828 x
  · exact rowEval13829 x
  · exact rowEval13830 x
  · exact rowEval13831 x
  · exact rowEval13832 x
  · exact rowEval13833 x
  · exact rowEval13834 x
  · exact rowEval13835 x
  · exact rowEval13836 x
  · exact rowEval13837 x
  · exact rowEval13838 x
  · exact rowEval13839 x
  · exact rowEval13840 x
  · exact rowEval13841 x
  · exact rowEval13842 x
  · exact rowEval13843 x
  · exact rowEval13844 x

theorem entryEval6_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_6 (GramNormalization.eval B) = GramFunctions.Block4.form6.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck6_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form6 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_6]

end MUB6.Certificate.GramEntries.Block4

end OAI
