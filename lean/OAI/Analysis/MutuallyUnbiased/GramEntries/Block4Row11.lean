import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block138
import OAI.Analysis.MutuallyUnbiased.GramRows.Block139

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows11_0 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14601, row14602, row14603, row14604, row14605, row14606, row14607, row14608, row14609, row14610, row14611, row14612, row14613, row14614, row14615, row14616, row14617, row14618, row14619, row14620]

theorem entryCheck11_0 : entry11_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_0 k)) := by decide +kernel

theorem rowsSound11_0 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval14601 x
  · exact rowEval14602 x
  · exact rowEval14603 x
  · exact rowEval14604 x
  · exact rowEval14605 x
  · exact rowEval14606 x
  · exact rowEval14607 x
  · exact rowEval14608 x
  · exact rowEval14609 x
  · exact rowEval14610 x
  · exact rowEval14611 x
  · exact rowEval14612 x
  · exact rowEval14613 x
  · exact rowEval14614 x
  · exact rowEval14615 x
  · exact rowEval14616 x
  · exact rowEval14617 x
  · exact rowEval14618 x
  · exact rowEval14619 x
  · exact rowEval14620 x

theorem entryEval11_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_0 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck11_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_0]

def rows11_1 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14621, row14622, row14623, row14624, row14625, row14626, row14627, row14628, row14629, row14630, row14631, row14632, row14633, row14634, row14635, row14636, row14637, row14638, row14639, row14640]

theorem entryCheck11_1 : entry11_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_1 k)) := by decide +kernel

theorem rowsSound11_1 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval14621 x
  · exact rowEval14622 x
  · exact rowEval14623 x
  · exact rowEval14624 x
  · exact rowEval14625 x
  · exact rowEval14626 x
  · exact rowEval14627 x
  · exact rowEval14628 x
  · exact rowEval14629 x
  · exact rowEval14630 x
  · exact rowEval14631 x
  · exact rowEval14632 x
  · exact rowEval14633 x
  · exact rowEval14634 x
  · exact rowEval14635 x
  · exact rowEval14636 x
  · exact rowEval14637 x
  · exact rowEval14638 x
  · exact rowEval14639 x
  · exact rowEval14640 x

theorem entryEval11_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_1 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck11_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_1]

def rows11_2 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14641, row14642, row14643, row14644, row14645, row14646, row14647, row14648, row14649, row14650, row14651, row14652, row14653, row14654, row14655, row14656, row14657, row14658, row14659, row14660]

theorem entryCheck11_2 : entry11_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_2 k)) := by decide +kernel

theorem rowsSound11_2 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval14641 x
  · exact rowEval14642 x
  · exact rowEval14643 x
  · exact rowEval14644 x
  · exact rowEval14645 x
  · exact rowEval14646 x
  · exact rowEval14647 x
  · exact rowEval14648 x
  · exact rowEval14649 x
  · exact rowEval14650 x
  · exact rowEval14651 x
  · exact rowEval14652 x
  · exact rowEval14653 x
  · exact rowEval14654 x
  · exact rowEval14655 x
  · exact rowEval14656 x
  · exact rowEval14657 x
  · exact rowEval14658 x
  · exact rowEval14659 x
  · exact rowEval14660 x

theorem entryEval11_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_2 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck11_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_2]

def rows11_3 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14661, row14662, row14663, row14664, row14665, row14666, row14667, row14668, row14669, row14670, row14671, row14672, row14673, row14674, row14675, row14676, row14677, row14678, row14679, row14680]

theorem entryCheck11_3 : entry11_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_3 k)) := by decide +kernel

theorem rowsSound11_3 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval14661 x
  · exact rowEval14662 x
  · exact rowEval14663 x
  · exact rowEval14664 x
  · exact rowEval14665 x
  · exact rowEval14666 x
  · exact rowEval14667 x
  · exact rowEval14668 x
  · exact rowEval14669 x
  · exact rowEval14670 x
  · exact rowEval14671 x
  · exact rowEval14672 x
  · exact rowEval14673 x
  · exact rowEval14674 x
  · exact rowEval14675 x
  · exact rowEval14676 x
  · exact rowEval14677 x
  · exact rowEval14678 x
  · exact rowEval14679 x
  · exact rowEval14680 x

theorem entryEval11_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_3 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck11_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_3]

def rows11_4 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14681, row14682, row14683, row14684, row14685, row14686, row14687, row14688, row14689, row14690, row14691, row14692, row14693, row14694, row14695, row14696, row14697, row14698, row14699, row14700]

theorem entryCheck11_4 : entry11_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_4 k)) := by decide +kernel

theorem rowsSound11_4 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval14681 x
  · exact rowEval14682 x
  · exact rowEval14683 x
  · exact rowEval14684 x
  · exact rowEval14685 x
  · exact rowEval14686 x
  · exact rowEval14687 x
  · exact rowEval14688 x
  · exact rowEval14689 x
  · exact rowEval14690 x
  · exact rowEval14691 x
  · exact rowEval14692 x
  · exact rowEval14693 x
  · exact rowEval14694 x
  · exact rowEval14695 x
  · exact rowEval14696 x
  · exact rowEval14697 x
  · exact rowEval14698 x
  · exact rowEval14699 x
  · exact rowEval14700 x

theorem entryEval11_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_4 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck11_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_4]

def rows11_5 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14701, row14702, row14703, row14704, row14705, row14706, row14707, row14708, row14709, row14710, row14711, row14712, row14713, row14714, row14715, row14716, row14717, row14718, row14719, row14720]

theorem entryCheck11_5 : entry11_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_5 k)) := by decide +kernel

theorem rowsSound11_5 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval14701 x
  · exact rowEval14702 x
  · exact rowEval14703 x
  · exact rowEval14704 x
  · exact rowEval14705 x
  · exact rowEval14706 x
  · exact rowEval14707 x
  · exact rowEval14708 x
  · exact rowEval14709 x
  · exact rowEval14710 x
  · exact rowEval14711 x
  · exact rowEval14712 x
  · exact rowEval14713 x
  · exact rowEval14714 x
  · exact rowEval14715 x
  · exact rowEval14716 x
  · exact rowEval14717 x
  · exact rowEval14718 x
  · exact rowEval14719 x
  · exact rowEval14720 x

theorem entryEval11_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_5 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck11_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_5]

def rows11_6 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14721, row14722, row14723, row14724, row14725, row14726, row14727, row14728, row14729, row14730, row14731, row14732, row14733, row14734, row14735, row14736, row14737, row14738, row14739, row14740]

theorem entryCheck11_6 : entry11_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_6 k)) := by decide +kernel

theorem rowsSound11_6 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval14721 x
  · exact rowEval14722 x
  · exact rowEval14723 x
  · exact rowEval14724 x
  · exact rowEval14725 x
  · exact rowEval14726 x
  · exact rowEval14727 x
  · exact rowEval14728 x
  · exact rowEval14729 x
  · exact rowEval14730 x
  · exact rowEval14731 x
  · exact rowEval14732 x
  · exact rowEval14733 x
  · exact rowEval14734 x
  · exact rowEval14735 x
  · exact rowEval14736 x
  · exact rowEval14737 x
  · exact rowEval14738 x
  · exact rowEval14739 x
  · exact rowEval14740 x

theorem entryEval11_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_6 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck11_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_6]

def rows11_7 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14741, row14742, row14743, row14744, row14745, row14746, row14747, row14748, row14749, row14750, row14751, row14752, row14753, row14754, row14755, row14756, row14757, row14758, row14759, row14760]

theorem entryCheck11_7 : entry11_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_7 k)) := by decide +kernel

theorem rowsSound11_7 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval14741 x
  · exact rowEval14742 x
  · exact rowEval14743 x
  · exact rowEval14744 x
  · exact rowEval14745 x
  · exact rowEval14746 x
  · exact rowEval14747 x
  · exact rowEval14748 x
  · exact rowEval14749 x
  · exact rowEval14750 x
  · exact rowEval14751 x
  · exact rowEval14752 x
  · exact rowEval14753 x
  · exact rowEval14754 x
  · exact rowEval14755 x
  · exact rowEval14756 x
  · exact rowEval14757 x
  · exact rowEval14758 x
  · exact rowEval14759 x
  · exact rowEval14760 x

theorem entryEval11_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_7 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck11_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_7]

def rows11_8 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14761, row14762, row14763, row14764, row14765, row14766, row14767, row14768, row14769, row14770, row14771, row14772, row14773, row14774, row14775, row14776, row14777, row14778, row14779, row14780]

theorem entryCheck11_8 : entry11_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_8 k)) := by decide +kernel

theorem rowsSound11_8 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval14761 x
  · exact rowEval14762 x
  · exact rowEval14763 x
  · exact rowEval14764 x
  · exact rowEval14765 x
  · exact rowEval14766 x
  · exact rowEval14767 x
  · exact rowEval14768 x
  · exact rowEval14769 x
  · exact rowEval14770 x
  · exact rowEval14771 x
  · exact rowEval14772 x
  · exact rowEval14773 x
  · exact rowEval14774 x
  · exact rowEval14775 x
  · exact rowEval14776 x
  · exact rowEval14777 x
  · exact rowEval14778 x
  · exact rowEval14779 x
  · exact rowEval14780 x

theorem entryEval11_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_8 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck11_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_8]

def rows11_9 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14781, row14782, row14783, row14784, row14785, row14786, row14787, row14788, row14789, row14790, row14791, row14792, row14793, row14794, row14795, row14796, row14797, row14798, row14799, row14800]

theorem entryCheck11_9 : entry11_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_9 k)) := by decide +kernel

theorem rowsSound11_9 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval14781 x
  · exact rowEval14782 x
  · exact rowEval14783 x
  · exact rowEval14784 x
  · exact rowEval14785 x
  · exact rowEval14786 x
  · exact rowEval14787 x
  · exact rowEval14788 x
  · exact rowEval14789 x
  · exact rowEval14790 x
  · exact rowEval14791 x
  · exact rowEval14792 x
  · exact rowEval14793 x
  · exact rowEval14794 x
  · exact rowEval14795 x
  · exact rowEval14796 x
  · exact rowEval14797 x
  · exact rowEval14798 x
  · exact rowEval14799 x
  · exact rowEval14800 x

theorem entryEval11_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_9 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck11_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_9]

def rows11_10 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14801, row14802, row14803, row14804, row14805, row14806, row14807, row14808, row14809, row14810, row14811, row14812, row14813, row14814, row14815, row14816, row14817, row14818, row14819, row14820]

theorem entryCheck11_10 : entry11_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_10 k)) := by decide +kernel

theorem rowsSound11_10 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form10) x := by
  fin_cases k
  · exact rowEval14801 x
  · exact rowEval14802 x
  · exact rowEval14803 x
  · exact rowEval14804 x
  · exact rowEval14805 x
  · exact rowEval14806 x
  · exact rowEval14807 x
  · exact rowEval14808 x
  · exact rowEval14809 x
  · exact rowEval14810 x
  · exact rowEval14811 x
  · exact rowEval14812 x
  · exact rowEval14813 x
  · exact rowEval14814 x
  · exact rowEval14815 x
  · exact rowEval14816 x
  · exact rowEval14817 x
  · exact rowEval14818 x
  · exact rowEval14819 x
  · exact rowEval14820 x

theorem entryEval11_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_10 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form10 B := by
  rw [entryCheck11_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_10]

def rows11_11 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14821, row14822, row14823, row14824, row14825, row14826, row14827, row14828, row14829, row14830, row14831, row14832, row14833, row14834, row14835, row14836, row14837, row14838, row14839, row14840]

theorem entryCheck11_11 : entry11_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_11 k)) := by decide +kernel

theorem rowsSound11_11 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval14821 x
  · exact rowEval14822 x
  · exact rowEval14823 x
  · exact rowEval14824 x
  · exact rowEval14825 x
  · exact rowEval14826 x
  · exact rowEval14827 x
  · exact rowEval14828 x
  · exact rowEval14829 x
  · exact rowEval14830 x
  · exact rowEval14831 x
  · exact rowEval14832 x
  · exact rowEval14833 x
  · exact rowEval14834 x
  · exact rowEval14835 x
  · exact rowEval14836 x
  · exact rowEval14837 x
  · exact rowEval14838 x
  · exact rowEval14839 x
  · exact rowEval14840 x

theorem entryEval11_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_11 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck11_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_11]

end MUB6.Certificate.GramEntries.Block4

end OAI
