import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramRows.Block177
import OAI.Analysis.MutuallyUnbiased.GramRows.Block178
import OAI.Analysis.MutuallyUnbiased.GramRows.Block179
import OAI.Analysis.MutuallyUnbiased.GramRows.Block180
import OAI.Analysis.MutuallyUnbiased.GramRows.Block181
import OAI.Analysis.MutuallyUnbiased.GramRows.Block182

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows11_0 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19604, row19605, row19606, row19607, row19608, row19609, row19610, row19611, row19612, row19613, row19614, row19615, row19616, row19617, row19618, row19619, row19620, row19621, row19622, row19623, row19624, row19625, row19626, row19627, row19628, row19629, row19630, row19631, row19632, row19633, row19634, row19635, row19636, row19637, row19638, row19639, row19640, row19641, row19642, row19643, row19644, row19645, row19646, row19647, row19648, row19649, row19650, row19651, row19652, row19653, row19654, row19655, row19656, row19657, row19658, row19659, row19660, row19661, row19662, row19663]

theorem entryCheck11_0 : entry11_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_0 k)) := by decide +kernel

theorem rowsSound11_0 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval19604 x
  · exact rowEval19605 x
  · exact rowEval19606 x
  · exact rowEval19607 x
  · exact rowEval19608 x
  · exact rowEval19609 x
  · exact rowEval19610 x
  · exact rowEval19611 x
  · exact rowEval19612 x
  · exact rowEval19613 x
  · exact rowEval19614 x
  · exact rowEval19615 x
  · exact rowEval19616 x
  · exact rowEval19617 x
  · exact rowEval19618 x
  · exact rowEval19619 x
  · exact rowEval19620 x
  · exact rowEval19621 x
  · exact rowEval19622 x
  · exact rowEval19623 x
  · exact rowEval19624 x
  · exact rowEval19625 x
  · exact rowEval19626 x
  · exact rowEval19627 x
  · exact rowEval19628 x
  · exact rowEval19629 x
  · exact rowEval19630 x
  · exact rowEval19631 x
  · exact rowEval19632 x
  · exact rowEval19633 x
  · exact rowEval19634 x
  · exact rowEval19635 x
  · exact rowEval19636 x
  · exact rowEval19637 x
  · exact rowEval19638 x
  · exact rowEval19639 x
  · exact rowEval19640 x
  · exact rowEval19641 x
  · exact rowEval19642 x
  · exact rowEval19643 x
  · exact rowEval19644 x
  · exact rowEval19645 x
  · exact rowEval19646 x
  · exact rowEval19647 x
  · exact rowEval19648 x
  · exact rowEval19649 x
  · exact rowEval19650 x
  · exact rowEval19651 x
  · exact rowEval19652 x
  · exact rowEval19653 x
  · exact rowEval19654 x
  · exact rowEval19655 x
  · exact rowEval19656 x
  · exact rowEval19657 x
  · exact rowEval19658 x
  · exact rowEval19659 x
  · exact rowEval19660 x
  · exact rowEval19661 x
  · exact rowEval19662 x
  · exact rowEval19663 x

theorem entryEval11_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_0 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck11_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_0]

def rows11_1 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19664, row19665, row19666, row19667, row19668, row19669, row19670, row19671, row19672, row19673, row19674, row19675, row19676, row19677, row19678, row19679, row19680, row19681, row19682, row19683, row19684, row19685, row19686, row19687, row19688, row19689, row19690, row19691, row19692, row19693, row19694, row19695, row19696, row19697, row19698, row19699, row19700, row19701, row19702, row19703, row19704, row19705, row19706, row19707, row19708, row19709, row19710, row19711, row19712, row19713, row19714, row19715, row19716, row19717, row19718, row19719, row19720, row19721, row19722, row19723]

theorem entryCheck11_1 : entry11_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_1 k)) := by decide +kernel

theorem rowsSound11_1 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval19664 x
  · exact rowEval19665 x
  · exact rowEval19666 x
  · exact rowEval19667 x
  · exact rowEval19668 x
  · exact rowEval19669 x
  · exact rowEval19670 x
  · exact rowEval19671 x
  · exact rowEval19672 x
  · exact rowEval19673 x
  · exact rowEval19674 x
  · exact rowEval19675 x
  · exact rowEval19676 x
  · exact rowEval19677 x
  · exact rowEval19678 x
  · exact rowEval19679 x
  · exact rowEval19680 x
  · exact rowEval19681 x
  · exact rowEval19682 x
  · exact rowEval19683 x
  · exact rowEval19684 x
  · exact rowEval19685 x
  · exact rowEval19686 x
  · exact rowEval19687 x
  · exact rowEval19688 x
  · exact rowEval19689 x
  · exact rowEval19690 x
  · exact rowEval19691 x
  · exact rowEval19692 x
  · exact rowEval19693 x
  · exact rowEval19694 x
  · exact rowEval19695 x
  · exact rowEval19696 x
  · exact rowEval19697 x
  · exact rowEval19698 x
  · exact rowEval19699 x
  · exact rowEval19700 x
  · exact rowEval19701 x
  · exact rowEval19702 x
  · exact rowEval19703 x
  · exact rowEval19704 x
  · exact rowEval19705 x
  · exact rowEval19706 x
  · exact rowEval19707 x
  · exact rowEval19708 x
  · exact rowEval19709 x
  · exact rowEval19710 x
  · exact rowEval19711 x
  · exact rowEval19712 x
  · exact rowEval19713 x
  · exact rowEval19714 x
  · exact rowEval19715 x
  · exact rowEval19716 x
  · exact rowEval19717 x
  · exact rowEval19718 x
  · exact rowEval19719 x
  · exact rowEval19720 x
  · exact rowEval19721 x
  · exact rowEval19722 x
  · exact rowEval19723 x

theorem entryEval11_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_1 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck11_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_1]

def rows11_2 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19724, row19725, row19726, row19727, row19728, row19729, row19730, row19731, row19732, row19733, row19734, row19735, row19736, row19737, row19738, row19739, row19740, row19741, row19742, row19743, row19744, row19745, row19746, row19747, row19748, row19749, row19750, row19751, row19752, row19753, row19754, row19755, row19756, row19757, row19758, row19759, row19760, row19761, row19762, row19763, row19764, row19765, row19766, row19767, row19768, row19769, row19770, row19771, row19772, row19773, row19774, row19775, row19776, row19777, row19778, row19779, row19780, row19781, row19782, row19783]

theorem entryCheck11_2 : entry11_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_2 k)) := by decide +kernel

theorem rowsSound11_2 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval19724 x
  · exact rowEval19725 x
  · exact rowEval19726 x
  · exact rowEval19727 x
  · exact rowEval19728 x
  · exact rowEval19729 x
  · exact rowEval19730 x
  · exact rowEval19731 x
  · exact rowEval19732 x
  · exact rowEval19733 x
  · exact rowEval19734 x
  · exact rowEval19735 x
  · exact rowEval19736 x
  · exact rowEval19737 x
  · exact rowEval19738 x
  · exact rowEval19739 x
  · exact rowEval19740 x
  · exact rowEval19741 x
  · exact rowEval19742 x
  · exact rowEval19743 x
  · exact rowEval19744 x
  · exact rowEval19745 x
  · exact rowEval19746 x
  · exact rowEval19747 x
  · exact rowEval19748 x
  · exact rowEval19749 x
  · exact rowEval19750 x
  · exact rowEval19751 x
  · exact rowEval19752 x
  · exact rowEval19753 x
  · exact rowEval19754 x
  · exact rowEval19755 x
  · exact rowEval19756 x
  · exact rowEval19757 x
  · exact rowEval19758 x
  · exact rowEval19759 x
  · exact rowEval19760 x
  · exact rowEval19761 x
  · exact rowEval19762 x
  · exact rowEval19763 x
  · exact rowEval19764 x
  · exact rowEval19765 x
  · exact rowEval19766 x
  · exact rowEval19767 x
  · exact rowEval19768 x
  · exact rowEval19769 x
  · exact rowEval19770 x
  · exact rowEval19771 x
  · exact rowEval19772 x
  · exact rowEval19773 x
  · exact rowEval19774 x
  · exact rowEval19775 x
  · exact rowEval19776 x
  · exact rowEval19777 x
  · exact rowEval19778 x
  · exact rowEval19779 x
  · exact rowEval19780 x
  · exact rowEval19781 x
  · exact rowEval19782 x
  · exact rowEval19783 x

theorem entryEval11_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_2 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck11_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_2]

def rows11_3 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19784, row19785, row19786, row19787, row19788, row19789, row19790, row19791, row19792, row19793, row19794, row19795, row19796, row19797, row19798, row19799, row19800, row19801, row19802, row19803, row19804, row19805, row19806, row19807, row19808, row19809, row19810, row19811, row19812, row19813, row19814, row19815, row19816, row19817, row19818, row19819, row19820, row19821, row19822, row19823, row19824, row19825, row19826, row19827, row19828, row19829, row19830, row19831, row19832, row19833, row19834, row19835, row19836, row19837, row19838, row19839, row19840, row19841, row19842, row19843]

theorem entryCheck11_3 : entry11_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_3 k)) := by decide +kernel

theorem rowsSound11_3 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval19784 x
  · exact rowEval19785 x
  · exact rowEval19786 x
  · exact rowEval19787 x
  · exact rowEval19788 x
  · exact rowEval19789 x
  · exact rowEval19790 x
  · exact rowEval19791 x
  · exact rowEval19792 x
  · exact rowEval19793 x
  · exact rowEval19794 x
  · exact rowEval19795 x
  · exact rowEval19796 x
  · exact rowEval19797 x
  · exact rowEval19798 x
  · exact rowEval19799 x
  · exact rowEval19800 x
  · exact rowEval19801 x
  · exact rowEval19802 x
  · exact rowEval19803 x
  · exact rowEval19804 x
  · exact rowEval19805 x
  · exact rowEval19806 x
  · exact rowEval19807 x
  · exact rowEval19808 x
  · exact rowEval19809 x
  · exact rowEval19810 x
  · exact rowEval19811 x
  · exact rowEval19812 x
  · exact rowEval19813 x
  · exact rowEval19814 x
  · exact rowEval19815 x
  · exact rowEval19816 x
  · exact rowEval19817 x
  · exact rowEval19818 x
  · exact rowEval19819 x
  · exact rowEval19820 x
  · exact rowEval19821 x
  · exact rowEval19822 x
  · exact rowEval19823 x
  · exact rowEval19824 x
  · exact rowEval19825 x
  · exact rowEval19826 x
  · exact rowEval19827 x
  · exact rowEval19828 x
  · exact rowEval19829 x
  · exact rowEval19830 x
  · exact rowEval19831 x
  · exact rowEval19832 x
  · exact rowEval19833 x
  · exact rowEval19834 x
  · exact rowEval19835 x
  · exact rowEval19836 x
  · exact rowEval19837 x
  · exact rowEval19838 x
  · exact rowEval19839 x
  · exact rowEval19840 x
  · exact rowEval19841 x
  · exact rowEval19842 x
  · exact rowEval19843 x

theorem entryEval11_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_3 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck11_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_3]

def rows11_4 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19844, row19845, row19846, row19847, row19848, row19849, row19850, row19851, row19852, row19853, row19854, row19855, row19856, row19857, row19858, row19859, row19860, row19861, row19862, row19863, row19864, row19865, row19866, row19867, row19868, row19869, row19870, row19871, row19872, row19873, row19874, row19875, row19876, row19877, row19878, row19879, row19880, row19881, row19882, row19883, row19884, row19885, row19886, row19887, row19888, row19889, row19890, row19891, row19892, row19893, row19894, row19895, row19896, row19897, row19898, row19899, row19900, row19901, row19902, row19903]

theorem entryCheck11_4 : entry11_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_4 k)) := by decide +kernel

theorem rowsSound11_4 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval19844 x
  · exact rowEval19845 x
  · exact rowEval19846 x
  · exact rowEval19847 x
  · exact rowEval19848 x
  · exact rowEval19849 x
  · exact rowEval19850 x
  · exact rowEval19851 x
  · exact rowEval19852 x
  · exact rowEval19853 x
  · exact rowEval19854 x
  · exact rowEval19855 x
  · exact rowEval19856 x
  · exact rowEval19857 x
  · exact rowEval19858 x
  · exact rowEval19859 x
  · exact rowEval19860 x
  · exact rowEval19861 x
  · exact rowEval19862 x
  · exact rowEval19863 x
  · exact rowEval19864 x
  · exact rowEval19865 x
  · exact rowEval19866 x
  · exact rowEval19867 x
  · exact rowEval19868 x
  · exact rowEval19869 x
  · exact rowEval19870 x
  · exact rowEval19871 x
  · exact rowEval19872 x
  · exact rowEval19873 x
  · exact rowEval19874 x
  · exact rowEval19875 x
  · exact rowEval19876 x
  · exact rowEval19877 x
  · exact rowEval19878 x
  · exact rowEval19879 x
  · exact rowEval19880 x
  · exact rowEval19881 x
  · exact rowEval19882 x
  · exact rowEval19883 x
  · exact rowEval19884 x
  · exact rowEval19885 x
  · exact rowEval19886 x
  · exact rowEval19887 x
  · exact rowEval19888 x
  · exact rowEval19889 x
  · exact rowEval19890 x
  · exact rowEval19891 x
  · exact rowEval19892 x
  · exact rowEval19893 x
  · exact rowEval19894 x
  · exact rowEval19895 x
  · exact rowEval19896 x
  · exact rowEval19897 x
  · exact rowEval19898 x
  · exact rowEval19899 x
  · exact rowEval19900 x
  · exact rowEval19901 x
  · exact rowEval19902 x
  · exact rowEval19903 x

theorem entryEval11_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_4 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck11_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_4]

def rows11_5 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19904, row19905, row19906, row19907, row19908, row19909, row19910, row19911, row19912, row19913, row19914, row19915, row19916, row19917, row19918, row19919, row19920, row19921, row19922, row19923, row19924, row19925, row19926, row19927, row19928, row19929, row19930, row19931, row19932, row19933, row19934, row19935, row19936, row19937, row19938, row19939, row19940, row19941, row19942, row19943, row19944, row19945, row19946, row19947, row19948, row19949, row19950, row19951, row19952, row19953, row19954, row19955, row19956, row19957, row19958, row19959, row19960, row19961, row19962, row19963]

theorem entryCheck11_5 : entry11_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_5 k)) := by decide +kernel

theorem rowsSound11_5 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form5) x := by
  fin_cases k
  · exact rowEval19904 x
  · exact rowEval19905 x
  · exact rowEval19906 x
  · exact rowEval19907 x
  · exact rowEval19908 x
  · exact rowEval19909 x
  · exact rowEval19910 x
  · exact rowEval19911 x
  · exact rowEval19912 x
  · exact rowEval19913 x
  · exact rowEval19914 x
  · exact rowEval19915 x
  · exact rowEval19916 x
  · exact rowEval19917 x
  · exact rowEval19918 x
  · exact rowEval19919 x
  · exact rowEval19920 x
  · exact rowEval19921 x
  · exact rowEval19922 x
  · exact rowEval19923 x
  · exact rowEval19924 x
  · exact rowEval19925 x
  · exact rowEval19926 x
  · exact rowEval19927 x
  · exact rowEval19928 x
  · exact rowEval19929 x
  · exact rowEval19930 x
  · exact rowEval19931 x
  · exact rowEval19932 x
  · exact rowEval19933 x
  · exact rowEval19934 x
  · exact rowEval19935 x
  · exact rowEval19936 x
  · exact rowEval19937 x
  · exact rowEval19938 x
  · exact rowEval19939 x
  · exact rowEval19940 x
  · exact rowEval19941 x
  · exact rowEval19942 x
  · exact rowEval19943 x
  · exact rowEval19944 x
  · exact rowEval19945 x
  · exact rowEval19946 x
  · exact rowEval19947 x
  · exact rowEval19948 x
  · exact rowEval19949 x
  · exact rowEval19950 x
  · exact rowEval19951 x
  · exact rowEval19952 x
  · exact rowEval19953 x
  · exact rowEval19954 x
  · exact rowEval19955 x
  · exact rowEval19956 x
  · exact rowEval19957 x
  · exact rowEval19958 x
  · exact rowEval19959 x
  · exact rowEval19960 x
  · exact rowEval19961 x
  · exact rowEval19962 x
  · exact rowEval19963 x

theorem entryEval11_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_5 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form5 B := by
  rw [entryCheck11_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_5]

def rows11_6 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19964, row19965, row19966, row19967, row19968, row19969, row19970, row19971, row19972, row19973, row19974, row19975, row19976, row19977, row19978, row19979, row19980, row19981, row19982, row19983, row19984, row19985, row19986, row19987, row19988, row19989, row19990, row19991, row19992, row19993, row19994, row19995, row19996, row19997, row19998, row19999, row20000, row20001, row20002, row20003, row20004, row20005, row20006, row20007, row20008, row20009, row20010, row20011, row20012, row20013, row20014, row20015, row20016, row20017, row20018, row20019, row20020, row20021, row20022, row20023]

theorem entryCheck11_6 : entry11_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_6 k)) := by decide +kernel

theorem rowsSound11_6 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form6) x := by
  fin_cases k
  · exact rowEval19964 x
  · exact rowEval19965 x
  · exact rowEval19966 x
  · exact rowEval19967 x
  · exact rowEval19968 x
  · exact rowEval19969 x
  · exact rowEval19970 x
  · exact rowEval19971 x
  · exact rowEval19972 x
  · exact rowEval19973 x
  · exact rowEval19974 x
  · exact rowEval19975 x
  · exact rowEval19976 x
  · exact rowEval19977 x
  · exact rowEval19978 x
  · exact rowEval19979 x
  · exact rowEval19980 x
  · exact rowEval19981 x
  · exact rowEval19982 x
  · exact rowEval19983 x
  · exact rowEval19984 x
  · exact rowEval19985 x
  · exact rowEval19986 x
  · exact rowEval19987 x
  · exact rowEval19988 x
  · exact rowEval19989 x
  · exact rowEval19990 x
  · exact rowEval19991 x
  · exact rowEval19992 x
  · exact rowEval19993 x
  · exact rowEval19994 x
  · exact rowEval19995 x
  · exact rowEval19996 x
  · exact rowEval19997 x
  · exact rowEval19998 x
  · exact rowEval19999 x
  · exact rowEval20000 x
  · exact rowEval20001 x
  · exact rowEval20002 x
  · exact rowEval20003 x
  · exact rowEval20004 x
  · exact rowEval20005 x
  · exact rowEval20006 x
  · exact rowEval20007 x
  · exact rowEval20008 x
  · exact rowEval20009 x
  · exact rowEval20010 x
  · exact rowEval20011 x
  · exact rowEval20012 x
  · exact rowEval20013 x
  · exact rowEval20014 x
  · exact rowEval20015 x
  · exact rowEval20016 x
  · exact rowEval20017 x
  · exact rowEval20018 x
  · exact rowEval20019 x
  · exact rowEval20020 x
  · exact rowEval20021 x
  · exact rowEval20022 x
  · exact rowEval20023 x

theorem entryEval11_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_6 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form6 B := by
  rw [entryCheck11_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_6]

def rows11_7 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row20024, row20025, row20026, row20027, row20028, row20029, row20030, row20031, row20032, row20033, row20034, row20035, row20036, row20037, row20038, row20039, row20040, row20041, row20042, row20043, row20044, row20045, row20046, row20047, row20048, row20049, row20050, row20051, row20052, row20053, row20054, row20055, row20056, row20057, row20058, row20059, row20060, row20061, row20062, row20063, row20064, row20065, row20066, row20067, row20068, row20069, row20070, row20071, row20072, row20073, row20074, row20075, row20076, row20077, row20078, row20079, row20080, row20081, row20082, row20083]

theorem entryCheck11_7 : entry11_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_7 k)) := by decide +kernel

theorem rowsSound11_7 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form7) x := by
  fin_cases k
  · exact rowEval20024 x
  · exact rowEval20025 x
  · exact rowEval20026 x
  · exact rowEval20027 x
  · exact rowEval20028 x
  · exact rowEval20029 x
  · exact rowEval20030 x
  · exact rowEval20031 x
  · exact rowEval20032 x
  · exact rowEval20033 x
  · exact rowEval20034 x
  · exact rowEval20035 x
  · exact rowEval20036 x
  · exact rowEval20037 x
  · exact rowEval20038 x
  · exact rowEval20039 x
  · exact rowEval20040 x
  · exact rowEval20041 x
  · exact rowEval20042 x
  · exact rowEval20043 x
  · exact rowEval20044 x
  · exact rowEval20045 x
  · exact rowEval20046 x
  · exact rowEval20047 x
  · exact rowEval20048 x
  · exact rowEval20049 x
  · exact rowEval20050 x
  · exact rowEval20051 x
  · exact rowEval20052 x
  · exact rowEval20053 x
  · exact rowEval20054 x
  · exact rowEval20055 x
  · exact rowEval20056 x
  · exact rowEval20057 x
  · exact rowEval20058 x
  · exact rowEval20059 x
  · exact rowEval20060 x
  · exact rowEval20061 x
  · exact rowEval20062 x
  · exact rowEval20063 x
  · exact rowEval20064 x
  · exact rowEval20065 x
  · exact rowEval20066 x
  · exact rowEval20067 x
  · exact rowEval20068 x
  · exact rowEval20069 x
  · exact rowEval20070 x
  · exact rowEval20071 x
  · exact rowEval20072 x
  · exact rowEval20073 x
  · exact rowEval20074 x
  · exact rowEval20075 x
  · exact rowEval20076 x
  · exact rowEval20077 x
  · exact rowEval20078 x
  · exact rowEval20079 x
  · exact rowEval20080 x
  · exact rowEval20081 x
  · exact rowEval20082 x
  · exact rowEval20083 x

theorem entryEval11_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_7 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form7 B := by
  rw [entryCheck11_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_7]

def rows11_8 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row20084, row20085, row20086, row20087, row20088, row20089, row20090, row20091, row20092, row20093, row20094, row20095, row20096, row20097, row20098, row20099, row20100, row20101, row20102, row20103, row20104, row20105, row20106, row20107, row20108, row20109, row20110, row20111, row20112, row20113, row20114, row20115, row20116, row20117, row20118, row20119, row20120, row20121, row20122, row20123, row20124, row20125, row20126, row20127, row20128, row20129, row20130, row20131, row20132, row20133, row20134, row20135, row20136, row20137, row20138, row20139, row20140, row20141, row20142, row20143]

theorem entryCheck11_8 : entry11_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_8 k)) := by decide +kernel

theorem rowsSound11_8 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form8) x := by
  fin_cases k
  · exact rowEval20084 x
  · exact rowEval20085 x
  · exact rowEval20086 x
  · exact rowEval20087 x
  · exact rowEval20088 x
  · exact rowEval20089 x
  · exact rowEval20090 x
  · exact rowEval20091 x
  · exact rowEval20092 x
  · exact rowEval20093 x
  · exact rowEval20094 x
  · exact rowEval20095 x
  · exact rowEval20096 x
  · exact rowEval20097 x
  · exact rowEval20098 x
  · exact rowEval20099 x
  · exact rowEval20100 x
  · exact rowEval20101 x
  · exact rowEval20102 x
  · exact rowEval20103 x
  · exact rowEval20104 x
  · exact rowEval20105 x
  · exact rowEval20106 x
  · exact rowEval20107 x
  · exact rowEval20108 x
  · exact rowEval20109 x
  · exact rowEval20110 x
  · exact rowEval20111 x
  · exact rowEval20112 x
  · exact rowEval20113 x
  · exact rowEval20114 x
  · exact rowEval20115 x
  · exact rowEval20116 x
  · exact rowEval20117 x
  · exact rowEval20118 x
  · exact rowEval20119 x
  · exact rowEval20120 x
  · exact rowEval20121 x
  · exact rowEval20122 x
  · exact rowEval20123 x
  · exact rowEval20124 x
  · exact rowEval20125 x
  · exact rowEval20126 x
  · exact rowEval20127 x
  · exact rowEval20128 x
  · exact rowEval20129 x
  · exact rowEval20130 x
  · exact rowEval20131 x
  · exact rowEval20132 x
  · exact rowEval20133 x
  · exact rowEval20134 x
  · exact rowEval20135 x
  · exact rowEval20136 x
  · exact rowEval20137 x
  · exact rowEval20138 x
  · exact rowEval20139 x
  · exact rowEval20140 x
  · exact rowEval20141 x
  · exact rowEval20142 x
  · exact rowEval20143 x

theorem entryEval11_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_8 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form8 B := by
  rw [entryCheck11_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_8]

def rows11_9 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row20144, row20145, row20146, row20147, row20148, row20149, row20150, row20151, row20152, row20153, row20154, row20155, row20156, row20157, row20158, row20159, row20160, row20161, row20162, row20163, row20164, row20165, row20166, row20167, row20168, row20169, row20170, row20171, row20172, row20173, row20174, row20175, row20176, row20177, row20178, row20179, row20180, row20181, row20182, row20183, row20184, row20185, row20186, row20187, row20188, row20189, row20190, row20191, row20192, row20193, row20194, row20195, row20196, row20197, row20198, row20199, row20200, row20201, row20202, row20203]

theorem entryCheck11_9 : entry11_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_9 k)) := by decide +kernel

theorem rowsSound11_9 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form9) x := by
  fin_cases k
  · exact rowEval20144 x
  · exact rowEval20145 x
  · exact rowEval20146 x
  · exact rowEval20147 x
  · exact rowEval20148 x
  · exact rowEval20149 x
  · exact rowEval20150 x
  · exact rowEval20151 x
  · exact rowEval20152 x
  · exact rowEval20153 x
  · exact rowEval20154 x
  · exact rowEval20155 x
  · exact rowEval20156 x
  · exact rowEval20157 x
  · exact rowEval20158 x
  · exact rowEval20159 x
  · exact rowEval20160 x
  · exact rowEval20161 x
  · exact rowEval20162 x
  · exact rowEval20163 x
  · exact rowEval20164 x
  · exact rowEval20165 x
  · exact rowEval20166 x
  · exact rowEval20167 x
  · exact rowEval20168 x
  · exact rowEval20169 x
  · exact rowEval20170 x
  · exact rowEval20171 x
  · exact rowEval20172 x
  · exact rowEval20173 x
  · exact rowEval20174 x
  · exact rowEval20175 x
  · exact rowEval20176 x
  · exact rowEval20177 x
  · exact rowEval20178 x
  · exact rowEval20179 x
  · exact rowEval20180 x
  · exact rowEval20181 x
  · exact rowEval20182 x
  · exact rowEval20183 x
  · exact rowEval20184 x
  · exact rowEval20185 x
  · exact rowEval20186 x
  · exact rowEval20187 x
  · exact rowEval20188 x
  · exact rowEval20189 x
  · exact rowEval20190 x
  · exact rowEval20191 x
  · exact rowEval20192 x
  · exact rowEval20193 x
  · exact rowEval20194 x
  · exact rowEval20195 x
  · exact rowEval20196 x
  · exact rowEval20197 x
  · exact rowEval20198 x
  · exact rowEval20199 x
  · exact rowEval20200 x
  · exact rowEval20201 x
  · exact rowEval20202 x
  · exact rowEval20203 x

theorem entryEval11_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_9 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form9 B := by
  rw [entryCheck11_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_9]

def rows11_10 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row20204, row20205, row20206, row20207, row20208, row20209, row20210, row20211, row20212, row20213, row20214, row20215, row20216, row20217, row20218, row20219, row20220, row20221, row20222, row20223, row20224, row20225, row20226, row20227, row20228, row20229, row20230, row20231, row20232, row20233, row20234, row20235, row20236, row20237, row20238, row20239, row20240, row20241, row20242, row20243, row20244, row20245, row20246, row20247, row20248, row20249, row20250, row20251, row20252, row20253, row20254, row20255, row20256, row20257, row20258, row20259, row20260, row20261, row20262, row20263]

theorem entryCheck11_10 : entry11_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_10 k)) := by decide +kernel

theorem rowsSound11_10 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form10) x := by
  fin_cases k
  · exact rowEval20204 x
  · exact rowEval20205 x
  · exact rowEval20206 x
  · exact rowEval20207 x
  · exact rowEval20208 x
  · exact rowEval20209 x
  · exact rowEval20210 x
  · exact rowEval20211 x
  · exact rowEval20212 x
  · exact rowEval20213 x
  · exact rowEval20214 x
  · exact rowEval20215 x
  · exact rowEval20216 x
  · exact rowEval20217 x
  · exact rowEval20218 x
  · exact rowEval20219 x
  · exact rowEval20220 x
  · exact rowEval20221 x
  · exact rowEval20222 x
  · exact rowEval20223 x
  · exact rowEval20224 x
  · exact rowEval20225 x
  · exact rowEval20226 x
  · exact rowEval20227 x
  · exact rowEval20228 x
  · exact rowEval20229 x
  · exact rowEval20230 x
  · exact rowEval20231 x
  · exact rowEval20232 x
  · exact rowEval20233 x
  · exact rowEval20234 x
  · exact rowEval20235 x
  · exact rowEval20236 x
  · exact rowEval20237 x
  · exact rowEval20238 x
  · exact rowEval20239 x
  · exact rowEval20240 x
  · exact rowEval20241 x
  · exact rowEval20242 x
  · exact rowEval20243 x
  · exact rowEval20244 x
  · exact rowEval20245 x
  · exact rowEval20246 x
  · exact rowEval20247 x
  · exact rowEval20248 x
  · exact rowEval20249 x
  · exact rowEval20250 x
  · exact rowEval20251 x
  · exact rowEval20252 x
  · exact rowEval20253 x
  · exact rowEval20254 x
  · exact rowEval20255 x
  · exact rowEval20256 x
  · exact rowEval20257 x
  · exact rowEval20258 x
  · exact rowEval20259 x
  · exact rowEval20260 x
  · exact rowEval20261 x
  · exact rowEval20262 x
  · exact rowEval20263 x

theorem entryEval11_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_10 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form10 B := by
  rw [entryCheck11_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_10]

def rows11_11 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row20264, row20265, row20266, row20267, row20268, row20269, row20270, row20271, row20272, row20273, row20274, row20275, row20276, row20277, row20278, row20279, row20280, row20281, row20282, row20283, row20284, row20285, row20286, row20287, row20288, row20289, row20290, row20291, row20292, row20293, row20294, row20295, row20296, row20297, row20298, row20299, row20300, row20301, row20302, row20303, row20304, row20305, row20306, row20307, row20308, row20309, row20310, row20311, row20312, row20313, row20314, row20315, row20316, row20317, row20318, row20319, row20320, row20321, row20322, row20323]

theorem entryCheck11_11 : entry11_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_11 k)) := by decide +kernel

theorem rowsSound11_11 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form11) x := by
  fin_cases k
  · exact rowEval20264 x
  · exact rowEval20265 x
  · exact rowEval20266 x
  · exact rowEval20267 x
  · exact rowEval20268 x
  · exact rowEval20269 x
  · exact rowEval20270 x
  · exact rowEval20271 x
  · exact rowEval20272 x
  · exact rowEval20273 x
  · exact rowEval20274 x
  · exact rowEval20275 x
  · exact rowEval20276 x
  · exact rowEval20277 x
  · exact rowEval20278 x
  · exact rowEval20279 x
  · exact rowEval20280 x
  · exact rowEval20281 x
  · exact rowEval20282 x
  · exact rowEval20283 x
  · exact rowEval20284 x
  · exact rowEval20285 x
  · exact rowEval20286 x
  · exact rowEval20287 x
  · exact rowEval20288 x
  · exact rowEval20289 x
  · exact rowEval20290 x
  · exact rowEval20291 x
  · exact rowEval20292 x
  · exact rowEval20293 x
  · exact rowEval20294 x
  · exact rowEval20295 x
  · exact rowEval20296 x
  · exact rowEval20297 x
  · exact rowEval20298 x
  · exact rowEval20299 x
  · exact rowEval20300 x
  · exact rowEval20301 x
  · exact rowEval20302 x
  · exact rowEval20303 x
  · exact rowEval20304 x
  · exact rowEval20305 x
  · exact rowEval20306 x
  · exact rowEval20307 x
  · exact rowEval20308 x
  · exact rowEval20309 x
  · exact rowEval20310 x
  · exact rowEval20311 x
  · exact rowEval20312 x
  · exact rowEval20313 x
  · exact rowEval20314 x
  · exact rowEval20315 x
  · exact rowEval20316 x
  · exact rowEval20317 x
  · exact rowEval20318 x
  · exact rowEval20319 x
  · exact rowEval20320 x
  · exact rowEval20321 x
  · exact rowEval20322 x
  · exact rowEval20323 x

theorem entryEval11_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_11 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form11 B := by
  rw [entryCheck11_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_11]

end MUB6.Certificate.GramEntries.Block5

end OAI
