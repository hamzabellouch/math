import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramRows.Block76
import OAI.Analysis.MutuallyUnbiased.GramRows.Block77
import OAI.Analysis.MutuallyUnbiased.GramRows.Block78

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows9_0 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6718, row6719, row6720, row6721, row6722, row6723, row6724, row6725, row6726, row6727, row6728, row6729, row6730, row6731, row6732, row6733, row6734, row6735, row6736, row6737, row6738, row6739, row6740, row6741, row6742, row6743, row6744, row6745, row6746, row6747]

theorem entryCheck9_0 : entry9_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form9.terms k).coefficient) (rows9_0 k)) := by decide +kernel

theorem rowsSound9_0 (k : Fin GramFunctions.Block2.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form9.terms k).tag (GramFunctions.Block2.form9.terms k).charge GramFunctions.Block2.form0) x := by
  fin_cases k
  · exact rowEval6718 x
  · exact rowEval6719 x
  · exact rowEval6720 x
  · exact rowEval6721 x
  · exact rowEval6722 x
  · exact rowEval6723 x
  · exact rowEval6724 x
  · exact rowEval6725 x
  · exact rowEval6726 x
  · exact rowEval6727 x
  · exact rowEval6728 x
  · exact rowEval6729 x
  · exact rowEval6730 x
  · exact rowEval6731 x
  · exact rowEval6732 x
  · exact rowEval6733 x
  · exact rowEval6734 x
  · exact rowEval6735 x
  · exact rowEval6736 x
  · exact rowEval6737 x
  · exact rowEval6738 x
  · exact rowEval6739 x
  · exact rowEval6740 x
  · exact rowEval6741 x
  · exact rowEval6742 x
  · exact rowEval6743 x
  · exact rowEval6744 x
  · exact rowEval6745 x
  · exact rowEval6746 x
  · exact rowEval6747 x

theorem entryEval9_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_0 (GramNormalization.eval B) = GramFunctions.Block2.form9.mixedGram GramFunctions.Block2.form0 B := by
  rw [entryCheck9_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form9 GramFunctions.Block2.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_0]

def rows9_1 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6748, row6749, row6750, row6751, row6752, row6753, row6754, row6755, row6756, row6757, row6758, row6759, row6760, row6761, row6762, row6763, row6764, row6765, row6766, row6767, row6768, row6769, row6770, row6771, row6772, row6773, row6774, row6775, row6776, row6777]

theorem entryCheck9_1 : entry9_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form9.terms k).coefficient) (rows9_1 k)) := by decide +kernel

theorem rowsSound9_1 (k : Fin GramFunctions.Block2.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form9.terms k).tag (GramFunctions.Block2.form9.terms k).charge GramFunctions.Block2.form1) x := by
  fin_cases k
  · exact rowEval6748 x
  · exact rowEval6749 x
  · exact rowEval6750 x
  · exact rowEval6751 x
  · exact rowEval6752 x
  · exact rowEval6753 x
  · exact rowEval6754 x
  · exact rowEval6755 x
  · exact rowEval6756 x
  · exact rowEval6757 x
  · exact rowEval6758 x
  · exact rowEval6759 x
  · exact rowEval6760 x
  · exact rowEval6761 x
  · exact rowEval6762 x
  · exact rowEval6763 x
  · exact rowEval6764 x
  · exact rowEval6765 x
  · exact rowEval6766 x
  · exact rowEval6767 x
  · exact rowEval6768 x
  · exact rowEval6769 x
  · exact rowEval6770 x
  · exact rowEval6771 x
  · exact rowEval6772 x
  · exact rowEval6773 x
  · exact rowEval6774 x
  · exact rowEval6775 x
  · exact rowEval6776 x
  · exact rowEval6777 x

theorem entryEval9_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_1 (GramNormalization.eval B) = GramFunctions.Block2.form9.mixedGram GramFunctions.Block2.form1 B := by
  rw [entryCheck9_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form9 GramFunctions.Block2.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_1]

def rows9_2 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6778, row6779, row6780, row6781, row6782, row6783, row6784, row6785, row6786, row6787, row6788, row6789, row6790, row6791, row6792, row6793, row6794, row6795, row6796, row6797, row6798, row6799, row6800, row6801, row6802, row6803, row6804, row6805, row6806, row6807]

theorem entryCheck9_2 : entry9_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form9.terms k).coefficient) (rows9_2 k)) := by decide +kernel

theorem rowsSound9_2 (k : Fin GramFunctions.Block2.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form9.terms k).tag (GramFunctions.Block2.form9.terms k).charge GramFunctions.Block2.form2) x := by
  fin_cases k
  · exact rowEval6778 x
  · exact rowEval6779 x
  · exact rowEval6780 x
  · exact rowEval6781 x
  · exact rowEval6782 x
  · exact rowEval6783 x
  · exact rowEval6784 x
  · exact rowEval6785 x
  · exact rowEval6786 x
  · exact rowEval6787 x
  · exact rowEval6788 x
  · exact rowEval6789 x
  · exact rowEval6790 x
  · exact rowEval6791 x
  · exact rowEval6792 x
  · exact rowEval6793 x
  · exact rowEval6794 x
  · exact rowEval6795 x
  · exact rowEval6796 x
  · exact rowEval6797 x
  · exact rowEval6798 x
  · exact rowEval6799 x
  · exact rowEval6800 x
  · exact rowEval6801 x
  · exact rowEval6802 x
  · exact rowEval6803 x
  · exact rowEval6804 x
  · exact rowEval6805 x
  · exact rowEval6806 x
  · exact rowEval6807 x

theorem entryEval9_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_2 (GramNormalization.eval B) = GramFunctions.Block2.form9.mixedGram GramFunctions.Block2.form2 B := by
  rw [entryCheck9_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form9 GramFunctions.Block2.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_2]

def rows9_3 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6808, row6809, row6810, row6811, row6812, row6813, row6814, row6815, row6816, row6817, row6818, row6819, row6820, row6821, row6822, row6823, row6824, row6825, row6826, row6827, row6828, row6829, row6830, row6831, row6832, row6833, row6834, row6835, row6836, row6837]

theorem entryCheck9_3 : entry9_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form9.terms k).coefficient) (rows9_3 k)) := by decide +kernel

theorem rowsSound9_3 (k : Fin GramFunctions.Block2.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form9.terms k).tag (GramFunctions.Block2.form9.terms k).charge GramFunctions.Block2.form3) x := by
  fin_cases k
  · exact rowEval6808 x
  · exact rowEval6809 x
  · exact rowEval6810 x
  · exact rowEval6811 x
  · exact rowEval6812 x
  · exact rowEval6813 x
  · exact rowEval6814 x
  · exact rowEval6815 x
  · exact rowEval6816 x
  · exact rowEval6817 x
  · exact rowEval6818 x
  · exact rowEval6819 x
  · exact rowEval6820 x
  · exact rowEval6821 x
  · exact rowEval6822 x
  · exact rowEval6823 x
  · exact rowEval6824 x
  · exact rowEval6825 x
  · exact rowEval6826 x
  · exact rowEval6827 x
  · exact rowEval6828 x
  · exact rowEval6829 x
  · exact rowEval6830 x
  · exact rowEval6831 x
  · exact rowEval6832 x
  · exact rowEval6833 x
  · exact rowEval6834 x
  · exact rowEval6835 x
  · exact rowEval6836 x
  · exact rowEval6837 x

theorem entryEval9_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_3 (GramNormalization.eval B) = GramFunctions.Block2.form9.mixedGram GramFunctions.Block2.form3 B := by
  rw [entryCheck9_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form9 GramFunctions.Block2.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_3]

def rows9_4 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6838, row6839, row6840, row6841, row6842, row6843, row6844, row6845, row6846, row6847, row6848, row6849, row6850, row6851, row6852, row6853, row6854, row6855, row6856, row6857, row6858, row6859, row6860, row6861, row6862, row6863, row6864, row6865, row6866, row6867]

theorem entryCheck9_4 : entry9_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form9.terms k).coefficient) (rows9_4 k)) := by decide +kernel

theorem rowsSound9_4 (k : Fin GramFunctions.Block2.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form9.terms k).tag (GramFunctions.Block2.form9.terms k).charge GramFunctions.Block2.form4) x := by
  fin_cases k
  · exact rowEval6838 x
  · exact rowEval6839 x
  · exact rowEval6840 x
  · exact rowEval6841 x
  · exact rowEval6842 x
  · exact rowEval6843 x
  · exact rowEval6844 x
  · exact rowEval6845 x
  · exact rowEval6846 x
  · exact rowEval6847 x
  · exact rowEval6848 x
  · exact rowEval6849 x
  · exact rowEval6850 x
  · exact rowEval6851 x
  · exact rowEval6852 x
  · exact rowEval6853 x
  · exact rowEval6854 x
  · exact rowEval6855 x
  · exact rowEval6856 x
  · exact rowEval6857 x
  · exact rowEval6858 x
  · exact rowEval6859 x
  · exact rowEval6860 x
  · exact rowEval6861 x
  · exact rowEval6862 x
  · exact rowEval6863 x
  · exact rowEval6864 x
  · exact rowEval6865 x
  · exact rowEval6866 x
  · exact rowEval6867 x

theorem entryEval9_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_4 (GramNormalization.eval B) = GramFunctions.Block2.form9.mixedGram GramFunctions.Block2.form4 B := by
  rw [entryCheck9_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form9 GramFunctions.Block2.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_4]

def rows9_5 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6868, row6869, row6870, row6871, row6872, row6873, row6874, row6875, row6876, row6877, row6878, row6879, row6880, row6881, row6882, row6883, row6884, row6885, row6886, row6887, row6888, row6889, row6890, row6891, row6892, row6893, row6894, row6895, row6896, row6897]

theorem entryCheck9_5 : entry9_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form9.terms k).coefficient) (rows9_5 k)) := by decide +kernel

theorem rowsSound9_5 (k : Fin GramFunctions.Block2.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form9.terms k).tag (GramFunctions.Block2.form9.terms k).charge GramFunctions.Block2.form5) x := by
  fin_cases k
  · exact rowEval6868 x
  · exact rowEval6869 x
  · exact rowEval6870 x
  · exact rowEval6871 x
  · exact rowEval6872 x
  · exact rowEval6873 x
  · exact rowEval6874 x
  · exact rowEval6875 x
  · exact rowEval6876 x
  · exact rowEval6877 x
  · exact rowEval6878 x
  · exact rowEval6879 x
  · exact rowEval6880 x
  · exact rowEval6881 x
  · exact rowEval6882 x
  · exact rowEval6883 x
  · exact rowEval6884 x
  · exact rowEval6885 x
  · exact rowEval6886 x
  · exact rowEval6887 x
  · exact rowEval6888 x
  · exact rowEval6889 x
  · exact rowEval6890 x
  · exact rowEval6891 x
  · exact rowEval6892 x
  · exact rowEval6893 x
  · exact rowEval6894 x
  · exact rowEval6895 x
  · exact rowEval6896 x
  · exact rowEval6897 x

theorem entryEval9_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_5 (GramNormalization.eval B) = GramFunctions.Block2.form9.mixedGram GramFunctions.Block2.form5 B := by
  rw [entryCheck9_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form9 GramFunctions.Block2.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_5]

def rows9_6 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6898, row6899, row6900, row6901, row6902, row6903, row6904, row6905, row6906, row6907, row6908, row6909, row6910, row6911, row6912, row6913, row6914, row6915, row6916, row6917, row6918, row6919, row6920, row6921, row6922, row6923, row6924, row6925, row6926, row6927]

theorem entryCheck9_6 : entry9_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form9.terms k).coefficient) (rows9_6 k)) := by decide +kernel

theorem rowsSound9_6 (k : Fin GramFunctions.Block2.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form9.terms k).tag (GramFunctions.Block2.form9.terms k).charge GramFunctions.Block2.form6) x := by
  fin_cases k
  · exact rowEval6898 x
  · exact rowEval6899 x
  · exact rowEval6900 x
  · exact rowEval6901 x
  · exact rowEval6902 x
  · exact rowEval6903 x
  · exact rowEval6904 x
  · exact rowEval6905 x
  · exact rowEval6906 x
  · exact rowEval6907 x
  · exact rowEval6908 x
  · exact rowEval6909 x
  · exact rowEval6910 x
  · exact rowEval6911 x
  · exact rowEval6912 x
  · exact rowEval6913 x
  · exact rowEval6914 x
  · exact rowEval6915 x
  · exact rowEval6916 x
  · exact rowEval6917 x
  · exact rowEval6918 x
  · exact rowEval6919 x
  · exact rowEval6920 x
  · exact rowEval6921 x
  · exact rowEval6922 x
  · exact rowEval6923 x
  · exact rowEval6924 x
  · exact rowEval6925 x
  · exact rowEval6926 x
  · exact rowEval6927 x

theorem entryEval9_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_6 (GramNormalization.eval B) = GramFunctions.Block2.form9.mixedGram GramFunctions.Block2.form6 B := by
  rw [entryCheck9_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form9 GramFunctions.Block2.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_6]

def rows9_7 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6928, row6929, row6930, row6931, row6932, row6933, row6934, row6935, row6936, row6937, row6938, row6939, row6940, row6941, row6942, row6943, row6944, row6945, row6946, row6947, row6948, row6949, row6950, row6951, row6952, row6953, row6954, row6955, row6956, row6957]

theorem entryCheck9_7 : entry9_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form9.terms k).coefficient) (rows9_7 k)) := by decide +kernel

theorem rowsSound9_7 (k : Fin GramFunctions.Block2.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form9.terms k).tag (GramFunctions.Block2.form9.terms k).charge GramFunctions.Block2.form7) x := by
  fin_cases k
  · exact rowEval6928 x
  · exact rowEval6929 x
  · exact rowEval6930 x
  · exact rowEval6931 x
  · exact rowEval6932 x
  · exact rowEval6933 x
  · exact rowEval6934 x
  · exact rowEval6935 x
  · exact rowEval6936 x
  · exact rowEval6937 x
  · exact rowEval6938 x
  · exact rowEval6939 x
  · exact rowEval6940 x
  · exact rowEval6941 x
  · exact rowEval6942 x
  · exact rowEval6943 x
  · exact rowEval6944 x
  · exact rowEval6945 x
  · exact rowEval6946 x
  · exact rowEval6947 x
  · exact rowEval6948 x
  · exact rowEval6949 x
  · exact rowEval6950 x
  · exact rowEval6951 x
  · exact rowEval6952 x
  · exact rowEval6953 x
  · exact rowEval6954 x
  · exact rowEval6955 x
  · exact rowEval6956 x
  · exact rowEval6957 x

theorem entryEval9_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_7 (GramNormalization.eval B) = GramFunctions.Block2.form9.mixedGram GramFunctions.Block2.form7 B := by
  rw [entryCheck9_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form9 GramFunctions.Block2.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_7]

def rows9_8 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6958, row6959, row6960, row6961, row6962, row6963, row6964, row6965, row6966, row6967, row6968, row6969, row6970, row6971, row6972, row6973, row6974, row6975, row6976, row6977, row6978, row6979, row6980, row6981, row6982, row6983, row6984, row6985, row6986, row6987]

theorem entryCheck9_8 : entry9_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form9.terms k).coefficient) (rows9_8 k)) := by decide +kernel

theorem rowsSound9_8 (k : Fin GramFunctions.Block2.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form9.terms k).tag (GramFunctions.Block2.form9.terms k).charge GramFunctions.Block2.form8) x := by
  fin_cases k
  · exact rowEval6958 x
  · exact rowEval6959 x
  · exact rowEval6960 x
  · exact rowEval6961 x
  · exact rowEval6962 x
  · exact rowEval6963 x
  · exact rowEval6964 x
  · exact rowEval6965 x
  · exact rowEval6966 x
  · exact rowEval6967 x
  · exact rowEval6968 x
  · exact rowEval6969 x
  · exact rowEval6970 x
  · exact rowEval6971 x
  · exact rowEval6972 x
  · exact rowEval6973 x
  · exact rowEval6974 x
  · exact rowEval6975 x
  · exact rowEval6976 x
  · exact rowEval6977 x
  · exact rowEval6978 x
  · exact rowEval6979 x
  · exact rowEval6980 x
  · exact rowEval6981 x
  · exact rowEval6982 x
  · exact rowEval6983 x
  · exact rowEval6984 x
  · exact rowEval6985 x
  · exact rowEval6986 x
  · exact rowEval6987 x

theorem entryEval9_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_8 (GramNormalization.eval B) = GramFunctions.Block2.form9.mixedGram GramFunctions.Block2.form8 B := by
  rw [entryCheck9_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form9 GramFunctions.Block2.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_8]

def rows9_9 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6988, row6989, row6990, row6991, row6992, row6993, row6994, row6995, row6996, row6997, row6998, row6999, row7000, row7001, row7002, row7003, row7004, row7005, row7006, row7007, row7008, row7009, row7010, row7011, row7012, row7013, row7014, row7015, row7016, row7017]

theorem entryCheck9_9 : entry9_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form9.terms k).coefficient) (rows9_9 k)) := by decide +kernel

theorem rowsSound9_9 (k : Fin GramFunctions.Block2.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form9.terms k).tag (GramFunctions.Block2.form9.terms k).charge GramFunctions.Block2.form9) x := by
  fin_cases k
  · exact rowEval6988 x
  · exact rowEval6989 x
  · exact rowEval6990 x
  · exact rowEval6991 x
  · exact rowEval6992 x
  · exact rowEval6993 x
  · exact rowEval6994 x
  · exact rowEval6995 x
  · exact rowEval6996 x
  · exact rowEval6997 x
  · exact rowEval6998 x
  · exact rowEval6999 x
  · exact rowEval7000 x
  · exact rowEval7001 x
  · exact rowEval7002 x
  · exact rowEval7003 x
  · exact rowEval7004 x
  · exact rowEval7005 x
  · exact rowEval7006 x
  · exact rowEval7007 x
  · exact rowEval7008 x
  · exact rowEval7009 x
  · exact rowEval7010 x
  · exact rowEval7011 x
  · exact rowEval7012 x
  · exact rowEval7013 x
  · exact rowEval7014 x
  · exact rowEval7015 x
  · exact rowEval7016 x
  · exact rowEval7017 x

theorem entryEval9_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_9 (GramNormalization.eval B) = GramFunctions.Block2.form9.mixedGram GramFunctions.Block2.form9 B := by
  rw [entryCheck9_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form9 GramFunctions.Block2.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_9]

end MUB6.Certificate.GramEntries.Block2

end OAI
