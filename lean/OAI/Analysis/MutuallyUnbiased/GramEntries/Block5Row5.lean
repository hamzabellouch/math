import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramRows.Block170
import OAI.Analysis.MutuallyUnbiased.GramRows.Block171

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows5_0 : Fin GramFunctions.Block5.form5.size → Integer.Sparse Key := ![row18759, row18760, row18761, row18762, row18763, row18764, row18765, row18766, row18767, row18768, row18769, row18770, row18771, row18772, row18773, row18774, row18775, row18776, row18777, row18778, row18779, row18780, row18781, row18782, row18783, row18784, row18785, row18786, row18787, row18788]

theorem entryCheck5_0 : entry5_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form5.terms k).coefficient) (rows5_0 k)) := by decide +kernel

theorem rowsSound5_0 (k : Fin GramFunctions.Block5.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form5.terms k).tag (GramFunctions.Block5.form5.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18759 x
  · exact rowEval18760 x
  · exact rowEval18761 x
  · exact rowEval18762 x
  · exact rowEval18763 x
  · exact rowEval18764 x
  · exact rowEval18765 x
  · exact rowEval18766 x
  · exact rowEval18767 x
  · exact rowEval18768 x
  · exact rowEval18769 x
  · exact rowEval18770 x
  · exact rowEval18771 x
  · exact rowEval18772 x
  · exact rowEval18773 x
  · exact rowEval18774 x
  · exact rowEval18775 x
  · exact rowEval18776 x
  · exact rowEval18777 x
  · exact rowEval18778 x
  · exact rowEval18779 x
  · exact rowEval18780 x
  · exact rowEval18781 x
  · exact rowEval18782 x
  · exact rowEval18783 x
  · exact rowEval18784 x
  · exact rowEval18785 x
  · exact rowEval18786 x
  · exact rowEval18787 x
  · exact rowEval18788 x

theorem entryEval5_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_0 (GramNormalization.eval B) = GramFunctions.Block5.form5.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck5_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form5 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_0]

def rows5_1 : Fin GramFunctions.Block5.form5.size → Integer.Sparse Key := ![row18789, row18790, row18791, row18792, row18793, row18794, row18795, row18796, row18797, row18798, row18799, row18800, row18801, row18802, row18803, row18804, row18805, row18806, row18807, row18808, row18809, row18810, row18811, row18812, row18813, row18814, row18815, row18816, row18817, row18818]

theorem entryCheck5_1 : entry5_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form5.terms k).coefficient) (rows5_1 k)) := by decide +kernel

theorem rowsSound5_1 (k : Fin GramFunctions.Block5.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form5.terms k).tag (GramFunctions.Block5.form5.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval18789 x
  · exact rowEval18790 x
  · exact rowEval18791 x
  · exact rowEval18792 x
  · exact rowEval18793 x
  · exact rowEval18794 x
  · exact rowEval18795 x
  · exact rowEval18796 x
  · exact rowEval18797 x
  · exact rowEval18798 x
  · exact rowEval18799 x
  · exact rowEval18800 x
  · exact rowEval18801 x
  · exact rowEval18802 x
  · exact rowEval18803 x
  · exact rowEval18804 x
  · exact rowEval18805 x
  · exact rowEval18806 x
  · exact rowEval18807 x
  · exact rowEval18808 x
  · exact rowEval18809 x
  · exact rowEval18810 x
  · exact rowEval18811 x
  · exact rowEval18812 x
  · exact rowEval18813 x
  · exact rowEval18814 x
  · exact rowEval18815 x
  · exact rowEval18816 x
  · exact rowEval18817 x
  · exact rowEval18818 x

theorem entryEval5_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_1 (GramNormalization.eval B) = GramFunctions.Block5.form5.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck5_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form5 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_1]

def rows5_2 : Fin GramFunctions.Block5.form5.size → Integer.Sparse Key := ![row18819, row18820, row18821, row18822, row18823, row18824, row18825, row18826, row18827, row18828, row18829, row18830, row18831, row18832, row18833, row18834, row18835, row18836, row18837, row18838, row18839, row18840, row18841, row18842, row18843, row18844, row18845, row18846, row18847, row18848]

theorem entryCheck5_2 : entry5_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form5.terms k).coefficient) (rows5_2 k)) := by decide +kernel

theorem rowsSound5_2 (k : Fin GramFunctions.Block5.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form5.terms k).tag (GramFunctions.Block5.form5.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval18819 x
  · exact rowEval18820 x
  · exact rowEval18821 x
  · exact rowEval18822 x
  · exact rowEval18823 x
  · exact rowEval18824 x
  · exact rowEval18825 x
  · exact rowEval18826 x
  · exact rowEval18827 x
  · exact rowEval18828 x
  · exact rowEval18829 x
  · exact rowEval18830 x
  · exact rowEval18831 x
  · exact rowEval18832 x
  · exact rowEval18833 x
  · exact rowEval18834 x
  · exact rowEval18835 x
  · exact rowEval18836 x
  · exact rowEval18837 x
  · exact rowEval18838 x
  · exact rowEval18839 x
  · exact rowEval18840 x
  · exact rowEval18841 x
  · exact rowEval18842 x
  · exact rowEval18843 x
  · exact rowEval18844 x
  · exact rowEval18845 x
  · exact rowEval18846 x
  · exact rowEval18847 x
  · exact rowEval18848 x

theorem entryEval5_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_2 (GramNormalization.eval B) = GramFunctions.Block5.form5.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck5_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form5 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_2]

def rows5_3 : Fin GramFunctions.Block5.form5.size → Integer.Sparse Key := ![row18849, row18850, row18851, row18852, row18853, row18854, row18855, row18856, row18857, row18858, row18859, row18860, row18861, row18862, row18863, row18864, row18865, row18866, row18867, row18868, row18869, row18870, row18871, row18872, row18873, row18874, row18875, row18876, row18877, row18878]

theorem entryCheck5_3 : entry5_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form5.terms k).coefficient) (rows5_3 k)) := by decide +kernel

theorem rowsSound5_3 (k : Fin GramFunctions.Block5.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form5.terms k).tag (GramFunctions.Block5.form5.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval18849 x
  · exact rowEval18850 x
  · exact rowEval18851 x
  · exact rowEval18852 x
  · exact rowEval18853 x
  · exact rowEval18854 x
  · exact rowEval18855 x
  · exact rowEval18856 x
  · exact rowEval18857 x
  · exact rowEval18858 x
  · exact rowEval18859 x
  · exact rowEval18860 x
  · exact rowEval18861 x
  · exact rowEval18862 x
  · exact rowEval18863 x
  · exact rowEval18864 x
  · exact rowEval18865 x
  · exact rowEval18866 x
  · exact rowEval18867 x
  · exact rowEval18868 x
  · exact rowEval18869 x
  · exact rowEval18870 x
  · exact rowEval18871 x
  · exact rowEval18872 x
  · exact rowEval18873 x
  · exact rowEval18874 x
  · exact rowEval18875 x
  · exact rowEval18876 x
  · exact rowEval18877 x
  · exact rowEval18878 x

theorem entryEval5_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_3 (GramNormalization.eval B) = GramFunctions.Block5.form5.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck5_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form5 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_3]

def rows5_4 : Fin GramFunctions.Block5.form5.size → Integer.Sparse Key := ![row18879, row18880, row18881, row18882, row18883, row18884, row18885, row18886, row18887, row18888, row18889, row18890, row18891, row18892, row18893, row18894, row18895, row18896, row18897, row18898, row18899, row18900, row18901, row18902, row18903, row18904, row18905, row18906, row18907, row18908]

theorem entryCheck5_4 : entry5_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form5.terms k).coefficient) (rows5_4 k)) := by decide +kernel

theorem rowsSound5_4 (k : Fin GramFunctions.Block5.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form5.terms k).tag (GramFunctions.Block5.form5.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval18879 x
  · exact rowEval18880 x
  · exact rowEval18881 x
  · exact rowEval18882 x
  · exact rowEval18883 x
  · exact rowEval18884 x
  · exact rowEval18885 x
  · exact rowEval18886 x
  · exact rowEval18887 x
  · exact rowEval18888 x
  · exact rowEval18889 x
  · exact rowEval18890 x
  · exact rowEval18891 x
  · exact rowEval18892 x
  · exact rowEval18893 x
  · exact rowEval18894 x
  · exact rowEval18895 x
  · exact rowEval18896 x
  · exact rowEval18897 x
  · exact rowEval18898 x
  · exact rowEval18899 x
  · exact rowEval18900 x
  · exact rowEval18901 x
  · exact rowEval18902 x
  · exact rowEval18903 x
  · exact rowEval18904 x
  · exact rowEval18905 x
  · exact rowEval18906 x
  · exact rowEval18907 x
  · exact rowEval18908 x

theorem entryEval5_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_4 (GramNormalization.eval B) = GramFunctions.Block5.form5.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck5_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form5 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_4]

def rows5_5 : Fin GramFunctions.Block5.form5.size → Integer.Sparse Key := ![row18909, row18910, row18911, row18912, row18913, row18914, row18915, row18916, row18917, row18918, row18919, row18920, row18921, row18922, row18923, row18924, row18925, row18926, row18927, row18928, row18929, row18930, row18931, row18932, row18933, row18934, row18935, row18936, row18937, row18938]

theorem entryCheck5_5 : entry5_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form5.terms k).coefficient) (rows5_5 k)) := by decide +kernel

theorem rowsSound5_5 (k : Fin GramFunctions.Block5.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form5.terms k).tag (GramFunctions.Block5.form5.terms k).charge GramFunctions.Block5.form5) x := by
  fin_cases k
  · exact rowEval18909 x
  · exact rowEval18910 x
  · exact rowEval18911 x
  · exact rowEval18912 x
  · exact rowEval18913 x
  · exact rowEval18914 x
  · exact rowEval18915 x
  · exact rowEval18916 x
  · exact rowEval18917 x
  · exact rowEval18918 x
  · exact rowEval18919 x
  · exact rowEval18920 x
  · exact rowEval18921 x
  · exact rowEval18922 x
  · exact rowEval18923 x
  · exact rowEval18924 x
  · exact rowEval18925 x
  · exact rowEval18926 x
  · exact rowEval18927 x
  · exact rowEval18928 x
  · exact rowEval18929 x
  · exact rowEval18930 x
  · exact rowEval18931 x
  · exact rowEval18932 x
  · exact rowEval18933 x
  · exact rowEval18934 x
  · exact rowEval18935 x
  · exact rowEval18936 x
  · exact rowEval18937 x
  · exact rowEval18938 x

theorem entryEval5_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_5 (GramNormalization.eval B) = GramFunctions.Block5.form5.mixedGram GramFunctions.Block5.form5 B := by
  rw [entryCheck5_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form5 GramFunctions.Block5.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_5]

end MUB6.Certificate.GramEntries.Block5

end OAI
