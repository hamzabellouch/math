import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block83
import OAI.Analysis.MutuallyUnbiased.GramRows.Block84
import OAI.Analysis.MutuallyUnbiased.GramRows.Block85
import OAI.Analysis.MutuallyUnbiased.GramRows.Block86

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_0 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7825, row7826, row7827, row7828, row7829, row7830, row7831, row7832, row7833, row7834, row7835, row7836, row7574, row7575, row7576, row7577, row7578, row7579, row7580, row7581, row7582, row7583, row7584, row7585]

theorem entryCheck7_0 : entry7_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form7.terms k).coefficient) (rows7_0 k)) := by decide +kernel

theorem rowsSound7_0 (k : Fin GramFunctions.Block3.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form7.terms k).tag (GramFunctions.Block3.form7.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7825 x
  · exact rowEval7826 x
  · exact rowEval7827 x
  · exact rowEval7828 x
  · exact rowEval7829 x
  · exact rowEval7830 x
  · exact rowEval7831 x
  · exact rowEval7832 x
  · exact rowEval7833 x
  · exact rowEval7834 x
  · exact rowEval7835 x
  · exact rowEval7836 x
  · exact rowEval7574 x
  · exact rowEval7575 x
  · exact rowEval7576 x
  · exact rowEval7577 x
  · exact rowEval7578 x
  · exact rowEval7579 x
  · exact rowEval7580 x
  · exact rowEval7581 x
  · exact rowEval7582 x
  · exact rowEval7583 x
  · exact rowEval7584 x
  · exact rowEval7585 x

theorem entryEval7_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_0 (GramNormalization.eval B) = GramFunctions.Block3.form7.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck7_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form7 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_0]

def rows7_1 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7837, row7838, row7839, row7840, row7841, row7842, row7843, row7844, row7845, row7846, row7847, row7848, row7610, row7611, row7612, row7613, row7614, row7615, row7616, row7617, row7618, row7619, row7620, row7621]

theorem entryCheck7_1 : entry7_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form7.terms k).coefficient) (rows7_1 k)) := by decide +kernel

theorem rowsSound7_1 (k : Fin GramFunctions.Block3.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form7.terms k).tag (GramFunctions.Block3.form7.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7837 x
  · exact rowEval7838 x
  · exact rowEval7839 x
  · exact rowEval7840 x
  · exact rowEval7841 x
  · exact rowEval7842 x
  · exact rowEval7843 x
  · exact rowEval7844 x
  · exact rowEval7845 x
  · exact rowEval7846 x
  · exact rowEval7847 x
  · exact rowEval7848 x
  · exact rowEval7610 x
  · exact rowEval7611 x
  · exact rowEval7612 x
  · exact rowEval7613 x
  · exact rowEval7614 x
  · exact rowEval7615 x
  · exact rowEval7616 x
  · exact rowEval7617 x
  · exact rowEval7618 x
  · exact rowEval7619 x
  · exact rowEval7620 x
  · exact rowEval7621 x

theorem entryEval7_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_1 (GramNormalization.eval B) = GramFunctions.Block3.form7.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck7_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form7 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_1]

def rows7_2 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7849, row7850, row7851, row7852, row7853, row7854, row7855, row7856, row7857, row7858, row7859, row7860, row7646, row7647, row7648, row7649, row7650, row7651, row7652, row7653, row7654, row7655, row7656, row7657]

theorem entryCheck7_2 : entry7_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form7.terms k).coefficient) (rows7_2 k)) := by decide +kernel

theorem rowsSound7_2 (k : Fin GramFunctions.Block3.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form7.terms k).tag (GramFunctions.Block3.form7.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7849 x
  · exact rowEval7850 x
  · exact rowEval7851 x
  · exact rowEval7852 x
  · exact rowEval7853 x
  · exact rowEval7854 x
  · exact rowEval7855 x
  · exact rowEval7856 x
  · exact rowEval7857 x
  · exact rowEval7858 x
  · exact rowEval7859 x
  · exact rowEval7860 x
  · exact rowEval7646 x
  · exact rowEval7647 x
  · exact rowEval7648 x
  · exact rowEval7649 x
  · exact rowEval7650 x
  · exact rowEval7651 x
  · exact rowEval7652 x
  · exact rowEval7653 x
  · exact rowEval7654 x
  · exact rowEval7655 x
  · exact rowEval7656 x
  · exact rowEval7657 x

theorem entryEval7_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_2 (GramNormalization.eval B) = GramFunctions.Block3.form7.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck7_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form7 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_2]

def rows7_3 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7861, row7862, row7863, row7864, row7865, row7866, row7867, row7868, row7869, row7870, row7871, row7872, row7682, row7683, row7684, row7685, row7686, row7687, row7688, row7689, row7690, row7691, row7692, row7693]

theorem entryCheck7_3 : entry7_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form7.terms k).coefficient) (rows7_3 k)) := by decide +kernel

theorem rowsSound7_3 (k : Fin GramFunctions.Block3.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form7.terms k).tag (GramFunctions.Block3.form7.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval7861 x
  · exact rowEval7862 x
  · exact rowEval7863 x
  · exact rowEval7864 x
  · exact rowEval7865 x
  · exact rowEval7866 x
  · exact rowEval7867 x
  · exact rowEval7868 x
  · exact rowEval7869 x
  · exact rowEval7870 x
  · exact rowEval7871 x
  · exact rowEval7872 x
  · exact rowEval7682 x
  · exact rowEval7683 x
  · exact rowEval7684 x
  · exact rowEval7685 x
  · exact rowEval7686 x
  · exact rowEval7687 x
  · exact rowEval7688 x
  · exact rowEval7689 x
  · exact rowEval7690 x
  · exact rowEval7691 x
  · exact rowEval7692 x
  · exact rowEval7693 x

theorem entryEval7_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_3 (GramNormalization.eval B) = GramFunctions.Block3.form7.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck7_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form7 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_3]

def rows7_4 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7873, row7874, row7875, row7876, row7877, row7878, row7879, row7880, row7881, row7882, row7883, row7884, row7718, row7719, row7720, row7721, row7722, row7723, row7724, row7725, row7726, row7727, row7728, row7729]

theorem entryCheck7_4 : entry7_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form7.terms k).coefficient) (rows7_4 k)) := by decide +kernel

theorem rowsSound7_4 (k : Fin GramFunctions.Block3.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form7.terms k).tag (GramFunctions.Block3.form7.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval7873 x
  · exact rowEval7874 x
  · exact rowEval7875 x
  · exact rowEval7876 x
  · exact rowEval7877 x
  · exact rowEval7878 x
  · exact rowEval7879 x
  · exact rowEval7880 x
  · exact rowEval7881 x
  · exact rowEval7882 x
  · exact rowEval7883 x
  · exact rowEval7884 x
  · exact rowEval7718 x
  · exact rowEval7719 x
  · exact rowEval7720 x
  · exact rowEval7721 x
  · exact rowEval7722 x
  · exact rowEval7723 x
  · exact rowEval7724 x
  · exact rowEval7725 x
  · exact rowEval7726 x
  · exact rowEval7727 x
  · exact rowEval7728 x
  · exact rowEval7729 x

theorem entryEval7_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_4 (GramNormalization.eval B) = GramFunctions.Block3.form7.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck7_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form7 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_4]

def rows7_5 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7885, row7886, row7887, row7888, row7889, row7890, row7891, row7892, row7893, row7894, row7895, row7896, row7754, row7755, row7756, row7757, row7758, row7759, row7760, row7761, row7762, row7763, row7764, row7765]

theorem entryCheck7_5 : entry7_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form7.terms k).coefficient) (rows7_5 k)) := by decide +kernel

theorem rowsSound7_5 (k : Fin GramFunctions.Block3.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form7.terms k).tag (GramFunctions.Block3.form7.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval7885 x
  · exact rowEval7886 x
  · exact rowEval7887 x
  · exact rowEval7888 x
  · exact rowEval7889 x
  · exact rowEval7890 x
  · exact rowEval7891 x
  · exact rowEval7892 x
  · exact rowEval7893 x
  · exact rowEval7894 x
  · exact rowEval7895 x
  · exact rowEval7896 x
  · exact rowEval7754 x
  · exact rowEval7755 x
  · exact rowEval7756 x
  · exact rowEval7757 x
  · exact rowEval7758 x
  · exact rowEval7759 x
  · exact rowEval7760 x
  · exact rowEval7761 x
  · exact rowEval7762 x
  · exact rowEval7763 x
  · exact rowEval7764 x
  · exact rowEval7765 x

theorem entryEval7_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_5 (GramNormalization.eval B) = GramFunctions.Block3.form7.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck7_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form7 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_5]

def rows7_6 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7897, row7898, row7899, row7900, row7901, row7902, row7903, row7904, row7905, row7906, row7907, row7908, row7909, row7910, row7911, row7912, row7913, row7914, row7915, row7916, row7917, row7918, row7919, row7920]

theorem entryCheck7_6 : entry7_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form7.terms k).coefficient) (rows7_6 k)) := by decide +kernel

theorem rowsSound7_6 (k : Fin GramFunctions.Block3.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form7.terms k).tag (GramFunctions.Block3.form7.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval7897 x
  · exact rowEval7898 x
  · exact rowEval7899 x
  · exact rowEval7900 x
  · exact rowEval7901 x
  · exact rowEval7902 x
  · exact rowEval7903 x
  · exact rowEval7904 x
  · exact rowEval7905 x
  · exact rowEval7906 x
  · exact rowEval7907 x
  · exact rowEval7908 x
  · exact rowEval7909 x
  · exact rowEval7910 x
  · exact rowEval7911 x
  · exact rowEval7912 x
  · exact rowEval7913 x
  · exact rowEval7914 x
  · exact rowEval7915 x
  · exact rowEval7916 x
  · exact rowEval7917 x
  · exact rowEval7918 x
  · exact rowEval7919 x
  · exact rowEval7920 x

theorem entryEval7_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_6 (GramNormalization.eval B) = GramFunctions.Block3.form7.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck7_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form7 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_6]

def rows7_7 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7921, row7922, row7923, row7924, row7925, row7926, row7927, row7928, row7929, row7930, row7931, row7932, row7933, row7934, row7935, row7936, row7937, row7938, row7939, row7940, row7941, row7942, row7943, row7944]

theorem entryCheck7_7 : entry7_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form7.terms k).coefficient) (rows7_7 k)) := by decide +kernel

theorem rowsSound7_7 (k : Fin GramFunctions.Block3.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form7.terms k).tag (GramFunctions.Block3.form7.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval7921 x
  · exact rowEval7922 x
  · exact rowEval7923 x
  · exact rowEval7924 x
  · exact rowEval7925 x
  · exact rowEval7926 x
  · exact rowEval7927 x
  · exact rowEval7928 x
  · exact rowEval7929 x
  · exact rowEval7930 x
  · exact rowEval7931 x
  · exact rowEval7932 x
  · exact rowEval7933 x
  · exact rowEval7934 x
  · exact rowEval7935 x
  · exact rowEval7936 x
  · exact rowEval7937 x
  · exact rowEval7938 x
  · exact rowEval7939 x
  · exact rowEval7940 x
  · exact rowEval7941 x
  · exact rowEval7942 x
  · exact rowEval7943 x
  · exact rowEval7944 x

theorem entryEval7_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_7 (GramNormalization.eval B) = GramFunctions.Block3.form7.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck7_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form7 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_7]

end MUB6.Certificate.GramEntries.Block3

end OAI
