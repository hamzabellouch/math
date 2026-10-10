import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block93
import OAI.Analysis.MutuallyUnbiased.GramRows.Block94

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows13_0 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8841, row8842, row8843, row8844, row8845, row8846, row8847, row8848, row8849, row8850, row8851, row8852, row8853, row8854, row8855, row8856]

theorem entryCheck13_0 : entry13_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_0 k)) := by decide +kernel

theorem rowsSound13_0 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval8841 x
  · exact rowEval8842 x
  · exact rowEval8843 x
  · exact rowEval8844 x
  · exact rowEval8845 x
  · exact rowEval8846 x
  · exact rowEval8847 x
  · exact rowEval8848 x
  · exact rowEval8849 x
  · exact rowEval8850 x
  · exact rowEval8851 x
  · exact rowEval8852 x
  · exact rowEval8853 x
  · exact rowEval8854 x
  · exact rowEval8855 x
  · exact rowEval8856 x

theorem entryEval13_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_0 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck13_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_0]

def rows13_1 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8857, row8858, row8859, row8860, row8861, row8862, row8863, row8864, row8865, row8866, row8867, row8868, row8869, row8870, row8871, row8872]

theorem entryCheck13_1 : entry13_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_1 k)) := by decide +kernel

theorem rowsSound13_1 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval8857 x
  · exact rowEval8858 x
  · exact rowEval8859 x
  · exact rowEval8860 x
  · exact rowEval8861 x
  · exact rowEval8862 x
  · exact rowEval8863 x
  · exact rowEval8864 x
  · exact rowEval8865 x
  · exact rowEval8866 x
  · exact rowEval8867 x
  · exact rowEval8868 x
  · exact rowEval8869 x
  · exact rowEval8870 x
  · exact rowEval8871 x
  · exact rowEval8872 x

theorem entryEval13_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_1 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck13_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_1]

def rows13_2 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8873, row8874, row8875, row8876, row8877, row8878, row8879, row8880, row8881, row8882, row8883, row8884, row8885, row8886, row8887, row8888]

theorem entryCheck13_2 : entry13_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_2 k)) := by decide +kernel

theorem rowsSound13_2 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval8873 x
  · exact rowEval8874 x
  · exact rowEval8875 x
  · exact rowEval8876 x
  · exact rowEval8877 x
  · exact rowEval8878 x
  · exact rowEval8879 x
  · exact rowEval8880 x
  · exact rowEval8881 x
  · exact rowEval8882 x
  · exact rowEval8883 x
  · exact rowEval8884 x
  · exact rowEval8885 x
  · exact rowEval8886 x
  · exact rowEval8887 x
  · exact rowEval8888 x

theorem entryEval13_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_2 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck13_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_2]

def rows13_3 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8889, row8890, row8891, row8892, row8893, row8894, row8895, row8896, row8897, row8898, row8899, row8900, row8901, row8902, row8903, row8904]

theorem entryCheck13_3 : entry13_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_3 k)) := by decide +kernel

theorem rowsSound13_3 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval8889 x
  · exact rowEval8890 x
  · exact rowEval8891 x
  · exact rowEval8892 x
  · exact rowEval8893 x
  · exact rowEval8894 x
  · exact rowEval8895 x
  · exact rowEval8896 x
  · exact rowEval8897 x
  · exact rowEval8898 x
  · exact rowEval8899 x
  · exact rowEval8900 x
  · exact rowEval8901 x
  · exact rowEval8902 x
  · exact rowEval8903 x
  · exact rowEval8904 x

theorem entryEval13_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_3 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck13_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_3]

def rows13_4 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8905, row8906, row8907, row8908, row8909, row8910, row8911, row8912, row8913, row8914, row8915, row8916, row8917, row8918, row8919, row8920]

theorem entryCheck13_4 : entry13_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_4 k)) := by decide +kernel

theorem rowsSound13_4 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval8905 x
  · exact rowEval8906 x
  · exact rowEval8907 x
  · exact rowEval8908 x
  · exact rowEval8909 x
  · exact rowEval8910 x
  · exact rowEval8911 x
  · exact rowEval8912 x
  · exact rowEval8913 x
  · exact rowEval8914 x
  · exact rowEval8915 x
  · exact rowEval8916 x
  · exact rowEval8917 x
  · exact rowEval8918 x
  · exact rowEval8919 x
  · exact rowEval8920 x

theorem entryEval13_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_4 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck13_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_4]

def rows13_5 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8921, row8922, row8923, row8924, row8925, row8926, row8927, row8928, row8929, row8930, row8931, row8932, row8933, row8934, row8935, row8936]

theorem entryCheck13_5 : entry13_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_5 k)) := by decide +kernel

theorem rowsSound13_5 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval8921 x
  · exact rowEval8922 x
  · exact rowEval8923 x
  · exact rowEval8924 x
  · exact rowEval8925 x
  · exact rowEval8926 x
  · exact rowEval8927 x
  · exact rowEval8928 x
  · exact rowEval8929 x
  · exact rowEval8930 x
  · exact rowEval8931 x
  · exact rowEval8932 x
  · exact rowEval8933 x
  · exact rowEval8934 x
  · exact rowEval8935 x
  · exact rowEval8936 x

theorem entryEval13_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_5 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck13_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_5]

def rows13_6 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8937, row8938, row8939, row8940, row8941, row8942, row8943, row8944, row8945, row8946, row8947, row8948, row8949, row8950, row8951, row8952]

theorem entryCheck13_6 : entry13_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_6 k)) := by decide +kernel

theorem rowsSound13_6 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval8937 x
  · exact rowEval8938 x
  · exact rowEval8939 x
  · exact rowEval8940 x
  · exact rowEval8941 x
  · exact rowEval8942 x
  · exact rowEval8943 x
  · exact rowEval8944 x
  · exact rowEval8945 x
  · exact rowEval8946 x
  · exact rowEval8947 x
  · exact rowEval8948 x
  · exact rowEval8949 x
  · exact rowEval8950 x
  · exact rowEval8951 x
  · exact rowEval8952 x

theorem entryEval13_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_6 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck13_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_6]

def rows13_7 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8953, row8954, row8955, row8956, row8957, row8958, row8959, row8960, row8961, row8962, row8963, row8964, row8965, row8966, row8967, row8968]

theorem entryCheck13_7 : entry13_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_7 k)) := by decide +kernel

theorem rowsSound13_7 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval8953 x
  · exact rowEval8954 x
  · exact rowEval8955 x
  · exact rowEval8956 x
  · exact rowEval8957 x
  · exact rowEval8958 x
  · exact rowEval8959 x
  · exact rowEval8960 x
  · exact rowEval8961 x
  · exact rowEval8962 x
  · exact rowEval8963 x
  · exact rowEval8964 x
  · exact rowEval8965 x
  · exact rowEval8966 x
  · exact rowEval8967 x
  · exact rowEval8968 x

theorem entryEval13_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_7 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck13_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_7]

def rows13_8 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8969, row8970, row8971, row8972, row8973, row8974, row8975, row8976, row8977, row8978, row8979, row8980, row8981, row8982, row8983, row8984]

theorem entryCheck13_8 : entry13_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_8 k)) := by decide +kernel

theorem rowsSound13_8 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval8969 x
  · exact rowEval8970 x
  · exact rowEval8971 x
  · exact rowEval8972 x
  · exact rowEval8973 x
  · exact rowEval8974 x
  · exact rowEval8975 x
  · exact rowEval8976 x
  · exact rowEval8977 x
  · exact rowEval8978 x
  · exact rowEval8979 x
  · exact rowEval8980 x
  · exact rowEval8981 x
  · exact rowEval8982 x
  · exact rowEval8983 x
  · exact rowEval8984 x

theorem entryEval13_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_8 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck13_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_8]

def rows13_9 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8985, row8986, row8987, row8988, row8989, row8990, row8991, row8992, row8993, row8994, row8995, row8996, row8997, row8998, row8999, row9000]

theorem entryCheck13_9 : entry13_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_9 k)) := by decide +kernel

theorem rowsSound13_9 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval8985 x
  · exact rowEval8986 x
  · exact rowEval8987 x
  · exact rowEval8988 x
  · exact rowEval8989 x
  · exact rowEval8990 x
  · exact rowEval8991 x
  · exact rowEval8992 x
  · exact rowEval8993 x
  · exact rowEval8994 x
  · exact rowEval8995 x
  · exact rowEval8996 x
  · exact rowEval8997 x
  · exact rowEval8998 x
  · exact rowEval8999 x
  · exact rowEval9000 x

theorem entryEval13_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_9 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck13_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_9]

def rows13_10 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row9001, row9002, row9003, row9004, row9005, row9006, row9007, row9008, row9009, row9010, row9011, row9012, row9013, row9014, row9015, row9016]

theorem entryCheck13_10 : entry13_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_10 k)) := by decide +kernel

theorem rowsSound13_10 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval9001 x
  · exact rowEval9002 x
  · exact rowEval9003 x
  · exact rowEval9004 x
  · exact rowEval9005 x
  · exact rowEval9006 x
  · exact rowEval9007 x
  · exact rowEval9008 x
  · exact rowEval9009 x
  · exact rowEval9010 x
  · exact rowEval9011 x
  · exact rowEval9012 x
  · exact rowEval9013 x
  · exact rowEval9014 x
  · exact rowEval9015 x
  · exact rowEval9016 x

theorem entryEval13_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_10 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck13_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_10]

def rows13_11 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row9017, row9018, row9019, row9020, row9021, row9022, row9023, row9024, row9025, row9026, row9027, row9028, row9029, row9030, row9031, row9032]

theorem entryCheck13_11 : entry13_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_11 k)) := by decide +kernel

theorem rowsSound13_11 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval9017 x
  · exact rowEval9018 x
  · exact rowEval9019 x
  · exact rowEval9020 x
  · exact rowEval9021 x
  · exact rowEval9022 x
  · exact rowEval9023 x
  · exact rowEval9024 x
  · exact rowEval9025 x
  · exact rowEval9026 x
  · exact rowEval9027 x
  · exact rowEval9028 x
  · exact rowEval9029 x
  · exact rowEval9030 x
  · exact rowEval9031 x
  · exact rowEval9032 x

theorem entryEval13_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_11 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck13_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_11]

def rows13_12 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row9033, row9034, row9035, row9036, row9037, row9038, row9039, row9040, row9041, row9042, row9043, row9044, row9045, row9046, row9047, row9048]

theorem entryCheck13_12 : entry13_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_12 k)) := by decide +kernel

theorem rowsSound13_12 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval9033 x
  · exact rowEval9034 x
  · exact rowEval9035 x
  · exact rowEval9036 x
  · exact rowEval9037 x
  · exact rowEval9038 x
  · exact rowEval9039 x
  · exact rowEval9040 x
  · exact rowEval9041 x
  · exact rowEval9042 x
  · exact rowEval9043 x
  · exact rowEval9044 x
  · exact rowEval9045 x
  · exact rowEval9046 x
  · exact rowEval9047 x
  · exact rowEval9048 x

theorem entryEval13_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_12 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck13_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_12]

def rows13_13 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row9049, row9050, row9051, row9052, row9053, row9054, row9055, row9056, row9057, row9058, row9059, row9060, row9061, row9062, row9063, row9064]

theorem entryCheck13_13 : entry13_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form13.terms k).coefficient) (rows13_13 k)) := by decide +kernel

theorem rowsSound13_13 (k : Fin GramFunctions.Block3.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form13.terms k).tag (GramFunctions.Block3.form13.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval9049 x
  · exact rowEval9050 x
  · exact rowEval9051 x
  · exact rowEval9052 x
  · exact rowEval9053 x
  · exact rowEval9054 x
  · exact rowEval9055 x
  · exact rowEval9056 x
  · exact rowEval9057 x
  · exact rowEval9058 x
  · exact rowEval9059 x
  · exact rowEval9060 x
  · exact rowEval9061 x
  · exact rowEval9062 x
  · exact rowEval9063 x
  · exact rowEval9064 x

theorem entryEval13_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_13 (GramNormalization.eval B) = GramFunctions.Block3.form13.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck13_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form13 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_13]

end MUB6.Certificate.GramEntries.Block3

end OAI
