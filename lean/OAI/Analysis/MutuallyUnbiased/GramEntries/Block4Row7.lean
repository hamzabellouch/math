import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block132

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_0 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13845, row13846, row13847, row13848, row13849, row13850, row13851, row13852, row13853, row13854]

theorem entryCheck7_0 : entry7_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_0 k)) := by decide +kernel

theorem rowsSound7_0 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13845 x
  · exact rowEval13846 x
  · exact rowEval13847 x
  · exact rowEval13848 x
  · exact rowEval13849 x
  · exact rowEval13850 x
  · exact rowEval13851 x
  · exact rowEval13852 x
  · exact rowEval13853 x
  · exact rowEval13854 x

theorem entryEval7_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_0 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck7_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_0]

def rows7_1 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13855, row13856, row13857, row13858, row13859, row13860, row13861, row13862, row13863, row13864]

theorem entryCheck7_1 : entry7_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_1 k)) := by decide +kernel

theorem rowsSound7_1 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13855 x
  · exact rowEval13856 x
  · exact rowEval13857 x
  · exact rowEval13858 x
  · exact rowEval13859 x
  · exact rowEval13860 x
  · exact rowEval13861 x
  · exact rowEval13862 x
  · exact rowEval13863 x
  · exact rowEval13864 x

theorem entryEval7_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_1 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck7_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_1]

def rows7_2 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13865, row13866, row13867, row13868, row13869, row13870, row13871, row13872, row13873, row13874]

theorem entryCheck7_2 : entry7_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_2 k)) := by decide +kernel

theorem rowsSound7_2 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval13865 x
  · exact rowEval13866 x
  · exact rowEval13867 x
  · exact rowEval13868 x
  · exact rowEval13869 x
  · exact rowEval13870 x
  · exact rowEval13871 x
  · exact rowEval13872 x
  · exact rowEval13873 x
  · exact rowEval13874 x

theorem entryEval7_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_2 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck7_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_2]

def rows7_3 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13875, row13876, row13877, row13878, row13879, row13880, row13881, row13882, row13883, row13884]

theorem entryCheck7_3 : entry7_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_3 k)) := by decide +kernel

theorem rowsSound7_3 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval13875 x
  · exact rowEval13876 x
  · exact rowEval13877 x
  · exact rowEval13878 x
  · exact rowEval13879 x
  · exact rowEval13880 x
  · exact rowEval13881 x
  · exact rowEval13882 x
  · exact rowEval13883 x
  · exact rowEval13884 x

theorem entryEval7_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_3 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck7_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_3]

def rows7_4 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13885, row13886, row13887, row13888, row13889, row13890, row13891, row13892, row13893, row13894]

theorem entryCheck7_4 : entry7_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_4 k)) := by decide +kernel

theorem rowsSound7_4 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval13885 x
  · exact rowEval13886 x
  · exact rowEval13887 x
  · exact rowEval13888 x
  · exact rowEval13889 x
  · exact rowEval13890 x
  · exact rowEval13891 x
  · exact rowEval13892 x
  · exact rowEval13893 x
  · exact rowEval13894 x

theorem entryEval7_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_4 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck7_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_4]

def rows7_5 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13895, row13896, row13897, row13898, row13899, row13900, row13901, row13902, row13903, row13904]

theorem entryCheck7_5 : entry7_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_5 k)) := by decide +kernel

theorem rowsSound7_5 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval13895 x
  · exact rowEval13896 x
  · exact rowEval13897 x
  · exact rowEval13898 x
  · exact rowEval13899 x
  · exact rowEval13900 x
  · exact rowEval13901 x
  · exact rowEval13902 x
  · exact rowEval13903 x
  · exact rowEval13904 x

theorem entryEval7_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_5 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck7_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_5]

def rows7_6 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13905, row13906, row13907, row13908, row13909, row13910, row13911, row13912, row13913, row13914]

theorem entryCheck7_6 : entry7_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_6 k)) := by decide +kernel

theorem rowsSound7_6 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval13905 x
  · exact rowEval13906 x
  · exact rowEval13907 x
  · exact rowEval13908 x
  · exact rowEval13909 x
  · exact rowEval13910 x
  · exact rowEval13911 x
  · exact rowEval13912 x
  · exact rowEval13913 x
  · exact rowEval13914 x

theorem entryEval7_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_6 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck7_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_6]

def rows7_7 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13915, row13916, row13917, row13918, row13919, row13920, row13921, row13922, row13923, row13924]

theorem entryCheck7_7 : entry7_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_7 k)) := by decide +kernel

theorem rowsSound7_7 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval13915 x
  · exact rowEval13916 x
  · exact rowEval13917 x
  · exact rowEval13918 x
  · exact rowEval13919 x
  · exact rowEval13920 x
  · exact rowEval13921 x
  · exact rowEval13922 x
  · exact rowEval13923 x
  · exact rowEval13924 x

theorem entryEval7_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_7 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck7_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_7]

end MUB6.Certificate.GramEntries.Block4

end OAI
