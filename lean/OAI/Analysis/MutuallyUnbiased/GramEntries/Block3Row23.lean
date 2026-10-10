import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block81
import OAI.Analysis.MutuallyUnbiased.GramRows.Block116
import OAI.Analysis.MutuallyUnbiased.GramRows.Block117
import OAI.Analysis.MutuallyUnbiased.GramRows.Block118
import OAI.Analysis.MutuallyUnbiased.GramRows.Block119

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows23_0 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11786, row11787, row11788, row11789, row11790, row11791, row7348, row7349, row7350, row7351, row7352, row7353, row7354, row7355, row7356, row7357, row7358, row7359]

theorem entryCheck23_0 : entry23_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_0 k)) := by decide +kernel

theorem rowsSound23_0 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval11786 x
  · exact rowEval11787 x
  · exact rowEval11788 x
  · exact rowEval11789 x
  · exact rowEval11790 x
  · exact rowEval11791 x
  · exact rowEval7348 x
  · exact rowEval7349 x
  · exact rowEval7350 x
  · exact rowEval7351 x
  · exact rowEval7352 x
  · exact rowEval7353 x
  · exact rowEval7354 x
  · exact rowEval7355 x
  · exact rowEval7356 x
  · exact rowEval7357 x
  · exact rowEval7358 x
  · exact rowEval7359 x

theorem entryEval23_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_0 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck23_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_0]

def rows23_1 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11792, row11793, row11794, row11795, row11796, row11797, row11798, row11799, row11800, row11801, row11802, row11803, row11804, row11805, row11806, row11807, row11808, row11809]

theorem entryCheck23_1 : entry23_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_1 k)) := by decide +kernel

theorem rowsSound23_1 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval11792 x
  · exact rowEval11793 x
  · exact rowEval11794 x
  · exact rowEval11795 x
  · exact rowEval11796 x
  · exact rowEval11797 x
  · exact rowEval11798 x
  · exact rowEval11799 x
  · exact rowEval11800 x
  · exact rowEval11801 x
  · exact rowEval11802 x
  · exact rowEval11803 x
  · exact rowEval11804 x
  · exact rowEval11805 x
  · exact rowEval11806 x
  · exact rowEval11807 x
  · exact rowEval11808 x
  · exact rowEval11809 x

theorem entryEval23_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_1 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck23_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_1]

def rows23_2 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11810, row11811, row11812, row11813, row11814, row11815, row11816, row11817, row11818, row11819, row11820, row11821, row11822, row11823, row11824, row11825, row11826, row11827]

theorem entryCheck23_2 : entry23_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_2 k)) := by decide +kernel

theorem rowsSound23_2 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval11810 x
  · exact rowEval11811 x
  · exact rowEval11812 x
  · exact rowEval11813 x
  · exact rowEval11814 x
  · exact rowEval11815 x
  · exact rowEval11816 x
  · exact rowEval11817 x
  · exact rowEval11818 x
  · exact rowEval11819 x
  · exact rowEval11820 x
  · exact rowEval11821 x
  · exact rowEval11822 x
  · exact rowEval11823 x
  · exact rowEval11824 x
  · exact rowEval11825 x
  · exact rowEval11826 x
  · exact rowEval11827 x

theorem entryEval23_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_2 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck23_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_2]

def rows23_3 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11828, row11829, row11830, row11831, row11832, row11833, row11834, row11835, row11836, row11837, row11838, row11839, row11840, row11841, row11842, row11843, row11844, row11845]

theorem entryCheck23_3 : entry23_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_3 k)) := by decide +kernel

theorem rowsSound23_3 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval11828 x
  · exact rowEval11829 x
  · exact rowEval11830 x
  · exact rowEval11831 x
  · exact rowEval11832 x
  · exact rowEval11833 x
  · exact rowEval11834 x
  · exact rowEval11835 x
  · exact rowEval11836 x
  · exact rowEval11837 x
  · exact rowEval11838 x
  · exact rowEval11839 x
  · exact rowEval11840 x
  · exact rowEval11841 x
  · exact rowEval11842 x
  · exact rowEval11843 x
  · exact rowEval11844 x
  · exact rowEval11845 x

theorem entryEval23_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_3 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck23_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_3]

def rows23_4 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11846, row11847, row11848, row11849, row11850, row11851, row11852, row11853, row11854, row11855, row11856, row11857, row11858, row11859, row11860, row11861, row11862, row11863]

theorem entryCheck23_4 : entry23_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_4 k)) := by decide +kernel

theorem rowsSound23_4 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval11846 x
  · exact rowEval11847 x
  · exact rowEval11848 x
  · exact rowEval11849 x
  · exact rowEval11850 x
  · exact rowEval11851 x
  · exact rowEval11852 x
  · exact rowEval11853 x
  · exact rowEval11854 x
  · exact rowEval11855 x
  · exact rowEval11856 x
  · exact rowEval11857 x
  · exact rowEval11858 x
  · exact rowEval11859 x
  · exact rowEval11860 x
  · exact rowEval11861 x
  · exact rowEval11862 x
  · exact rowEval11863 x

theorem entryEval23_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_4 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck23_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_4]

def rows23_5 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11864, row11865, row11866, row11867, row11868, row11869, row11870, row11871, row11872, row11873, row11874, row11875, row11876, row11877, row11878, row11879, row11880, row11881]

theorem entryCheck23_5 : entry23_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_5 k)) := by decide +kernel

theorem rowsSound23_5 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval11864 x
  · exact rowEval11865 x
  · exact rowEval11866 x
  · exact rowEval11867 x
  · exact rowEval11868 x
  · exact rowEval11869 x
  · exact rowEval11870 x
  · exact rowEval11871 x
  · exact rowEval11872 x
  · exact rowEval11873 x
  · exact rowEval11874 x
  · exact rowEval11875 x
  · exact rowEval11876 x
  · exact rowEval11877 x
  · exact rowEval11878 x
  · exact rowEval11879 x
  · exact rowEval11880 x
  · exact rowEval11881 x

theorem entryEval23_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_5 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck23_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_5]

def rows23_6 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11882, row11883, row11884, row11885, row11886, row11887, row11888, row11889, row11890, row11891, row11892, row11893, row11894, row11895, row11896, row11897, row11898, row11899]

theorem entryCheck23_6 : entry23_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_6 k)) := by decide +kernel

theorem rowsSound23_6 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval11882 x
  · exact rowEval11883 x
  · exact rowEval11884 x
  · exact rowEval11885 x
  · exact rowEval11886 x
  · exact rowEval11887 x
  · exact rowEval11888 x
  · exact rowEval11889 x
  · exact rowEval11890 x
  · exact rowEval11891 x
  · exact rowEval11892 x
  · exact rowEval11893 x
  · exact rowEval11894 x
  · exact rowEval11895 x
  · exact rowEval11896 x
  · exact rowEval11897 x
  · exact rowEval11898 x
  · exact rowEval11899 x

theorem entryEval23_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_6 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck23_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_6]

def rows23_7 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11900, row11901, row11902, row11903, row11904, row11905, row11906, row11907, row11908, row11909, row11910, row11911, row11912, row11913, row11914, row11915, row11916, row11917]

theorem entryCheck23_7 : entry23_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_7 k)) := by decide +kernel

theorem rowsSound23_7 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval11900 x
  · exact rowEval11901 x
  · exact rowEval11902 x
  · exact rowEval11903 x
  · exact rowEval11904 x
  · exact rowEval11905 x
  · exact rowEval11906 x
  · exact rowEval11907 x
  · exact rowEval11908 x
  · exact rowEval11909 x
  · exact rowEval11910 x
  · exact rowEval11911 x
  · exact rowEval11912 x
  · exact rowEval11913 x
  · exact rowEval11914 x
  · exact rowEval11915 x
  · exact rowEval11916 x
  · exact rowEval11917 x

theorem entryEval23_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_7 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck23_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_7]

def rows23_8 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11918, row11919, row11920, row11921, row11922, row11923, row11924, row11925, row11926, row11927, row11928, row11929, row11930, row11931, row11932, row11933, row11934, row11935]

theorem entryCheck23_8 : entry23_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_8 k)) := by decide +kernel

theorem rowsSound23_8 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval11918 x
  · exact rowEval11919 x
  · exact rowEval11920 x
  · exact rowEval11921 x
  · exact rowEval11922 x
  · exact rowEval11923 x
  · exact rowEval11924 x
  · exact rowEval11925 x
  · exact rowEval11926 x
  · exact rowEval11927 x
  · exact rowEval11928 x
  · exact rowEval11929 x
  · exact rowEval11930 x
  · exact rowEval11931 x
  · exact rowEval11932 x
  · exact rowEval11933 x
  · exact rowEval11934 x
  · exact rowEval11935 x

theorem entryEval23_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_8 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck23_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_8]

def rows23_9 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11936, row11937, row11938, row11939, row11940, row11941, row11942, row11943, row11944, row11945, row11946, row11947, row11948, row11949, row11950, row11951, row11952, row11953]

theorem entryCheck23_9 : entry23_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_9 k)) := by decide +kernel

theorem rowsSound23_9 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval11936 x
  · exact rowEval11937 x
  · exact rowEval11938 x
  · exact rowEval11939 x
  · exact rowEval11940 x
  · exact rowEval11941 x
  · exact rowEval11942 x
  · exact rowEval11943 x
  · exact rowEval11944 x
  · exact rowEval11945 x
  · exact rowEval11946 x
  · exact rowEval11947 x
  · exact rowEval11948 x
  · exact rowEval11949 x
  · exact rowEval11950 x
  · exact rowEval11951 x
  · exact rowEval11952 x
  · exact rowEval11953 x

theorem entryEval23_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_9 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck23_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_9]

def rows23_10 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11954, row11955, row11956, row11957, row11958, row11959, row11960, row11961, row11962, row11963, row11964, row11965, row11966, row11967, row11968, row11969, row11970, row11971]

theorem entryCheck23_10 : entry23_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_10 k)) := by decide +kernel

theorem rowsSound23_10 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval11954 x
  · exact rowEval11955 x
  · exact rowEval11956 x
  · exact rowEval11957 x
  · exact rowEval11958 x
  · exact rowEval11959 x
  · exact rowEval11960 x
  · exact rowEval11961 x
  · exact rowEval11962 x
  · exact rowEval11963 x
  · exact rowEval11964 x
  · exact rowEval11965 x
  · exact rowEval11966 x
  · exact rowEval11967 x
  · exact rowEval11968 x
  · exact rowEval11969 x
  · exact rowEval11970 x
  · exact rowEval11971 x

theorem entryEval23_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_10 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck23_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_10]

def rows23_11 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11972, row11973, row11974, row11975, row11976, row11977, row11978, row11979, row11980, row11981, row11982, row11983, row11984, row11985, row11986, row11987, row11988, row11989]

theorem entryCheck23_11 : entry23_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_11 k)) := by decide +kernel

theorem rowsSound23_11 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval11972 x
  · exact rowEval11973 x
  · exact rowEval11974 x
  · exact rowEval11975 x
  · exact rowEval11976 x
  · exact rowEval11977 x
  · exact rowEval11978 x
  · exact rowEval11979 x
  · exact rowEval11980 x
  · exact rowEval11981 x
  · exact rowEval11982 x
  · exact rowEval11983 x
  · exact rowEval11984 x
  · exact rowEval11985 x
  · exact rowEval11986 x
  · exact rowEval11987 x
  · exact rowEval11988 x
  · exact rowEval11989 x

theorem entryEval23_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_11 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck23_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_11]

def rows23_12 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11990, row11991, row11992, row11993, row11994, row11995, row11996, row11997, row11998, row11999, row12000, row12001, row12002, row12003, row12004, row12005, row12006, row12007]

theorem entryCheck23_12 : entry23_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_12 k)) := by decide +kernel

theorem rowsSound23_12 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval11990 x
  · exact rowEval11991 x
  · exact rowEval11992 x
  · exact rowEval11993 x
  · exact rowEval11994 x
  · exact rowEval11995 x
  · exact rowEval11996 x
  · exact rowEval11997 x
  · exact rowEval11998 x
  · exact rowEval11999 x
  · exact rowEval12000 x
  · exact rowEval12001 x
  · exact rowEval12002 x
  · exact rowEval12003 x
  · exact rowEval12004 x
  · exact rowEval12005 x
  · exact rowEval12006 x
  · exact rowEval12007 x

theorem entryEval23_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_12 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck23_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_12]

def rows23_13 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12008, row12009, row12010, row12011, row12012, row12013, row12014, row12015, row12016, row12017, row12018, row12019, row12020, row12021, row12022, row12023, row12024, row12025]

theorem entryCheck23_13 : entry23_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_13 k)) := by decide +kernel

theorem rowsSound23_13 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval12008 x
  · exact rowEval12009 x
  · exact rowEval12010 x
  · exact rowEval12011 x
  · exact rowEval12012 x
  · exact rowEval12013 x
  · exact rowEval12014 x
  · exact rowEval12015 x
  · exact rowEval12016 x
  · exact rowEval12017 x
  · exact rowEval12018 x
  · exact rowEval12019 x
  · exact rowEval12020 x
  · exact rowEval12021 x
  · exact rowEval12022 x
  · exact rowEval12023 x
  · exact rowEval12024 x
  · exact rowEval12025 x

theorem entryEval23_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_13 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck23_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_13]

def rows23_14 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12026, row12027, row12028, row12029, row12030, row12031, row12032, row12033, row12034, row12035, row12036, row12037, row12038, row12039, row12040, row12041, row12042, row12043]

theorem entryCheck23_14 : entry23_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_14 k)) := by decide +kernel

theorem rowsSound23_14 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval12026 x
  · exact rowEval12027 x
  · exact rowEval12028 x
  · exact rowEval12029 x
  · exact rowEval12030 x
  · exact rowEval12031 x
  · exact rowEval12032 x
  · exact rowEval12033 x
  · exact rowEval12034 x
  · exact rowEval12035 x
  · exact rowEval12036 x
  · exact rowEval12037 x
  · exact rowEval12038 x
  · exact rowEval12039 x
  · exact rowEval12040 x
  · exact rowEval12041 x
  · exact rowEval12042 x
  · exact rowEval12043 x

theorem entryEval23_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_14 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck23_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_14]

def rows23_15 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12044, row12045, row12046, row12047, row12048, row12049, row12050, row12051, row12052, row12053, row12054, row12055, row12056, row12057, row12058, row12059, row12060, row12061]

theorem entryCheck23_15 : entry23_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_15 k)) := by decide +kernel

theorem rowsSound23_15 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval12044 x
  · exact rowEval12045 x
  · exact rowEval12046 x
  · exact rowEval12047 x
  · exact rowEval12048 x
  · exact rowEval12049 x
  · exact rowEval12050 x
  · exact rowEval12051 x
  · exact rowEval12052 x
  · exact rowEval12053 x
  · exact rowEval12054 x
  · exact rowEval12055 x
  · exact rowEval12056 x
  · exact rowEval12057 x
  · exact rowEval12058 x
  · exact rowEval12059 x
  · exact rowEval12060 x
  · exact rowEval12061 x

theorem entryEval23_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_15 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck23_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_15]

def rows23_16 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12062, row12063, row12064, row12065, row12066, row12067, row12068, row12069, row12070, row12071, row12072, row12073, row12074, row12075, row12076, row12077, row12078, row12079]

theorem entryCheck23_16 : entry23_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_16 k)) := by decide +kernel

theorem rowsSound23_16 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval12062 x
  · exact rowEval12063 x
  · exact rowEval12064 x
  · exact rowEval12065 x
  · exact rowEval12066 x
  · exact rowEval12067 x
  · exact rowEval12068 x
  · exact rowEval12069 x
  · exact rowEval12070 x
  · exact rowEval12071 x
  · exact rowEval12072 x
  · exact rowEval12073 x
  · exact rowEval12074 x
  · exact rowEval12075 x
  · exact rowEval12076 x
  · exact rowEval12077 x
  · exact rowEval12078 x
  · exact rowEval12079 x

theorem entryEval23_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_16 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck23_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_16]

def rows23_17 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12080, row12081, row12082, row12083, row12084, row12085, row12086, row12087, row12088, row12089, row12090, row12091, row12092, row12093, row12094, row12095, row12096, row12097]

theorem entryCheck23_17 : entry23_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_17 k)) := by decide +kernel

theorem rowsSound23_17 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval12080 x
  · exact rowEval12081 x
  · exact rowEval12082 x
  · exact rowEval12083 x
  · exact rowEval12084 x
  · exact rowEval12085 x
  · exact rowEval12086 x
  · exact rowEval12087 x
  · exact rowEval12088 x
  · exact rowEval12089 x
  · exact rowEval12090 x
  · exact rowEval12091 x
  · exact rowEval12092 x
  · exact rowEval12093 x
  · exact rowEval12094 x
  · exact rowEval12095 x
  · exact rowEval12096 x
  · exact rowEval12097 x

theorem entryEval23_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_17 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck23_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_17]

def rows23_18 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12098, row12099, row12100, row12101, row12102, row12103, row12104, row12105, row12106, row12107, row12108, row12109, row12110, row12111, row12112, row12113, row12114, row12115]

theorem entryCheck23_18 : entry23_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_18 k)) := by decide +kernel

theorem rowsSound23_18 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval12098 x
  · exact rowEval12099 x
  · exact rowEval12100 x
  · exact rowEval12101 x
  · exact rowEval12102 x
  · exact rowEval12103 x
  · exact rowEval12104 x
  · exact rowEval12105 x
  · exact rowEval12106 x
  · exact rowEval12107 x
  · exact rowEval12108 x
  · exact rowEval12109 x
  · exact rowEval12110 x
  · exact rowEval12111 x
  · exact rowEval12112 x
  · exact rowEval12113 x
  · exact rowEval12114 x
  · exact rowEval12115 x

theorem entryEval23_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_18 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck23_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_18]

def rows23_19 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12116, row12117, row12118, row12119, row12120, row12121, row12122, row12123, row12124, row12125, row12126, row12127, row12128, row12129, row12130, row12131, row12132, row12133]

theorem entryCheck23_19 : entry23_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_19 k)) := by decide +kernel

theorem rowsSound23_19 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval12116 x
  · exact rowEval12117 x
  · exact rowEval12118 x
  · exact rowEval12119 x
  · exact rowEval12120 x
  · exact rowEval12121 x
  · exact rowEval12122 x
  · exact rowEval12123 x
  · exact rowEval12124 x
  · exact rowEval12125 x
  · exact rowEval12126 x
  · exact rowEval12127 x
  · exact rowEval12128 x
  · exact rowEval12129 x
  · exact rowEval12130 x
  · exact rowEval12131 x
  · exact rowEval12132 x
  · exact rowEval12133 x

theorem entryEval23_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_19 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck23_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_19]

def rows23_20 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12134, row12135, row12136, row12137, row12138, row12139, row12140, row12141, row12142, row12143, row12144, row12145, row12146, row12147, row12148, row12149, row12150, row12151]

theorem entryCheck23_20 : entry23_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_20 k)) := by decide +kernel

theorem rowsSound23_20 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval12134 x
  · exact rowEval12135 x
  · exact rowEval12136 x
  · exact rowEval12137 x
  · exact rowEval12138 x
  · exact rowEval12139 x
  · exact rowEval12140 x
  · exact rowEval12141 x
  · exact rowEval12142 x
  · exact rowEval12143 x
  · exact rowEval12144 x
  · exact rowEval12145 x
  · exact rowEval12146 x
  · exact rowEval12147 x
  · exact rowEval12148 x
  · exact rowEval12149 x
  · exact rowEval12150 x
  · exact rowEval12151 x

theorem entryEval23_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_20 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck23_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_20]

def rows23_21 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12152, row12153, row12154, row12155, row12156, row12157, row12158, row12159, row12160, row12161, row12162, row12163, row12164, row12165, row12166, row12167, row12168, row12169]

theorem entryCheck23_21 : entry23_21 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_21 k)) := by decide +kernel

theorem rowsSound23_21 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_21 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form21) x := by
  fin_cases k
  · exact rowEval12152 x
  · exact rowEval12153 x
  · exact rowEval12154 x
  · exact rowEval12155 x
  · exact rowEval12156 x
  · exact rowEval12157 x
  · exact rowEval12158 x
  · exact rowEval12159 x
  · exact rowEval12160 x
  · exact rowEval12161 x
  · exact rowEval12162 x
  · exact rowEval12163 x
  · exact rowEval12164 x
  · exact rowEval12165 x
  · exact rowEval12166 x
  · exact rowEval12167 x
  · exact rowEval12168 x
  · exact rowEval12169 x

theorem entryEval23_21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_21 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form21 B := by
  rw [entryCheck23_21, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form21 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_21]

def rows23_22 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12170, row12171, row12172, row12173, row12174, row12175, row12176, row12177, row12178, row12179, row12180, row12181, row12182, row12183, row12184, row12185, row12186, row12187]

theorem entryCheck23_22 : entry23_22 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_22 k)) := by decide +kernel

theorem rowsSound23_22 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_22 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form22) x := by
  fin_cases k
  · exact rowEval12170 x
  · exact rowEval12171 x
  · exact rowEval12172 x
  · exact rowEval12173 x
  · exact rowEval12174 x
  · exact rowEval12175 x
  · exact rowEval12176 x
  · exact rowEval12177 x
  · exact rowEval12178 x
  · exact rowEval12179 x
  · exact rowEval12180 x
  · exact rowEval12181 x
  · exact rowEval12182 x
  · exact rowEval12183 x
  · exact rowEval12184 x
  · exact rowEval12185 x
  · exact rowEval12186 x
  · exact rowEval12187 x

theorem entryEval23_22 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_22 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form22 B := by
  rw [entryCheck23_22, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form22 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_22]

def rows23_23 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12188, row12189, row12190, row12191, row12192, row12193, row12194, row12195, row12196, row12197, row12198, row12199, row12200, row12201, row12202, row12203, row12204, row12205]

theorem entryCheck23_23 : entry23_23 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form23.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form23.terms k).coefficient) (rows23_23 k)) := by decide +kernel

theorem rowsSound23_23 (k : Fin GramFunctions.Block3.form23.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows23_23 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form23.terms k).tag (GramFunctions.Block3.form23.terms k).charge GramFunctions.Block3.form23) x := by
  fin_cases k
  · exact rowEval12188 x
  · exact rowEval12189 x
  · exact rowEval12190 x
  · exact rowEval12191 x
  · exact rowEval12192 x
  · exact rowEval12193 x
  · exact rowEval12194 x
  · exact rowEval12195 x
  · exact rowEval12196 x
  · exact rowEval12197 x
  · exact rowEval12198 x
  · exact rowEval12199 x
  · exact rowEval12200 x
  · exact rowEval12201 x
  · exact rowEval12202 x
  · exact rowEval12203 x
  · exact rowEval12204 x
  · exact rowEval12205 x

theorem entryEval23_23 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry23_23 (GramNormalization.eval B) = GramFunctions.Block3.form23.mixedGram GramFunctions.Block3.form23 B := by
  rw [entryCheck23_23, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form23 GramFunctions.Block3.form23 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound23_23]

end MUB6.Certificate.GramEntries.Block3

end OAI
