import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block127
import OAI.Analysis.MutuallyUnbiased.GramRows.Block139
import OAI.Analysis.MutuallyUnbiased.GramRows.Block140
import OAI.Analysis.MutuallyUnbiased.GramRows.Block141
import OAI.Analysis.MutuallyUnbiased.GramRows.Block142

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows12_0 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14841, row14842, row14843, row14844, row14845, row14846, row14847, row14848, row14849, row13190, row13191, row13192, row13193, row13194, row13195, row14850, row14851, row14852, row13196, row13197, row13198, row13199, row13200, row13201, row13202, row13203, row13204]

theorem entryCheck12_0 : entry12_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_0 k)) := by decide +kernel

theorem rowsSound12_0 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval14841 x
  · exact rowEval14842 x
  · exact rowEval14843 x
  · exact rowEval14844 x
  · exact rowEval14845 x
  · exact rowEval14846 x
  · exact rowEval14847 x
  · exact rowEval14848 x
  · exact rowEval14849 x
  · exact rowEval13190 x
  · exact rowEval13191 x
  · exact rowEval13192 x
  · exact rowEval13193 x
  · exact rowEval13194 x
  · exact rowEval13195 x
  · exact rowEval14850 x
  · exact rowEval14851 x
  · exact rowEval14852 x
  · exact rowEval13196 x
  · exact rowEval13197 x
  · exact rowEval13198 x
  · exact rowEval13199 x
  · exact rowEval13200 x
  · exact rowEval13201 x
  · exact rowEval13202 x
  · exact rowEval13203 x
  · exact rowEval13204 x

theorem entryEval12_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_0 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck12_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_0]

def rows12_1 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14853, row14854, row14855, row14856, row14857, row14858, row14859, row14860, row14861, row14862, row14863, row14864, row14865, row14866, row14867, row14868, row14869, row14870, row14871, row14872, row14873, row14874, row14875, row14876, row14877, row14878, row14879]

theorem entryCheck12_1 : entry12_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_1 k)) := by decide +kernel

theorem rowsSound12_1 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval14853 x
  · exact rowEval14854 x
  · exact rowEval14855 x
  · exact rowEval14856 x
  · exact rowEval14857 x
  · exact rowEval14858 x
  · exact rowEval14859 x
  · exact rowEval14860 x
  · exact rowEval14861 x
  · exact rowEval14862 x
  · exact rowEval14863 x
  · exact rowEval14864 x
  · exact rowEval14865 x
  · exact rowEval14866 x
  · exact rowEval14867 x
  · exact rowEval14868 x
  · exact rowEval14869 x
  · exact rowEval14870 x
  · exact rowEval14871 x
  · exact rowEval14872 x
  · exact rowEval14873 x
  · exact rowEval14874 x
  · exact rowEval14875 x
  · exact rowEval14876 x
  · exact rowEval14877 x
  · exact rowEval14878 x
  · exact rowEval14879 x

theorem entryEval12_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_1 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck12_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_1]

def rows12_2 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14880, row14881, row14882, row14883, row14884, row14885, row14886, row14887, row14888, row14889, row14890, row14891, row14892, row14893, row14894, row14895, row14896, row14897, row14898, row14899, row14900, row14901, row14902, row14903, row14904, row14905, row14906]

theorem entryCheck12_2 : entry12_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_2 k)) := by decide +kernel

theorem rowsSound12_2 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval14880 x
  · exact rowEval14881 x
  · exact rowEval14882 x
  · exact rowEval14883 x
  · exact rowEval14884 x
  · exact rowEval14885 x
  · exact rowEval14886 x
  · exact rowEval14887 x
  · exact rowEval14888 x
  · exact rowEval14889 x
  · exact rowEval14890 x
  · exact rowEval14891 x
  · exact rowEval14892 x
  · exact rowEval14893 x
  · exact rowEval14894 x
  · exact rowEval14895 x
  · exact rowEval14896 x
  · exact rowEval14897 x
  · exact rowEval14898 x
  · exact rowEval14899 x
  · exact rowEval14900 x
  · exact rowEval14901 x
  · exact rowEval14902 x
  · exact rowEval14903 x
  · exact rowEval14904 x
  · exact rowEval14905 x
  · exact rowEval14906 x

theorem entryEval12_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_2 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck12_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_2]

def rows12_3 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14907, row14908, row14909, row14910, row14911, row14912, row14913, row14914, row14915, row14916, row14917, row14918, row14919, row14920, row14921, row14922, row14923, row14924, row14925, row14926, row14927, row14928, row14929, row14930, row14931, row14932, row14933]

theorem entryCheck12_3 : entry12_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_3 k)) := by decide +kernel

theorem rowsSound12_3 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval14907 x
  · exact rowEval14908 x
  · exact rowEval14909 x
  · exact rowEval14910 x
  · exact rowEval14911 x
  · exact rowEval14912 x
  · exact rowEval14913 x
  · exact rowEval14914 x
  · exact rowEval14915 x
  · exact rowEval14916 x
  · exact rowEval14917 x
  · exact rowEval14918 x
  · exact rowEval14919 x
  · exact rowEval14920 x
  · exact rowEval14921 x
  · exact rowEval14922 x
  · exact rowEval14923 x
  · exact rowEval14924 x
  · exact rowEval14925 x
  · exact rowEval14926 x
  · exact rowEval14927 x
  · exact rowEval14928 x
  · exact rowEval14929 x
  · exact rowEval14930 x
  · exact rowEval14931 x
  · exact rowEval14932 x
  · exact rowEval14933 x

theorem entryEval12_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_3 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck12_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_3]

def rows12_4 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14934, row14935, row14936, row14937, row14938, row14939, row14940, row14941, row14942, row14943, row14944, row14945, row14946, row14947, row14948, row14949, row14950, row14951, row14952, row14953, row14954, row14955, row14956, row14957, row14958, row14959, row14960]

theorem entryCheck12_4 : entry12_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_4 k)) := by decide +kernel

theorem rowsSound12_4 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval14934 x
  · exact rowEval14935 x
  · exact rowEval14936 x
  · exact rowEval14937 x
  · exact rowEval14938 x
  · exact rowEval14939 x
  · exact rowEval14940 x
  · exact rowEval14941 x
  · exact rowEval14942 x
  · exact rowEval14943 x
  · exact rowEval14944 x
  · exact rowEval14945 x
  · exact rowEval14946 x
  · exact rowEval14947 x
  · exact rowEval14948 x
  · exact rowEval14949 x
  · exact rowEval14950 x
  · exact rowEval14951 x
  · exact rowEval14952 x
  · exact rowEval14953 x
  · exact rowEval14954 x
  · exact rowEval14955 x
  · exact rowEval14956 x
  · exact rowEval14957 x
  · exact rowEval14958 x
  · exact rowEval14959 x
  · exact rowEval14960 x

theorem entryEval12_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_4 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck12_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_4]

def rows12_5 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14961, row14962, row14963, row14964, row14965, row14966, row14967, row14968, row14969, row14970, row14971, row14972, row14973, row14974, row14975, row14976, row14977, row14978, row14979, row14980, row14981, row14982, row14983, row14984, row14985, row14986, row14987]

theorem entryCheck12_5 : entry12_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_5 k)) := by decide +kernel

theorem rowsSound12_5 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval14961 x
  · exact rowEval14962 x
  · exact rowEval14963 x
  · exact rowEval14964 x
  · exact rowEval14965 x
  · exact rowEval14966 x
  · exact rowEval14967 x
  · exact rowEval14968 x
  · exact rowEval14969 x
  · exact rowEval14970 x
  · exact rowEval14971 x
  · exact rowEval14972 x
  · exact rowEval14973 x
  · exact rowEval14974 x
  · exact rowEval14975 x
  · exact rowEval14976 x
  · exact rowEval14977 x
  · exact rowEval14978 x
  · exact rowEval14979 x
  · exact rowEval14980 x
  · exact rowEval14981 x
  · exact rowEval14982 x
  · exact rowEval14983 x
  · exact rowEval14984 x
  · exact rowEval14985 x
  · exact rowEval14986 x
  · exact rowEval14987 x

theorem entryEval12_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_5 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck12_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_5]

def rows12_6 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14988, row14989, row14990, row14991, row14992, row14993, row14994, row14995, row14996, row14997, row14998, row14999, row15000, row15001, row15002, row15003, row15004, row15005, row15006, row15007, row15008, row15009, row15010, row15011, row15012, row15013, row15014]

theorem entryCheck12_6 : entry12_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_6 k)) := by decide +kernel

theorem rowsSound12_6 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval14988 x
  · exact rowEval14989 x
  · exact rowEval14990 x
  · exact rowEval14991 x
  · exact rowEval14992 x
  · exact rowEval14993 x
  · exact rowEval14994 x
  · exact rowEval14995 x
  · exact rowEval14996 x
  · exact rowEval14997 x
  · exact rowEval14998 x
  · exact rowEval14999 x
  · exact rowEval15000 x
  · exact rowEval15001 x
  · exact rowEval15002 x
  · exact rowEval15003 x
  · exact rowEval15004 x
  · exact rowEval15005 x
  · exact rowEval15006 x
  · exact rowEval15007 x
  · exact rowEval15008 x
  · exact rowEval15009 x
  · exact rowEval15010 x
  · exact rowEval15011 x
  · exact rowEval15012 x
  · exact rowEval15013 x
  · exact rowEval15014 x

theorem entryEval12_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_6 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck12_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_6]

def rows12_7 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15015, row15016, row15017, row15018, row15019, row15020, row15021, row15022, row15023, row15024, row15025, row15026, row15027, row15028, row15029, row15030, row15031, row15032, row15033, row15034, row15035, row15036, row15037, row15038, row15039, row15040, row15041]

theorem entryCheck12_7 : entry12_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_7 k)) := by decide +kernel

theorem rowsSound12_7 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval15015 x
  · exact rowEval15016 x
  · exact rowEval15017 x
  · exact rowEval15018 x
  · exact rowEval15019 x
  · exact rowEval15020 x
  · exact rowEval15021 x
  · exact rowEval15022 x
  · exact rowEval15023 x
  · exact rowEval15024 x
  · exact rowEval15025 x
  · exact rowEval15026 x
  · exact rowEval15027 x
  · exact rowEval15028 x
  · exact rowEval15029 x
  · exact rowEval15030 x
  · exact rowEval15031 x
  · exact rowEval15032 x
  · exact rowEval15033 x
  · exact rowEval15034 x
  · exact rowEval15035 x
  · exact rowEval15036 x
  · exact rowEval15037 x
  · exact rowEval15038 x
  · exact rowEval15039 x
  · exact rowEval15040 x
  · exact rowEval15041 x

theorem entryEval12_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_7 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck12_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_7]

def rows12_8 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15042, row15043, row15044, row15045, row15046, row15047, row15048, row15049, row15050, row15051, row15052, row15053, row15054, row15055, row15056, row15057, row15058, row15059, row15060, row15061, row15062, row15063, row15064, row15065, row15066, row15067, row15068]

theorem entryCheck12_8 : entry12_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_8 k)) := by decide +kernel

theorem rowsSound12_8 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval15042 x
  · exact rowEval15043 x
  · exact rowEval15044 x
  · exact rowEval15045 x
  · exact rowEval15046 x
  · exact rowEval15047 x
  · exact rowEval15048 x
  · exact rowEval15049 x
  · exact rowEval15050 x
  · exact rowEval15051 x
  · exact rowEval15052 x
  · exact rowEval15053 x
  · exact rowEval15054 x
  · exact rowEval15055 x
  · exact rowEval15056 x
  · exact rowEval15057 x
  · exact rowEval15058 x
  · exact rowEval15059 x
  · exact rowEval15060 x
  · exact rowEval15061 x
  · exact rowEval15062 x
  · exact rowEval15063 x
  · exact rowEval15064 x
  · exact rowEval15065 x
  · exact rowEval15066 x
  · exact rowEval15067 x
  · exact rowEval15068 x

theorem entryEval12_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_8 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck12_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_8]

def rows12_9 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15069, row15070, row15071, row15072, row15073, row15074, row15075, row15076, row15077, row15078, row15079, row15080, row15081, row15082, row15083, row15084, row15085, row15086, row15087, row15088, row15089, row15090, row15091, row15092, row15093, row15094, row15095]

theorem entryCheck12_9 : entry12_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_9 k)) := by decide +kernel

theorem rowsSound12_9 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval15069 x
  · exact rowEval15070 x
  · exact rowEval15071 x
  · exact rowEval15072 x
  · exact rowEval15073 x
  · exact rowEval15074 x
  · exact rowEval15075 x
  · exact rowEval15076 x
  · exact rowEval15077 x
  · exact rowEval15078 x
  · exact rowEval15079 x
  · exact rowEval15080 x
  · exact rowEval15081 x
  · exact rowEval15082 x
  · exact rowEval15083 x
  · exact rowEval15084 x
  · exact rowEval15085 x
  · exact rowEval15086 x
  · exact rowEval15087 x
  · exact rowEval15088 x
  · exact rowEval15089 x
  · exact rowEval15090 x
  · exact rowEval15091 x
  · exact rowEval15092 x
  · exact rowEval15093 x
  · exact rowEval15094 x
  · exact rowEval15095 x

theorem entryEval12_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_9 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck12_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_9]

def rows12_10 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15096, row15097, row15098, row15099, row15100, row15101, row15102, row15103, row15104, row15105, row15106, row15107, row15108, row15109, row15110, row15111, row15112, row15113, row15114, row15115, row15116, row15117, row15118, row15119, row15120, row15121, row15122]

theorem entryCheck12_10 : entry12_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_10 k)) := by decide +kernel

theorem rowsSound12_10 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form10) x := by
  fin_cases k
  · exact rowEval15096 x
  · exact rowEval15097 x
  · exact rowEval15098 x
  · exact rowEval15099 x
  · exact rowEval15100 x
  · exact rowEval15101 x
  · exact rowEval15102 x
  · exact rowEval15103 x
  · exact rowEval15104 x
  · exact rowEval15105 x
  · exact rowEval15106 x
  · exact rowEval15107 x
  · exact rowEval15108 x
  · exact rowEval15109 x
  · exact rowEval15110 x
  · exact rowEval15111 x
  · exact rowEval15112 x
  · exact rowEval15113 x
  · exact rowEval15114 x
  · exact rowEval15115 x
  · exact rowEval15116 x
  · exact rowEval15117 x
  · exact rowEval15118 x
  · exact rowEval15119 x
  · exact rowEval15120 x
  · exact rowEval15121 x
  · exact rowEval15122 x

theorem entryEval12_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_10 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form10 B := by
  rw [entryCheck12_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_10]

def rows12_11 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15123, row15124, row15125, row15126, row15127, row15128, row15129, row15130, row15131, row15132, row15133, row15134, row15135, row15136, row15137, row15138, row15139, row15140, row15141, row15142, row15143, row15144, row15145, row15146, row15147, row15148, row15149]

theorem entryCheck12_11 : entry12_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_11 k)) := by decide +kernel

theorem rowsSound12_11 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval15123 x
  · exact rowEval15124 x
  · exact rowEval15125 x
  · exact rowEval15126 x
  · exact rowEval15127 x
  · exact rowEval15128 x
  · exact rowEval15129 x
  · exact rowEval15130 x
  · exact rowEval15131 x
  · exact rowEval15132 x
  · exact rowEval15133 x
  · exact rowEval15134 x
  · exact rowEval15135 x
  · exact rowEval15136 x
  · exact rowEval15137 x
  · exact rowEval15138 x
  · exact rowEval15139 x
  · exact rowEval15140 x
  · exact rowEval15141 x
  · exact rowEval15142 x
  · exact rowEval15143 x
  · exact rowEval15144 x
  · exact rowEval15145 x
  · exact rowEval15146 x
  · exact rowEval15147 x
  · exact rowEval15148 x
  · exact rowEval15149 x

theorem entryEval12_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_11 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck12_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_11]

def rows12_12 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15150, row15151, row15152, row15153, row15154, row15155, row15156, row15157, row15158, row15159, row15160, row15161, row15162, row15163, row15164, row15165, row15166, row15167, row15168, row15169, row15170, row15171, row15172, row15173, row15174, row15175, row15176]

theorem entryCheck12_12 : entry12_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_12 k)) := by decide +kernel

theorem rowsSound12_12 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form12) x := by
  fin_cases k
  · exact rowEval15150 x
  · exact rowEval15151 x
  · exact rowEval15152 x
  · exact rowEval15153 x
  · exact rowEval15154 x
  · exact rowEval15155 x
  · exact rowEval15156 x
  · exact rowEval15157 x
  · exact rowEval15158 x
  · exact rowEval15159 x
  · exact rowEval15160 x
  · exact rowEval15161 x
  · exact rowEval15162 x
  · exact rowEval15163 x
  · exact rowEval15164 x
  · exact rowEval15165 x
  · exact rowEval15166 x
  · exact rowEval15167 x
  · exact rowEval15168 x
  · exact rowEval15169 x
  · exact rowEval15170 x
  · exact rowEval15171 x
  · exact rowEval15172 x
  · exact rowEval15173 x
  · exact rowEval15174 x
  · exact rowEval15175 x
  · exact rowEval15176 x

theorem entryEval12_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_12 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form12 B := by
  rw [entryCheck12_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_12]

end MUB6.Certificate.GramEntries.Block4

end OAI
