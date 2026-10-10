import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block25
import OAI.Analysis.MutuallyUnbiased.GramRows.Block26
import OAI.Analysis.MutuallyUnbiased.GramRows.Block27
import OAI.Analysis.MutuallyUnbiased.GramRows.Block28
import OAI.Analysis.MutuallyUnbiased.GramRows.Block29
import OAI.Analysis.MutuallyUnbiased.GramRows.Block30

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows5_0 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row904, row905, row906, row907, row908, row909, row910, row911, row912, row913, row914, row915, row916, row917, row918, row919, row920, row921, row922, row923, row924, row925, row926, row927, row928, row929, row930, row931, row932, row933]

theorem entryCheck5_0 : entry5_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form5.terms k).coefficient) (rows5_0 k)) := by decide +kernel

theorem rowsSound5_0 (k : Fin GramFunctions.Block1.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form5.terms k).tag (GramFunctions.Block1.form5.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval904 x
  · exact rowEval905 x
  · exact rowEval906 x
  · exact rowEval907 x
  · exact rowEval908 x
  · exact rowEval909 x
  · exact rowEval910 x
  · exact rowEval911 x
  · exact rowEval912 x
  · exact rowEval913 x
  · exact rowEval914 x
  · exact rowEval915 x
  · exact rowEval916 x
  · exact rowEval917 x
  · exact rowEval918 x
  · exact rowEval919 x
  · exact rowEval920 x
  · exact rowEval921 x
  · exact rowEval922 x
  · exact rowEval923 x
  · exact rowEval924 x
  · exact rowEval925 x
  · exact rowEval926 x
  · exact rowEval927 x
  · exact rowEval928 x
  · exact rowEval929 x
  · exact rowEval930 x
  · exact rowEval931 x
  · exact rowEval932 x
  · exact rowEval933 x

theorem entryEval5_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_0 (GramNormalization.eval B) = GramFunctions.Block1.form5.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck5_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form5 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_0]

def rows5_1 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row934, row935, row936, row937, row938, row939, row940, row941, row942, row943, row944, row945, row946, row947, row948, row949, row950, row951, row952, row953, row954, row955, row956, row957, row958, row959, row960, row961, row962, row963]

theorem entryCheck5_1 : entry5_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form5.terms k).coefficient) (rows5_1 k)) := by decide +kernel

theorem rowsSound5_1 (k : Fin GramFunctions.Block1.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form5.terms k).tag (GramFunctions.Block1.form5.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval934 x
  · exact rowEval935 x
  · exact rowEval936 x
  · exact rowEval937 x
  · exact rowEval938 x
  · exact rowEval939 x
  · exact rowEval940 x
  · exact rowEval941 x
  · exact rowEval942 x
  · exact rowEval943 x
  · exact rowEval944 x
  · exact rowEval945 x
  · exact rowEval946 x
  · exact rowEval947 x
  · exact rowEval948 x
  · exact rowEval949 x
  · exact rowEval950 x
  · exact rowEval951 x
  · exact rowEval952 x
  · exact rowEval953 x
  · exact rowEval954 x
  · exact rowEval955 x
  · exact rowEval956 x
  · exact rowEval957 x
  · exact rowEval958 x
  · exact rowEval959 x
  · exact rowEval960 x
  · exact rowEval961 x
  · exact rowEval962 x
  · exact rowEval963 x

theorem entryEval5_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_1 (GramNormalization.eval B) = GramFunctions.Block1.form5.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck5_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form5 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_1]

def rows5_2 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row964, row965, row966, row967, row968, row969, row970, row971, row972, row973, row974, row975, row976, row977, row978, row979, row980, row981, row982, row983, row984, row985, row986, row987, row988, row989, row990, row991, row992, row993]

theorem entryCheck5_2 : entry5_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form5.terms k).coefficient) (rows5_2 k)) := by decide +kernel

theorem rowsSound5_2 (k : Fin GramFunctions.Block1.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form5.terms k).tag (GramFunctions.Block1.form5.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval964 x
  · exact rowEval965 x
  · exact rowEval966 x
  · exact rowEval967 x
  · exact rowEval968 x
  · exact rowEval969 x
  · exact rowEval970 x
  · exact rowEval971 x
  · exact rowEval972 x
  · exact rowEval973 x
  · exact rowEval974 x
  · exact rowEval975 x
  · exact rowEval976 x
  · exact rowEval977 x
  · exact rowEval978 x
  · exact rowEval979 x
  · exact rowEval980 x
  · exact rowEval981 x
  · exact rowEval982 x
  · exact rowEval983 x
  · exact rowEval984 x
  · exact rowEval985 x
  · exact rowEval986 x
  · exact rowEval987 x
  · exact rowEval988 x
  · exact rowEval989 x
  · exact rowEval990 x
  · exact rowEval991 x
  · exact rowEval992 x
  · exact rowEval993 x

theorem entryEval5_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_2 (GramNormalization.eval B) = GramFunctions.Block1.form5.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck5_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form5 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_2]

def rows5_3 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row994, row995, row996, row997, row998, row999, row1000, row1001, row1002, row1003, row1004, row1005, row1006, row1007, row1008, row1009, row1010, row1011, row1012, row1013, row1014, row1015, row1016, row1017, row1018, row1019, row1020, row1021, row1022, row1023]

theorem entryCheck5_3 : entry5_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form5.terms k).coefficient) (rows5_3 k)) := by decide +kernel

theorem rowsSound5_3 (k : Fin GramFunctions.Block1.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form5.terms k).tag (GramFunctions.Block1.form5.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval994 x
  · exact rowEval995 x
  · exact rowEval996 x
  · exact rowEval997 x
  · exact rowEval998 x
  · exact rowEval999 x
  · exact rowEval1000 x
  · exact rowEval1001 x
  · exact rowEval1002 x
  · exact rowEval1003 x
  · exact rowEval1004 x
  · exact rowEval1005 x
  · exact rowEval1006 x
  · exact rowEval1007 x
  · exact rowEval1008 x
  · exact rowEval1009 x
  · exact rowEval1010 x
  · exact rowEval1011 x
  · exact rowEval1012 x
  · exact rowEval1013 x
  · exact rowEval1014 x
  · exact rowEval1015 x
  · exact rowEval1016 x
  · exact rowEval1017 x
  · exact rowEval1018 x
  · exact rowEval1019 x
  · exact rowEval1020 x
  · exact rowEval1021 x
  · exact rowEval1022 x
  · exact rowEval1023 x

theorem entryEval5_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_3 (GramNormalization.eval B) = GramFunctions.Block1.form5.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck5_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form5 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_3]

def rows5_4 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row1024, row1025, row1026, row1027, row1028, row1029, row1030, row1031, row1032, row1033, row1034, row1035, row1036, row1037, row1038, row1039, row1040, row1041, row1042, row1043, row1044, row1045, row1046, row1047, row1048, row1049, row1050, row1051, row1052, row1053]

theorem entryCheck5_4 : entry5_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form5.terms k).coefficient) (rows5_4 k)) := by decide +kernel

theorem rowsSound5_4 (k : Fin GramFunctions.Block1.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form5.terms k).tag (GramFunctions.Block1.form5.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval1024 x
  · exact rowEval1025 x
  · exact rowEval1026 x
  · exact rowEval1027 x
  · exact rowEval1028 x
  · exact rowEval1029 x
  · exact rowEval1030 x
  · exact rowEval1031 x
  · exact rowEval1032 x
  · exact rowEval1033 x
  · exact rowEval1034 x
  · exact rowEval1035 x
  · exact rowEval1036 x
  · exact rowEval1037 x
  · exact rowEval1038 x
  · exact rowEval1039 x
  · exact rowEval1040 x
  · exact rowEval1041 x
  · exact rowEval1042 x
  · exact rowEval1043 x
  · exact rowEval1044 x
  · exact rowEval1045 x
  · exact rowEval1046 x
  · exact rowEval1047 x
  · exact rowEval1048 x
  · exact rowEval1049 x
  · exact rowEval1050 x
  · exact rowEval1051 x
  · exact rowEval1052 x
  · exact rowEval1053 x

theorem entryEval5_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_4 (GramNormalization.eval B) = GramFunctions.Block1.form5.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck5_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form5 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_4]

def rows5_5 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row1054, row1055, row1056, row1057, row1058, row1059, row1060, row1061, row1062, row1063, row1064, row1065, row1066, row1067, row1068, row1069, row1070, row1071, row1072, row1073, row1074, row1075, row1076, row1077, row1078, row1079, row1080, row1081, row1082, row1083]

theorem entryCheck5_5 : entry5_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form5.terms k).coefficient) (rows5_5 k)) := by decide +kernel

theorem rowsSound5_5 (k : Fin GramFunctions.Block1.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form5.terms k).tag (GramFunctions.Block1.form5.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval1054 x
  · exact rowEval1055 x
  · exact rowEval1056 x
  · exact rowEval1057 x
  · exact rowEval1058 x
  · exact rowEval1059 x
  · exact rowEval1060 x
  · exact rowEval1061 x
  · exact rowEval1062 x
  · exact rowEval1063 x
  · exact rowEval1064 x
  · exact rowEval1065 x
  · exact rowEval1066 x
  · exact rowEval1067 x
  · exact rowEval1068 x
  · exact rowEval1069 x
  · exact rowEval1070 x
  · exact rowEval1071 x
  · exact rowEval1072 x
  · exact rowEval1073 x
  · exact rowEval1074 x
  · exact rowEval1075 x
  · exact rowEval1076 x
  · exact rowEval1077 x
  · exact rowEval1078 x
  · exact rowEval1079 x
  · exact rowEval1080 x
  · exact rowEval1081 x
  · exact rowEval1082 x
  · exact rowEval1083 x

theorem entryEval5_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_5 (GramNormalization.eval B) = GramFunctions.Block1.form5.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck5_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form5 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_5]

end MUB6.Certificate.GramEntries.Block1

end OAI
