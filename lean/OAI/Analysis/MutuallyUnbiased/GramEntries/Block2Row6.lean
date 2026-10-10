import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramRows.Block70
import OAI.Analysis.MutuallyUnbiased.GramRows.Block71
import OAI.Analysis.MutuallyUnbiased.GramRows.Block72

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows6_0 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row5898, row5899, row5900, row5901, row5902, row5903, row5904, row5905, row5906, row5907, row5908, row5909, row5910, row5911, row5912, row5913, row5914, row5915, row5916, row5917, row5918, row5919, row5920, row5921, row5922, row5923, row5924, row5925, row5926, row5927, row5928, row5929, row5930, row5931, row5932, row5933, row5934, row5935, row5936, row5937]

theorem entryCheck6_0 : entry6_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form6.terms k).coefficient) (rows6_0 k)) := by decide +kernel

theorem rowsSound6_0 (k : Fin GramFunctions.Block2.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form6.terms k).tag (GramFunctions.Block2.form6.terms k).charge GramFunctions.Block2.form0) x := by
  fin_cases k
  · exact rowEval5898 x
  · exact rowEval5899 x
  · exact rowEval5900 x
  · exact rowEval5901 x
  · exact rowEval5902 x
  · exact rowEval5903 x
  · exact rowEval5904 x
  · exact rowEval5905 x
  · exact rowEval5906 x
  · exact rowEval5907 x
  · exact rowEval5908 x
  · exact rowEval5909 x
  · exact rowEval5910 x
  · exact rowEval5911 x
  · exact rowEval5912 x
  · exact rowEval5913 x
  · exact rowEval5914 x
  · exact rowEval5915 x
  · exact rowEval5916 x
  · exact rowEval5917 x
  · exact rowEval5918 x
  · exact rowEval5919 x
  · exact rowEval5920 x
  · exact rowEval5921 x
  · exact rowEval5922 x
  · exact rowEval5923 x
  · exact rowEval5924 x
  · exact rowEval5925 x
  · exact rowEval5926 x
  · exact rowEval5927 x
  · exact rowEval5928 x
  · exact rowEval5929 x
  · exact rowEval5930 x
  · exact rowEval5931 x
  · exact rowEval5932 x
  · exact rowEval5933 x
  · exact rowEval5934 x
  · exact rowEval5935 x
  · exact rowEval5936 x
  · exact rowEval5937 x

theorem entryEval6_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_0 (GramNormalization.eval B) = GramFunctions.Block2.form6.mixedGram GramFunctions.Block2.form0 B := by
  rw [entryCheck6_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form6 GramFunctions.Block2.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_0]

def rows6_1 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row5938, row5939, row5940, row5941, row5942, row5943, row5944, row5945, row5946, row5947, row5948, row5949, row5950, row5951, row5952, row5953, row5954, row5955, row5956, row5957, row5958, row5959, row5960, row5961, row5962, row5963, row5964, row5965, row5966, row5967, row5968, row5969, row5970, row5971, row5972, row5973, row5974, row5975, row5976, row5977]

theorem entryCheck6_1 : entry6_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form6.terms k).coefficient) (rows6_1 k)) := by decide +kernel

theorem rowsSound6_1 (k : Fin GramFunctions.Block2.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form6.terms k).tag (GramFunctions.Block2.form6.terms k).charge GramFunctions.Block2.form1) x := by
  fin_cases k
  · exact rowEval5938 x
  · exact rowEval5939 x
  · exact rowEval5940 x
  · exact rowEval5941 x
  · exact rowEval5942 x
  · exact rowEval5943 x
  · exact rowEval5944 x
  · exact rowEval5945 x
  · exact rowEval5946 x
  · exact rowEval5947 x
  · exact rowEval5948 x
  · exact rowEval5949 x
  · exact rowEval5950 x
  · exact rowEval5951 x
  · exact rowEval5952 x
  · exact rowEval5953 x
  · exact rowEval5954 x
  · exact rowEval5955 x
  · exact rowEval5956 x
  · exact rowEval5957 x
  · exact rowEval5958 x
  · exact rowEval5959 x
  · exact rowEval5960 x
  · exact rowEval5961 x
  · exact rowEval5962 x
  · exact rowEval5963 x
  · exact rowEval5964 x
  · exact rowEval5965 x
  · exact rowEval5966 x
  · exact rowEval5967 x
  · exact rowEval5968 x
  · exact rowEval5969 x
  · exact rowEval5970 x
  · exact rowEval5971 x
  · exact rowEval5972 x
  · exact rowEval5973 x
  · exact rowEval5974 x
  · exact rowEval5975 x
  · exact rowEval5976 x
  · exact rowEval5977 x

theorem entryEval6_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_1 (GramNormalization.eval B) = GramFunctions.Block2.form6.mixedGram GramFunctions.Block2.form1 B := by
  rw [entryCheck6_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form6 GramFunctions.Block2.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_1]

def rows6_2 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row5978, row5979, row5980, row5981, row5982, row5983, row5984, row5985, row5986, row5987, row5988, row5989, row5990, row5991, row5992, row5993, row5994, row5995, row5996, row5997, row5998, row5999, row6000, row6001, row6002, row6003, row6004, row6005, row6006, row6007, row6008, row6009, row6010, row6011, row6012, row6013, row6014, row6015, row6016, row6017]

theorem entryCheck6_2 : entry6_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form6.terms k).coefficient) (rows6_2 k)) := by decide +kernel

theorem rowsSound6_2 (k : Fin GramFunctions.Block2.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form6.terms k).tag (GramFunctions.Block2.form6.terms k).charge GramFunctions.Block2.form2) x := by
  fin_cases k
  · exact rowEval5978 x
  · exact rowEval5979 x
  · exact rowEval5980 x
  · exact rowEval5981 x
  · exact rowEval5982 x
  · exact rowEval5983 x
  · exact rowEval5984 x
  · exact rowEval5985 x
  · exact rowEval5986 x
  · exact rowEval5987 x
  · exact rowEval5988 x
  · exact rowEval5989 x
  · exact rowEval5990 x
  · exact rowEval5991 x
  · exact rowEval5992 x
  · exact rowEval5993 x
  · exact rowEval5994 x
  · exact rowEval5995 x
  · exact rowEval5996 x
  · exact rowEval5997 x
  · exact rowEval5998 x
  · exact rowEval5999 x
  · exact rowEval6000 x
  · exact rowEval6001 x
  · exact rowEval6002 x
  · exact rowEval6003 x
  · exact rowEval6004 x
  · exact rowEval6005 x
  · exact rowEval6006 x
  · exact rowEval6007 x
  · exact rowEval6008 x
  · exact rowEval6009 x
  · exact rowEval6010 x
  · exact rowEval6011 x
  · exact rowEval6012 x
  · exact rowEval6013 x
  · exact rowEval6014 x
  · exact rowEval6015 x
  · exact rowEval6016 x
  · exact rowEval6017 x

theorem entryEval6_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_2 (GramNormalization.eval B) = GramFunctions.Block2.form6.mixedGram GramFunctions.Block2.form2 B := by
  rw [entryCheck6_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form6 GramFunctions.Block2.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_2]

def rows6_3 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row6018, row6019, row6020, row6021, row6022, row6023, row6024, row6025, row6026, row6027, row6028, row6029, row6030, row6031, row6032, row6033, row6034, row6035, row6036, row6037, row6038, row6039, row6040, row6041, row6042, row6043, row6044, row6045, row6046, row6047, row6048, row6049, row6050, row6051, row6052, row6053, row6054, row6055, row6056, row6057]

theorem entryCheck6_3 : entry6_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form6.terms k).coefficient) (rows6_3 k)) := by decide +kernel

theorem rowsSound6_3 (k : Fin GramFunctions.Block2.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form6.terms k).tag (GramFunctions.Block2.form6.terms k).charge GramFunctions.Block2.form3) x := by
  fin_cases k
  · exact rowEval6018 x
  · exact rowEval6019 x
  · exact rowEval6020 x
  · exact rowEval6021 x
  · exact rowEval6022 x
  · exact rowEval6023 x
  · exact rowEval6024 x
  · exact rowEval6025 x
  · exact rowEval6026 x
  · exact rowEval6027 x
  · exact rowEval6028 x
  · exact rowEval6029 x
  · exact rowEval6030 x
  · exact rowEval6031 x
  · exact rowEval6032 x
  · exact rowEval6033 x
  · exact rowEval6034 x
  · exact rowEval6035 x
  · exact rowEval6036 x
  · exact rowEval6037 x
  · exact rowEval6038 x
  · exact rowEval6039 x
  · exact rowEval6040 x
  · exact rowEval6041 x
  · exact rowEval6042 x
  · exact rowEval6043 x
  · exact rowEval6044 x
  · exact rowEval6045 x
  · exact rowEval6046 x
  · exact rowEval6047 x
  · exact rowEval6048 x
  · exact rowEval6049 x
  · exact rowEval6050 x
  · exact rowEval6051 x
  · exact rowEval6052 x
  · exact rowEval6053 x
  · exact rowEval6054 x
  · exact rowEval6055 x
  · exact rowEval6056 x
  · exact rowEval6057 x

theorem entryEval6_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_3 (GramNormalization.eval B) = GramFunctions.Block2.form6.mixedGram GramFunctions.Block2.form3 B := by
  rw [entryCheck6_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form6 GramFunctions.Block2.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_3]

def rows6_4 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row6058, row6059, row6060, row6061, row6062, row6063, row6064, row6065, row6066, row6067, row6068, row6069, row6070, row6071, row6072, row6073, row6074, row6075, row6076, row6077, row6078, row6079, row6080, row6081, row6082, row6083, row6084, row6085, row6086, row6087, row6088, row6089, row6090, row6091, row6092, row6093, row6094, row6095, row6096, row6097]

theorem entryCheck6_4 : entry6_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form6.terms k).coefficient) (rows6_4 k)) := by decide +kernel

theorem rowsSound6_4 (k : Fin GramFunctions.Block2.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form6.terms k).tag (GramFunctions.Block2.form6.terms k).charge GramFunctions.Block2.form4) x := by
  fin_cases k
  · exact rowEval6058 x
  · exact rowEval6059 x
  · exact rowEval6060 x
  · exact rowEval6061 x
  · exact rowEval6062 x
  · exact rowEval6063 x
  · exact rowEval6064 x
  · exact rowEval6065 x
  · exact rowEval6066 x
  · exact rowEval6067 x
  · exact rowEval6068 x
  · exact rowEval6069 x
  · exact rowEval6070 x
  · exact rowEval6071 x
  · exact rowEval6072 x
  · exact rowEval6073 x
  · exact rowEval6074 x
  · exact rowEval6075 x
  · exact rowEval6076 x
  · exact rowEval6077 x
  · exact rowEval6078 x
  · exact rowEval6079 x
  · exact rowEval6080 x
  · exact rowEval6081 x
  · exact rowEval6082 x
  · exact rowEval6083 x
  · exact rowEval6084 x
  · exact rowEval6085 x
  · exact rowEval6086 x
  · exact rowEval6087 x
  · exact rowEval6088 x
  · exact rowEval6089 x
  · exact rowEval6090 x
  · exact rowEval6091 x
  · exact rowEval6092 x
  · exact rowEval6093 x
  · exact rowEval6094 x
  · exact rowEval6095 x
  · exact rowEval6096 x
  · exact rowEval6097 x

theorem entryEval6_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_4 (GramNormalization.eval B) = GramFunctions.Block2.form6.mixedGram GramFunctions.Block2.form4 B := by
  rw [entryCheck6_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form6 GramFunctions.Block2.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_4]

def rows6_5 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row6098, row6099, row6100, row6101, row6102, row6103, row6104, row6105, row6106, row6107, row6108, row6109, row6110, row6111, row6112, row6113, row6114, row6115, row6116, row6117, row6118, row6119, row6120, row6121, row6122, row6123, row6124, row6125, row6126, row6127, row6128, row6129, row6130, row6131, row6132, row6133, row6134, row6135, row6136, row6137]

theorem entryCheck6_5 : entry6_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form6.terms k).coefficient) (rows6_5 k)) := by decide +kernel

theorem rowsSound6_5 (k : Fin GramFunctions.Block2.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form6.terms k).tag (GramFunctions.Block2.form6.terms k).charge GramFunctions.Block2.form5) x := by
  fin_cases k
  · exact rowEval6098 x
  · exact rowEval6099 x
  · exact rowEval6100 x
  · exact rowEval6101 x
  · exact rowEval6102 x
  · exact rowEval6103 x
  · exact rowEval6104 x
  · exact rowEval6105 x
  · exact rowEval6106 x
  · exact rowEval6107 x
  · exact rowEval6108 x
  · exact rowEval6109 x
  · exact rowEval6110 x
  · exact rowEval6111 x
  · exact rowEval6112 x
  · exact rowEval6113 x
  · exact rowEval6114 x
  · exact rowEval6115 x
  · exact rowEval6116 x
  · exact rowEval6117 x
  · exact rowEval6118 x
  · exact rowEval6119 x
  · exact rowEval6120 x
  · exact rowEval6121 x
  · exact rowEval6122 x
  · exact rowEval6123 x
  · exact rowEval6124 x
  · exact rowEval6125 x
  · exact rowEval6126 x
  · exact rowEval6127 x
  · exact rowEval6128 x
  · exact rowEval6129 x
  · exact rowEval6130 x
  · exact rowEval6131 x
  · exact rowEval6132 x
  · exact rowEval6133 x
  · exact rowEval6134 x
  · exact rowEval6135 x
  · exact rowEval6136 x
  · exact rowEval6137 x

theorem entryEval6_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_5 (GramNormalization.eval B) = GramFunctions.Block2.form6.mixedGram GramFunctions.Block2.form5 B := by
  rw [entryCheck6_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form6 GramFunctions.Block2.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_5]

def rows6_6 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row6138, row6139, row6140, row6141, row6142, row6143, row6144, row6145, row6146, row6147, row6148, row6149, row6150, row6151, row6152, row6153, row6154, row6155, row6156, row6157, row6158, row6159, row6160, row6161, row6162, row6163, row6164, row6165, row6166, row6167, row6168, row6169, row6170, row6171, row6172, row6173, row6174, row6175, row6176, row6177]

theorem entryCheck6_6 : entry6_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form6.terms k).coefficient) (rows6_6 k)) := by decide +kernel

theorem rowsSound6_6 (k : Fin GramFunctions.Block2.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form6.terms k).tag (GramFunctions.Block2.form6.terms k).charge GramFunctions.Block2.form6) x := by
  fin_cases k
  · exact rowEval6138 x
  · exact rowEval6139 x
  · exact rowEval6140 x
  · exact rowEval6141 x
  · exact rowEval6142 x
  · exact rowEval6143 x
  · exact rowEval6144 x
  · exact rowEval6145 x
  · exact rowEval6146 x
  · exact rowEval6147 x
  · exact rowEval6148 x
  · exact rowEval6149 x
  · exact rowEval6150 x
  · exact rowEval6151 x
  · exact rowEval6152 x
  · exact rowEval6153 x
  · exact rowEval6154 x
  · exact rowEval6155 x
  · exact rowEval6156 x
  · exact rowEval6157 x
  · exact rowEval6158 x
  · exact rowEval6159 x
  · exact rowEval6160 x
  · exact rowEval6161 x
  · exact rowEval6162 x
  · exact rowEval6163 x
  · exact rowEval6164 x
  · exact rowEval6165 x
  · exact rowEval6166 x
  · exact rowEval6167 x
  · exact rowEval6168 x
  · exact rowEval6169 x
  · exact rowEval6170 x
  · exact rowEval6171 x
  · exact rowEval6172 x
  · exact rowEval6173 x
  · exact rowEval6174 x
  · exact rowEval6175 x
  · exact rowEval6176 x
  · exact rowEval6177 x

theorem entryEval6_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_6 (GramNormalization.eval B) = GramFunctions.Block2.form6.mixedGram GramFunctions.Block2.form6 B := by
  rw [entryCheck6_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form6 GramFunctions.Block2.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_6]

end MUB6.Certificate.GramEntries.Block2

end OAI
