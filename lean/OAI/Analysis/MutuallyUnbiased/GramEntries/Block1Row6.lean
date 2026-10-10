import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block30
import OAI.Analysis.MutuallyUnbiased.GramRows.Block31
import OAI.Analysis.MutuallyUnbiased.GramRows.Block32
import OAI.Analysis.MutuallyUnbiased.GramRows.Block33

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows6_0 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1084, row1085, row1086, row1087, row1088, row1089, row1090, row1091, row1092, row1093, row1094, row1095, row1096, row1097]

theorem entryCheck6_0 : entry6_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form6.terms k).coefficient) (rows6_0 k)) := by decide +kernel

theorem rowsSound6_0 (k : Fin GramFunctions.Block1.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form6.terms k).tag (GramFunctions.Block1.form6.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval1084 x
  · exact rowEval1085 x
  · exact rowEval1086 x
  · exact rowEval1087 x
  · exact rowEval1088 x
  · exact rowEval1089 x
  · exact rowEval1090 x
  · exact rowEval1091 x
  · exact rowEval1092 x
  · exact rowEval1093 x
  · exact rowEval1094 x
  · exact rowEval1095 x
  · exact rowEval1096 x
  · exact rowEval1097 x

theorem entryEval6_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_0 (GramNormalization.eval B) = GramFunctions.Block1.form6.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck6_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form6 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_0]

def rows6_1 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1098, row1099, row1100, row1101, row1102, row1103, row1104, row1105, row1106, row1107, row1108, row1109, row1110, row1111]

theorem entryCheck6_1 : entry6_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form6.terms k).coefficient) (rows6_1 k)) := by decide +kernel

theorem rowsSound6_1 (k : Fin GramFunctions.Block1.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form6.terms k).tag (GramFunctions.Block1.form6.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval1098 x
  · exact rowEval1099 x
  · exact rowEval1100 x
  · exact rowEval1101 x
  · exact rowEval1102 x
  · exact rowEval1103 x
  · exact rowEval1104 x
  · exact rowEval1105 x
  · exact rowEval1106 x
  · exact rowEval1107 x
  · exact rowEval1108 x
  · exact rowEval1109 x
  · exact rowEval1110 x
  · exact rowEval1111 x

theorem entryEval6_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_1 (GramNormalization.eval B) = GramFunctions.Block1.form6.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck6_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form6 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_1]

def rows6_2 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1112, row1113, row1114, row1115, row1116, row1117, row1118, row1119, row1120, row1121, row1122, row1123, row1124, row1125]

theorem entryCheck6_2 : entry6_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form6.terms k).coefficient) (rows6_2 k)) := by decide +kernel

theorem rowsSound6_2 (k : Fin GramFunctions.Block1.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form6.terms k).tag (GramFunctions.Block1.form6.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval1112 x
  · exact rowEval1113 x
  · exact rowEval1114 x
  · exact rowEval1115 x
  · exact rowEval1116 x
  · exact rowEval1117 x
  · exact rowEval1118 x
  · exact rowEval1119 x
  · exact rowEval1120 x
  · exact rowEval1121 x
  · exact rowEval1122 x
  · exact rowEval1123 x
  · exact rowEval1124 x
  · exact rowEval1125 x

theorem entryEval6_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_2 (GramNormalization.eval B) = GramFunctions.Block1.form6.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck6_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form6 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_2]

def rows6_3 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1126, row1127, row1128, row1129, row1130, row1131, row1132, row1133, row1134, row1135, row1136, row1137, row1138, row1139]

theorem entryCheck6_3 : entry6_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form6.terms k).coefficient) (rows6_3 k)) := by decide +kernel

theorem rowsSound6_3 (k : Fin GramFunctions.Block1.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form6.terms k).tag (GramFunctions.Block1.form6.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval1126 x
  · exact rowEval1127 x
  · exact rowEval1128 x
  · exact rowEval1129 x
  · exact rowEval1130 x
  · exact rowEval1131 x
  · exact rowEval1132 x
  · exact rowEval1133 x
  · exact rowEval1134 x
  · exact rowEval1135 x
  · exact rowEval1136 x
  · exact rowEval1137 x
  · exact rowEval1138 x
  · exact rowEval1139 x

theorem entryEval6_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_3 (GramNormalization.eval B) = GramFunctions.Block1.form6.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck6_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form6 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_3]

def rows6_4 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1140, row1141, row1142, row1143, row1144, row1145, row1146, row1147, row1148, row1149, row1150, row1151, row1152, row1153]

theorem entryCheck6_4 : entry6_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form6.terms k).coefficient) (rows6_4 k)) := by decide +kernel

theorem rowsSound6_4 (k : Fin GramFunctions.Block1.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form6.terms k).tag (GramFunctions.Block1.form6.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval1140 x
  · exact rowEval1141 x
  · exact rowEval1142 x
  · exact rowEval1143 x
  · exact rowEval1144 x
  · exact rowEval1145 x
  · exact rowEval1146 x
  · exact rowEval1147 x
  · exact rowEval1148 x
  · exact rowEval1149 x
  · exact rowEval1150 x
  · exact rowEval1151 x
  · exact rowEval1152 x
  · exact rowEval1153 x

theorem entryEval6_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_4 (GramNormalization.eval B) = GramFunctions.Block1.form6.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck6_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form6 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_4]

def rows6_5 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1154, row1155, row1156, row1157, row1158, row1159, row1160, row1161, row1162, row1163, row1164, row1165, row1166, row1167]

theorem entryCheck6_5 : entry6_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form6.terms k).coefficient) (rows6_5 k)) := by decide +kernel

theorem rowsSound6_5 (k : Fin GramFunctions.Block1.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form6.terms k).tag (GramFunctions.Block1.form6.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval1154 x
  · exact rowEval1155 x
  · exact rowEval1156 x
  · exact rowEval1157 x
  · exact rowEval1158 x
  · exact rowEval1159 x
  · exact rowEval1160 x
  · exact rowEval1161 x
  · exact rowEval1162 x
  · exact rowEval1163 x
  · exact rowEval1164 x
  · exact rowEval1165 x
  · exact rowEval1166 x
  · exact rowEval1167 x

theorem entryEval6_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_5 (GramNormalization.eval B) = GramFunctions.Block1.form6.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck6_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form6 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_5]

def rows6_6 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1168, row1169, row1170, row1171, row1172, row1173, row1174, row1175, row1176, row1177, row1178, row1179, row1180, row1181]

theorem entryCheck6_6 : entry6_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form6.terms k).coefficient) (rows6_6 k)) := by decide +kernel

theorem rowsSound6_6 (k : Fin GramFunctions.Block1.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form6.terms k).tag (GramFunctions.Block1.form6.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval1168 x
  · exact rowEval1169 x
  · exact rowEval1170 x
  · exact rowEval1171 x
  · exact rowEval1172 x
  · exact rowEval1173 x
  · exact rowEval1174 x
  · exact rowEval1175 x
  · exact rowEval1176 x
  · exact rowEval1177 x
  · exact rowEval1178 x
  · exact rowEval1179 x
  · exact rowEval1180 x
  · exact rowEval1181 x

theorem entryEval6_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_6 (GramNormalization.eval B) = GramFunctions.Block1.form6.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck6_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form6 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_6]

end MUB6.Certificate.GramEntries.Block1

end OAI
