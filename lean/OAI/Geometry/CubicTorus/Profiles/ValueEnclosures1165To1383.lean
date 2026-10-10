import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ValueEnclosures945To1164

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def e1165 : ℝ := e1163 ^ 3
lemma b1165 : Encl e1165 (164371854979 / 200000000000 : ℝ) (821859274899 / 1000000000000 : ℝ) := by
  exact Encl.pow b1163 (by norm_num) 3 (by norm_num) (by norm_num)

def e1166 : ℝ := e1165 / e35
lemma b1166 : Encl e1166 (273953091631 / 1000000000000 : ℝ) (273953091633 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1165 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1167 : ℝ := e1164 + e1166
lemma b1167 : Encl e1167 (1961352997 / 500000000000 : ℝ) (1961352999 / 500000000000 : ℝ) := by
  exact Encl.add b1164 b1166 (by norm_num) (by norm_num)

def e1168 : ℝ := e8 * e1167
lemma b1168 : Encl e1168 (1922125937 / 500000000000 : ℝ) (3844251879 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1167 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1169 : ℝ := e1161 / e1163
lemma b1169 : Encl e1169 (65441986769 / 500000000000 : ℝ) (6544198677 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b1161 b1163 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1170 : ℝ := e1169 - e23
lemma b1170 : Encl e1170 (-934558013231 / 500000000000 : ℝ) (-93455801323 / 50000000000 : ℝ) := by
  exact Encl.sub b1169 b23 (by norm_num) (by norm_num)

def e1171 : ℝ := e23 * e1163
lemma b1171 : Encl e1171 (468348526151 / 250000000000 : ℝ) (936697052303 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1163 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1172 : ℝ := e1170 + e1171
lemma b1172 : Encl e1172 (2139039071 / 500000000000 : ℝ) (2139039073 / 500000000000 : ℝ) := by
  exact Encl.add b1170 b1171 (by norm_num) (by norm_num)

def e1173 : ℝ := e1172 / e43
lemma b1173 : Encl e1173 (42780781 / 500000000000 : ℝ) (85561563 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1172 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1174 : ℝ := e1168 - e1173
lemma b1174 : Encl e1174 (3758690311 / 1000000000000 : ℝ) (3758690317 / 1000000000000 : ℝ) := by
  exact Encl.sub b1168 b1173 (by norm_num) (by norm_num)

def e1175 : ℝ := e1160 * e1174
lemma b1175 : Encl e1175 (9758904023 / 1000000000000 : ℝ) (9758904039 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1160 b1174 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1176 : ℝ := e1159 + e1175
lemma b1176 : Encl e1176 (-43121458923 / 100000000000 : ℝ) (-107803647303 / 250000000000 : ℝ) := by
  exact Encl.add b1159 b1175 (by norm_num) (by norm_num)

def e1177 : ℝ := e1147 ^ 2
lemma b1177 : Encl e1177 (562288707641 / 1000000000000 : ℝ) (112457741529 / 200000000000 : ℝ) := by
  exact Encl.pow b1147 (by norm_num) 2 (by norm_num) (by norm_num)

def e1178 : ℝ := e5 - e1177
lemma b1178 : Encl e1178 (87542258471 / 200000000000 : ℝ) (437711292359 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1177 (by norm_num) (by norm_num)

def e1179 : ℝ := Real.sqrt e1178
lemma b1179 : Encl e1179 (661597530493 / 1000000000000 : ℝ) (661597530497 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1178 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1180 : ℝ := e5 + e1179
lemma b1180 : Encl e1180 (1661597530493 / 1000000000000 : ℝ) (1661597530497 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1179 (by norm_num) (by norm_num)

def e1181 : ℝ := e1147 / e1180
lemma b1181 : Encl e1181 (451288059493 / 1000000000000 : ℝ) (56411007437 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1147 b1180 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1182 : ℝ := e1181 ^ 2
lemma b1182 : Encl e1182 (19888761 / 97656250 : ℝ) (50915228161 / 250000000000 : ℝ) := by
  exact Encl.pow b1181 (by norm_num) 2 (by norm_num) (by norm_num)

def e1183 : ℝ := e5 + e1182
lemma b1183 : Encl e1183 (117545011 / 97656250 : ℝ) (300915228161 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1182 (by norm_num) (by norm_num)

def e1184 : ℝ := Real.sqrt e1183
lemma b1184 : Encl e1184 (1097114812879 / 1000000000000 : ℝ) (548557406441 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1183 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1185 : ℝ := e5 + e1184
lemma b1185 : Encl e1185 (2097114812879 / 1000000000000 : ℝ) (1048557406441 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1184 (by norm_num) (by norm_num)

def e1186 : ℝ := e1181 / e1185
lemma b1186 : Encl e1186 (43038946339 / 200000000000 : ℝ) (107597365849 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1181 b1185 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1187 : ℝ := Real.arcsin e1147
lemma b1187 : Encl e1187 (211962280501 / 250000000000 : ℝ) (847849122017 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e1147) (a := (43038946339 / 200000000000 : ℝ)) (b := (107597365849 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (749859125197 / 1000000000000 : ℝ) by norm_num).trans b1147.1
        exact b1147.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1147) (43038946339 / 200000000000 : ℝ) (107597365849 / 500000000000 : ℝ) from b1186) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1188 : ℝ := e59 * e1187
lemma b1188 : Encl e1188 (216201526111 / 500000000000 : ℝ) (432403052229 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1187 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1189 : ℝ := e61 * e1147
lemma b1189 : Encl e1189 (183715485673 / 500000000000 : ℝ) (91857742837 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1147 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1190 : ℝ := e1189 * e1179
lemma b1190 : Encl e1190 (243091423269 / 1000000000000 : ℝ) (30386427909 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1189 b1179 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1191 : ℝ := e1188 - e1190
lemma b1191 : Encl e1191 (3786232579 / 20000000000 : ℝ) (1183197681 / 6250000000 : ℝ) := by
  exact Encl.sub b1188 b1190 (by norm_num) (by norm_num)

def e1192 : ℝ := e43 * e1179
lemma b1192 : Encl e1192 (661597530493 / 20000000000 : ℝ) (661597530497 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1179 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1193 : ℝ := e1147 / e1192
lemma b1193 : Encl e1193 (11334067777 / 500000000000 : ℝ) (4533627111 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1147 b1192 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1194 : ℝ := e1191 - e1193
lemma b1194 : Encl e1194 (33328698679 / 200000000000 : ℝ) (83321746703 / 500000000000 : ℝ) := by
  exact Encl.sub b1191 b1193 (by norm_num) (by norm_num)

def e1195 : ℝ := e5 + e1163
lemma b1195 : Encl e1195 (968348526151 / 500000000000 : ℝ) (1936697052303 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1163 (by norm_num) (by norm_num)

def e1196 : ℝ := e1146 / e1195
lemma b1196 : Encl e1196 (3615855917 / 20000000000 : ℝ) (45198198963 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1146 b1195 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1197 : ℝ := e1196 ^ 2
lemma b1197 : Encl e1197 (32686035031 / 1000000000000 : ℝ) (4085754379 / 125000000000 : ℝ) := by
  exact Encl.pow b1196 (by norm_num) 2 (by norm_num) (by norm_num)

def e1198 : ℝ := e5 + e1197
lemma b1198 : Encl e1198 (1032686035031 / 1000000000000 : ℝ) (129085754379 / 125000000000 : ℝ) := by
  exact Encl.add b5 b1197 (by norm_num) (by norm_num)

def e1199 : ℝ := Real.sqrt e1198
lemma b1199 : Encl e1199 (31756612793 / 31250000000 : ℝ) (1016211609377 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1198 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1200 : ℝ := e5 + e1199
lemma b1200 : Encl e1200 (63006612793 / 31250000000 : ℝ) (2016211609377 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1199 (by norm_num) (by norm_num)

def e1201 : ℝ := e1196 / e1200
lemma b1201 : Encl e1201 (89669554033 / 1000000000000 : ℝ) (17933910807 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1196 b1200 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1202 : ℝ := Real.arcsin e1146
lemma b1202 : Encl e1202 (8943037367 / 25000000000 : ℝ) (357721494689 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e1146) (a := (89669554033 / 1000000000000 : ℝ)) (b := (17933910807 / 200000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (175070437401 / 500000000000 : ℝ) by norm_num).trans b1146.1
        exact b1146.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1146) (89669554033 / 1000000000000 : ℝ) (17933910807 / 200000000000 : ℝ) from b1201) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1203 : ℝ := e59 * e1202
lemma b1203 : Encl e1203 (91218981143 / 500000000000 : ℝ) (45609490573 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1202 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1204 : ℝ := e61 * e1146
lemma b1204 : Encl e1204 (42892257163 / 250000000000 : ℝ) (85784514327 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1146 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1205 : ℝ := e1204 * e1163
lemma b1205 : Encl e1205 (40177050851 / 250000000000 : ℝ) (160708203407 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1204 b1163 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1206 : ℝ := e1203 - e1205
lemma b1206 : Encl e1206 (21729758879 / 1000000000000 : ℝ) (2716219861 / 125000000000 : ℝ) := by
  exact Encl.sub b1203 b1205 (by norm_num) (by norm_num)

def e1207 : ℝ := e43 * e1163
lemma b1207 : Encl e1207 (468348526151 / 10000000000 : ℝ) (936697052303 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1163 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1208 : ℝ := e1146 / e1207
lemma b1208 : Encl e1208 (3738037543 / 500000000000 : ℝ) (7476075087 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1146 b1207 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1209 : ℝ := e1206 - e1208
lemma b1209 : Encl e1209 (890855237 / 62500000000 : ℝ) (7126841901 / 500000000000 : ℝ) := by
  exact Encl.sub b1206 b1208 (by norm_num) (by norm_num)

def e1210 : ℝ := e1194 - e1209
lemma b1210 : Encl e1210 (152389809593 / 1000000000000 : ℝ) (76194904807 / 500000000000 : ℝ) := by
  exact Encl.sub b1194 b1209 (by norm_num) (by norm_num)

def e1211 : ℝ := e1210 / e1145
lemma b1211 : Encl e1211 (138536190539 / 1000000000000 : ℝ) (138536190559 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1210 b1145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1212 : ℝ := e1176 + e1211
lemma b1212 : Encl e1212 (-292678398691 / 1000000000000 : ℝ) (-292678398653 / 1000000000000 : ℝ) := by
  exact Encl.add b1176 b1211 (by norm_num) (by norm_num)

def e1213 : ℝ := e1147 + e4
lemma b1213 : Encl e1213 (1739602443807 / 1000000000000 : ℝ) (173960244381 / 100000000000 : ℝ) := by
  exact Encl.add b1147 b4 (by norm_num) (by norm_num)

def e1214 : ℝ := e1213 / e23
lemma b1214 : Encl e1214 (869801221903 / 1000000000000 : ℝ) (173960244381 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1213 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1215 : ℝ := e1147 / e1145
lemma b1215 : Encl e1215 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1147 b1145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1216 : ℝ := e89 * e1215
lemma b1216 : Encl e1216 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1215 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1217 : ℝ := e1215 ^ 2
lemma b1217 : Encl e1217 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b1215 (by norm_num) 2 (by norm_num) (by norm_num)

def e1218 : ℝ := e91 * e1217
lemma b1218 : Encl e1218 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1217 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1219 : ℝ := e5 + e1218
lemma b1219 : Encl e1219 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1218 (by norm_num) (by norm_num)

def e1220 : ℝ := Real.sqrt e1219
lemma b1220 : Encl e1220 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1219 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1221 : ℝ := e1216 * e1220
lemma b1221 : Encl e1221 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1216 b1220 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1222 : ℝ := e97 * e1217
lemma b1222 : Encl e1222 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1217 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1223 : ℝ := e1221 - e1222
lemma b1223 : Encl e1223 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b1221 b1222 (by norm_num) (by norm_num)

def e1224 : ℝ := e1214 * e1223
lemma b1224 : Encl e1224 (296467446973 / 500000000000 : ℝ) (592934893969 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1214 b1223 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1225 : ℝ := e1214 / e1145
lemma b1225 : Encl e1225 (197682095887 / 250000000000 : ℝ) (15814567671 / 20000000000 : ℝ) := by
  exact Encl.div_nonneg b1214 b1145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1226 : ℝ := e89 * e1225
lemma b1226 : Encl e1226 (1401529568439 / 1000000000000 : ℝ) (350382392111 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1225 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1227 : ℝ := e1225 ^ 2
lemma b1227 : Encl e1227 (156312844137 / 250000000000 : ℝ) (78156422069 / 125000000000 : ℝ) := by
  exact Encl.pow b1225 (by norm_num) 2 (by norm_num) (by norm_num)

def e1228 : ℝ := e91 * e1227
lemma b1228 : Encl e1228 (245535641401 / 500000000000 : ℝ) (491071282807 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1227 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1229 : ℝ := e5 + e1228
lemma b1229 : Encl e1229 (745535641401 / 500000000000 : ℝ) (1491071282807 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1228 (by norm_num) (by norm_num)

def e1230 : ℝ := Real.sqrt e1229
lemma b1230 : Encl e1230 (61054714863 / 50000000000 : ℝ) (1221094297263 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1229 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1231 : ℝ := e1226 * e1230
lemma b1231 : Encl e1231 (855699881731 / 500000000000 : ℝ) (1711399763473 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1226 b1230 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1232 : ℝ := e97 * e1227
lemma b1232 : Encl e1232 (245535641401 / 250000000000 : ℝ) (245535641403 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1227 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1233 : ℝ := e1231 - e1232
lemma b1233 : Encl e1233 (14585143957 / 20000000000 : ℝ) (729257197869 / 1000000000000 : ℝ) := by
  exact Encl.sub b1231 b1232 (by norm_num) (by norm_num)

def e1234 : ℝ := e1147 * e1233
lemma b1234 : Encl e1234 (546840164423 / 1000000000000 : ℝ) (13671004111 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b1147 b1233 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1235 : ℝ := e1224 - e1234
lemma b1235 : Encl e1235 (23047364753 / 500000000000 : ℝ) (23047364773 / 500000000000 : ℝ) := by
  exact Encl.sub b1224 b1234 (by norm_num) (by norm_num)

def e1236 : ℝ := e1214 ^ 2
lemma b1236 : Encl e1236 (756554165623 / 1000000000000 : ℝ) (189138541407 / 250000000000 : ℝ) := by
  exact Encl.pow b1214 (by norm_num) 2 (by norm_num) (by norm_num)

def e1237 : ℝ := e8 * e1236
lemma b1237 : Encl e1237 (74142308231 / 100000000000 : ℝ) (185355770579 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1236 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1238 : ℝ := e5 - e1237
lemma b1238 : Encl e1238 (64644229421 / 250000000000 : ℝ) (25857691769 / 100000000000 : ℝ) := by
  exact Encl.sub b5 b1237 (by norm_num) (by norm_num)

def e1239 : ℝ := e5 - e1236
lemma b1239 : Encl e1239 (60861458593 / 250000000000 : ℝ) (243445834377 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1236 (by norm_num) (by norm_num)

def e1240 : ℝ := Real.sqrt e1239
lemma b1240 : Encl e1240 (493402304789 / 1000000000000 : ℝ) (98680460959 / 200000000000 : ℝ) := by
  exact Encl.sqrt b1239 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1241 : ℝ := e1238 / e1240
lemma b1241 : Encl e1241 (65508641521 / 125000000000 : ℝ) (131017283047 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1238 b1240 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1242 : ℝ := e5 - e1241
lemma b1242 : Encl e1242 (118982716953 / 250000000000 : ℝ) (59491358479 / 125000000000 : ℝ) := by
  exact Encl.sub b5 b1241 (by norm_num) (by norm_num)

def e1243 : ℝ := e8 * e1177
lemma b1243 : Encl e1243 (34440183343 / 62500000000 : ℝ) (551042933493 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1177 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1244 : ℝ := e5 - e1243
lemma b1244 : Encl e1244 (448957066507 / 1000000000000 : ℝ) (28059816657 / 62500000000 : ℝ) := by
  exact Encl.sub b5 b1243 (by norm_num) (by norm_num)

def e1245 : ℝ := e1244 / e1179
lemma b1245 : Encl e1245 (135719087757 / 200000000000 : ℝ) (339297719399 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1244 b1179 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1246 : ℝ := e5 - e1245
lemma b1246 : Encl e1246 (160702280601 / 500000000000 : ℝ) (64280912243 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b1245 (by norm_num) (by norm_num)

def e1247 : ℝ := e1242 - e1246
lemma b1247 : Encl e1247 (154526306597 / 1000000000000 : ℝ) (15452630663 / 100000000000 : ℝ) := by
  exact Encl.sub b1242 b1246 (by norm_num) (by norm_num)

def e1248 : ℝ := e1235 * e1247
lemma b1248 : Encl e1248 (445178019 / 62500000000 : ℝ) (890356039 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1235 b1247 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1249 : ℝ := e1233 - e1223
lemma b1249 : Encl e1249 (23783542011 / 500000000000 : ℝ) (1486471377 / 31250000000 : ℝ) := by
  exact Encl.sub b1233 b1223 (by norm_num) (by norm_num)

def e1250 : ℝ := e5 + e1240
lemma b1250 : Encl e1250 (1493402304789 / 1000000000000 : ℝ) (298680460959 / 200000000000 : ℝ) := by
  exact Encl.add b5 b1240 (by norm_num) (by norm_num)

def e1251 : ℝ := e1214 / e1250
lemma b1251 : Encl e1251 (582429275159 / 1000000000000 : ℝ) (582429275163 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1214 b1250 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1252 : ℝ := e1251 ^ 2
lemma b1252 : Encl e1252 (169611930281 / 500000000000 : ℝ) (339223860567 / 1000000000000 : ℝ) := by
  exact Encl.pow b1251 (by norm_num) 2 (by norm_num) (by norm_num)

def e1253 : ℝ := e5 + e1252
lemma b1253 : Encl e1253 (669611930281 / 500000000000 : ℝ) (1339223860567 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1252 (by norm_num) (by norm_num)

def e1254 : ℝ := Real.sqrt e1253
lemma b1254 : Encl e1254 (36164012517 / 31250000000 : ℝ) (1157248400547 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1253 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1255 : ℝ := e5 + e1254
lemma b1255 : Encl e1255 (67414012517 / 31250000000 : ℝ) (2157248400547 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1254 (by norm_num) (by norm_num)

def e1256 : ℝ := e1251 / e1255
lemma b1256 : Encl e1256 (269987116463 / 1000000000000 : ℝ) (134993558233 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1251 b1255 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1257 : ℝ := Real.arcsin e1214
lemma b1257 : Encl e1257 (1054799305119 / 1000000000000 : ℝ) (263699826283 / 250000000000 : ℝ) := by
  apply Encl.arcsin (z := e1214) (a := (269987116463 / 1000000000000 : ℝ)) (b := (134993558233 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (869801221903 / 1000000000000 : ℝ) by norm_num).trans b1214.1
        exact b1214.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1214) (269987116463 / 1000000000000 : ℝ) (134993558233 / 500000000000 : ℝ) from b1256) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1258 : ℝ := e59 * e1257
lemma b1258 : Encl e1258 (53794764561 / 100000000000 : ℝ) (268973822809 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1257 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1259 : ℝ := e61 * e1214
lemma b1259 : Encl e1259 (106550649683 / 250000000000 : ℝ) (213101299367 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1214 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1260 : ℝ := e1259 * e1240
lemma b1260 : Encl e1260 (210289344521 / 1000000000000 : ℝ) (8411573781 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b1259 b1240 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1261 : ℝ := e1258 - e1260
lemma b1261 : Encl e1261 (65531660217 / 200000000000 : ℝ) (327658301097 / 1000000000000 : ℝ) := by
  exact Encl.sub b1258 b1260 (by norm_num) (by norm_num)

def e1262 : ℝ := e43 * e1240
lemma b1262 : Encl e1262 (493402304789 / 20000000000 : ℝ) (98680460959 / 4000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1240 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1263 : ℝ := e1214 / e1262
lemma b1263 : Encl e1263 (35257282483 / 1000000000000 : ℝ) (8814320621 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1214 b1262 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1264 : ℝ := e1261 - e1263
lemma b1264 : Encl e1264 (292401018601 / 1000000000000 : ℝ) (146200509307 / 500000000000 : ℝ) := by
  exact Encl.sub b1261 b1263 (by norm_num) (by norm_num)

def e1265 : ℝ := e1264 - e1194
lemma b1265 : Encl e1265 (25151505039 / 200000000000 : ℝ) (125757525219 / 1000000000000 : ℝ) := by
  exact Encl.sub b1264 b1194 (by norm_num) (by norm_num)

def e1266 : ℝ := e1249 * e1265
lemma b1266 : Encl e1266 (5981918767 / 1000000000000 : ℝ) (2990959387 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1249 b1265 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1267 : ℝ := e1248 + e1266
lemma b1267 : Encl e1267 (13104767071 / 1000000000000 : ℝ) (6552383543 / 500000000000 : ℝ) := by
  exact Encl.add b1248 b1266 (by norm_num) (by norm_num)

def e1268 : ℝ := e1214 - e1147
lemma b1268 : Encl e1268 (1874095261 / 15625000000 : ℝ) (29985524177 / 250000000000 : ℝ) := by
  exact Encl.sub b1214 b1147 (by norm_num) (by norm_num)

def e1269 : ℝ := e1267 / e1268
lemma b1269 : Encl e1269 (109259112777 / 1000000000000 : ℝ) (109259112907 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1267 b1268 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1270 : ℝ := e1212 + e1269
lemma b1270 : Encl e1270 (-91709642957 / 500000000000 : ℝ) (-91709642873 / 500000000000 : ℝ) := by
  exact Encl.add b1212 b1269 (by norm_num) (by norm_num)

def e1271 : ℝ := e4 * e1233
lemma b1271 : Encl e1271 (9022217989 / 12500000000 : ℝ) (36088871957 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b1233 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1272 : ℝ := e4 / e1145
lemma b1272 : Encl e1272 (899766653281 / 1000000000000 : ℝ) (899766653283 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b1145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1273 : ℝ := e89 * e1272
lemma b1273 : Encl e1273 (1594794869523 / 1000000000000 : ℝ) (1594794869529 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1272 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1274 : ℝ := e1272 ^ 2
lemma b1274 : Encl e1274 (202395007589 / 250000000000 : ℝ) (809580030361 / 1000000000000 : ℝ) := by
  exact Encl.pow b1272 (by norm_num) 2 (by norm_num) (by norm_num)

def e1275 : ℝ := e91 * e1274
lemma b1275 : Encl e1275 (158960667241 / 250000000000 : ℝ) (63584266897 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1274 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1276 : ℝ := e5 + e1275
lemma b1276 : Encl e1276 (408960667241 / 250000000000 : ℝ) (163584266897 / 100000000000 : ℝ) := by
  exact Encl.add b5 b1275 (by norm_num) (by norm_num)

def e1277 : ℝ := Real.sqrt e1276
lemma b1277 : Encl e1277 (39968770389 / 31250000000 : ℝ) (1279000652451 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1276 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1278 : ℝ := e1273 * e1277
lemma b1278 : Encl e1278 (25496795983 / 12500000000 : ℝ) (1019871839327 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1273 b1277 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1279 : ℝ := e97 * e1274
lemma b1279 : Encl e1279 (158960667241 / 125000000000 : ℝ) (635842668969 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1274 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1280 : ℝ := e1278 - e1279
lemma b1280 : Encl e1280 (384029170351 / 500000000000 : ℝ) (384029170363 / 500000000000 : ℝ) := by
  exact Encl.sub b1278 b1279 (by norm_num) (by norm_num)

def e1281 : ℝ := e1214 * e1280
lemma b1281 : Encl e1281 (133611616647 / 200000000000 : ℝ) (334029041629 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1214 b1280 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1282 : ℝ := e1271 - e1281
lemma b1282 : Encl e1282 (26859677931 / 500000000000 : ℝ) (10743871181 / 200000000000 : ℝ) := by
  exact Encl.sub b1271 b1281 (by norm_num) (by norm_num)

def e1283 : ℝ := e165 - e1242
lemma b1283 : Encl e1283 (244069132143 / 1000000000000 : ℝ) (30508641527 / 125000000000 : ℝ) := by
  exact Encl.sub b165 b1242 (by norm_num) (by norm_num)

def e1284 : ℝ := e1282 * e1283
lemma b1284 : Encl e1284 (3277809141 / 250000000000 : ℝ) (13111236579 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1282 b1283 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1285 : ℝ := e1280 - e1233
lemma b1285 : Encl e1285 (38801142833 / 1000000000000 : ℝ) (9700285719 / 250000000000 : ℝ) := by
  exact Encl.sub b1280 b1233 (by norm_num) (by norm_num)

def e1286 : ℝ := e183 - e1264
lemma b1286 : Encl e1286 (113875875449 / 500000000000 : ℝ) (113875875521 / 500000000000 : ℝ) := by
  exact Encl.sub b183 b1264 (by norm_num) (by norm_num)

def e1287 : ℝ := e1285 * e1286
lemma b1287 : Encl e1287 (8837028217 / 1000000000000 : ℝ) (8837028233 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1285 b1286 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1288 : ℝ := e1284 + e1287
lemma b1288 : Encl e1288 (21948264781 / 1000000000000 : ℝ) (5487066203 / 250000000000 : ℝ) := by
  exact Encl.add b1284 b1287 (by norm_num) (by norm_num)

def e1289 : ℝ := e4 - e1214
lemma b1289 : Encl e1289 (23988419341 / 200000000000 : ℝ) (29985524177 / 250000000000 : ℝ) := by
  exact Encl.sub b4 b1214 (by norm_num) (by norm_num)

def e1290 : ℝ := e1288 / e1289
lemma b1290 : Encl e1290 (91495252223 / 500000000000 : ℝ) (18299050471 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1288 b1289 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1291 : ℝ := e1270 + e1290
lemma b1291 : Encl e1291 (-107195367 / 250000000000 : ℝ) (-107195259 / 250000000000 : ℝ) := by
  exact Encl.add b1270 b1290 (by norm_num) (by norm_num)

def e1292 : ℝ := e924 / e1145
lemma b1292 : Encl e1292 (872727272727 / 1000000000000 : ℝ) (109090909091 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b1145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1293 : ℝ := min e7 e1292
lemma b1293 : Encl e1293 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b1292 (by norm_num) (by norm_num)

def e1294 : ℝ := e1293 - e5
lemma b1294 : Encl e1294 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b1293 b5 (by norm_num) (by norm_num)

def e1295 : ℝ := e23 * e1145
lemma b1295 : Encl e1295 (11 / 5 : ℝ) (11 / 5 : ℝ) := by
  exact Encl.mul_nonneg b23 b1145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1296 : ℝ := e1295 * e1156
lemma b1296 : Encl e1296 (1696266388467 / 1000000000000 : ℝ) (169626638847 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b1295 b1156 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1297 : ℝ := e1296 / e0
lemma b1297 : Encl e1297 (10798767221 / 20000000000 : ℝ) (134984590263 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1296 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1298 : ℝ := e1294 + e1297
lemma b1298 : Encl e1298 (110814237433 / 500000000000 : ℝ) (221628474869 / 1000000000000 : ℝ) := by
  exact Encl.add b1294 b1297 (by norm_num) (by norm_num)

def e1299 : ℝ := e23 * e1150
lemma b1299 : Encl e1299 (121 / 50 : ℝ) (121 / 50 : ℝ) := by
  exact Encl.mul_nonneg b23 b1150 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1300 : ℝ := e1299 * e1156
lemma b1300 : Encl e1300 (1865893027313 / 1000000000000 : ℝ) (1865893027317 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1299 b1156 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1301 : ℝ := e0 + e1300
lemma b1301 : Encl e1301 (2503742840451 / 500000000000 : ℝ) (5007485680907 / 1000000000000 : ℝ) := by
  exact Encl.add b0 b1300 (by norm_num) (by norm_num)

def e1302 : ℝ := Real.sqrt e1301
lemma b1302 : Encl e1302 (69929412519 / 31250000000 : ℝ) (223774120061 / 100000000000 : ℝ) := by
  exact Encl.sqrt b1301 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1303 : ℝ := e932 * e1302
lemma b1303 : Encl e1303 (1424590293747 / 1000000000000 : ℝ) (1424590293751 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b1302 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1304 : ℝ := e1145 ^ 3
lemma b1304 : Encl e1304 (1331 / 1000 : ℝ) (1331 / 1000 : ℝ) := by
  exact Encl.pow b1145 (by norm_num) 3 (by norm_num) (by norm_num)

def e1305 : ℝ := e939 * e1304
lemma b1305 : Encl e1305 (89177 / 500000 : ℝ) (89177 / 500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b1304 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1306 : ℝ := min e1305 e941
lemma b1306 : Encl e1306 (89177 / 500000 : ℝ) (89177 / 500000 : ℝ) := by
  exact Encl.min b1305 b941 (by norm_num) (by norm_num)

def e1307 : ℝ := e23 * e1298
lemma b1307 : Encl e1307 (110814237433 / 250000000000 : ℝ) (221628474869 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1298 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1308 : ℝ := e944 * e1306
lemma b1308 : Encl e1308 (267531 / 250000 : ℝ) (267531 / 250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b1306 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1309 : ℝ := e1303 ^ 2
lemma b1309 : Encl e1309 (1014728752519 / 500000000000 : ℝ) (40589150101 / 20000000000 : ℝ) := by
  exact Encl.pow b1303 (by norm_num) 2 (by norm_num) (by norm_num)

def e1310 : ℝ := e1308 * e1309
lemma b1310 : Encl e1310 (2171771183121 / 1000000000000 : ℝ) (434354236627 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1308 b1309 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1311 : ℝ := e1310 * e1298
lemma b1311 : Encl e1311 (481326335073 / 1000000000000 : ℝ) (481326335083 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1310 b1298 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1312 : ℝ := e1311 / e9
lemma b1312 : Encl e1312 (85951131263 / 50000000000 : ℝ) (1719022625297 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1311 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1313 : ℝ := e5 + e1312
lemma b1313 : Encl e1313 (135951131263 / 50000000000 : ℝ) (2719022625297 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1312 (by norm_num) (by norm_num)

def e1314 : ℝ := Real.sqrt e1313
lemma b1314 : Encl e1314 (824472956691 / 500000000000 : ℝ) (824472956697 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1313 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1315 : ℝ := e5 + e1314
lemma b1315 : Encl e1315 (1324472956691 / 500000000000 : ℝ) (1324472956697 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1314 (by norm_num) (by norm_num)

def e1316 : ℝ := e1307 / e1315
lemma b1316 : Encl e1316 (167333333417 / 1000000000000 : ℝ) (167333333421 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1307 b1315 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1317 : ℝ := e1306 * e954
lemma b1317 : Encl e1317 (825868197 / 500000000000 : ℝ) (825868197 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1306 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1318 : ℝ := e1298 - e1316
lemma b1318 : Encl e1318 (10859028289 / 200000000000 : ℝ) (13573785363 / 250000000000 : ℝ) := by
  exact Encl.sub b1298 b1316 (by norm_num) (by norm_num)

def e1319 : ℝ := e1318 / e1303
lemma b1319 : Encl e1319 (1905640579 / 50000000000 : ℝ) (19056405793 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1318 b1303 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1320 : ℝ := e1319 ^ 2
lemma b1320 : Encl e1320 (726293203 / 500000000000 : ℝ) (1452586407 / 1000000000000 : ℝ) := by
  exact Encl.pow b1319 (by norm_num) 2 (by norm_num) (by norm_num)

def e1321 : ℝ := e9 * e1320
lemma b1321 : Encl e1321 (406724193 / 1000000000000 : ℝ) (203362097 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1320 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1322 : ℝ := e1316 ^ 3
lemma b1322 : Encl e1322 (468540771 / 100000000000 : ℝ) (146418991 / 31250000000 : ℝ) := by
  exact Encl.pow b1316 (by norm_num) 3 (by norm_num) (by norm_num)

def e1323 : ℝ := e1306 * e1322
lemma b1323 : Encl e1323 (417830603 / 500000000000 : ℝ) (104457651 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1306 b1322 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1324 : ℝ := e1321 + e1323
lemma b1324 : Encl e1324 (1242385399 / 1000000000000 : ℝ) (621192701 / 500000000000 : ℝ) := by
  exact Encl.add b1321 b1323 (by norm_num) (by norm_num)

def e1325 : ℝ := min e1317 e1324
lemma b1325 : Encl e1325 (1242385399 / 1000000000000 : ℝ) (621192701 / 500000000000 : ℝ) := by
  exact Encl.min b1317 b1324 (by norm_num) (by norm_num)

def e1326 : ℝ := (57 / 50 : ℝ)
lemma b1326 : Encl e1326 (57 / 50 : ℝ) (57 / 50 : ℝ) := by
  exact Encl.exact (57 / 50 : ℝ)

def e1327 : ℝ := e1326 / e0
lemma b1327 : Encl e1327 (362873270249 / 1000000000000 : ℝ) (1451493081 / 4000000000 : ℝ) := by
  exact Encl.div_nonneg b1326 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1328 : ℝ := e1326 * e7
lemma b1328 : Encl e1328 (3108506919 / 4000000000 : ℝ) (97140841219 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1326 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1329 : ℝ := e8 * e1326
lemma b1329 : Encl e1329 (2793 / 2500 : ℝ) (2793 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b1326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1330 : ℝ := e1329 / e0
lemma b1330 : Encl e1330 (88903951211 / 250000000000 : ℝ) (71123160969 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1329 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1331 : ℝ := e1326 ^ 2
lemma b1331 : Encl e1331 (3249 / 2500 : ℝ) (3249 / 2500 : ℝ) := by
  exact Encl.pow b1326 (by norm_num) 2 (by norm_num) (by norm_num)

def e1332 : ℝ := e17 * e1331
lemma b1332 : Encl e1332 (3249 / 625 : ℝ) (3249 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b1331 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1333 : ℝ := e1332 / e0
lemma b1333 : Encl e1333 (1654702112337 / 1000000000000 : ℝ) (827351056169 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1332 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1334 : ℝ := e5 + e1333
lemma b1334 : Encl e1334 (2654702112337 / 1000000000000 : ℝ) (1327351056169 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1333 (by norm_num) (by norm_num)

def e1335 : ℝ := Real.sqrt e1334
lemma b1335 : Encl e1335 (814662830921 / 500000000000 : ℝ) (1629325661843 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1334 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1336 : ℝ := e5 + e1335
lemma b1336 : Encl e1336 (1314662830921 / 500000000000 : ℝ) (2629325661843 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1335 (by norm_num) (by norm_num)

def e1337 : ℝ := e23 / e1336
lemma b1337 : Encl e1337 (760651306539 / 1000000000000 : ℝ) (760651306541 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b1336 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1338 : ℝ := e9 * e1337
lemma b1338 : Encl e1338 (21298236583 / 100000000000 : ℝ) (26622795729 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1339 : ℝ := e1330 + e1338
lemma b1339 : Encl e1339 (284299085337 / 500000000000 : ℝ) (568598170677 / 1000000000000 : ℝ) := by
  exact Encl.add b1330 b1338 (by norm_num) (by norm_num)

def e1340 : ℝ := e1339 - e5
lemma b1340 : Encl e1340 (-215700914663 / 500000000000 : ℝ) (-431401829323 / 1000000000000 : ℝ) := by
  exact Encl.sub b1339 b5 (by norm_num) (by norm_num)

def e1341 : ℝ := e0 / e1331
lemma b1341 : Encl e1341 (1208676767309 / 500000000000 : ℝ) (2417353534619 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b1331 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1342 : ℝ := e1327 ^ 2
lemma b1342 : Encl e1342 (131677010261 / 1000000000000 : ℝ) (65838505131 / 500000000000 : ℝ) := by
  exact Encl.pow b1327 (by norm_num) 2 (by norm_num) (by norm_num)

def e1343 : ℝ := e5 - e1342
lemma b1343 : Encl e1343 (434161494869 / 500000000000 : ℝ) (868322989739 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1342 (by norm_num) (by norm_num)

def e1344 : ℝ := Real.sqrt e1343
lemma b1344 : Encl e1344 (186367699963 / 200000000000 : ℝ) (116479812477 / 125000000000 : ℝ) := by
  exact Encl.sqrt b1343 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1345 : ℝ := e29 - e1344
lemma b1345 : Encl e1345 (-5303436663 / 20000000000 : ℝ) (-66292958287 / 250000000000 : ℝ) := by
  exact Encl.sub b29 b1344 (by norm_num) (by norm_num)

def e1346 : ℝ := e1344 ^ 3
lemma b1346 : Encl e1346 (809136792111 / 1000000000000 : ℝ) (161827358423 / 200000000000 : ℝ) := by
  exact Encl.pow b1344 (by norm_num) 3 (by norm_num) (by norm_num)

def e1347 : ℝ := e1346 / e35
lemma b1347 : Encl e1347 (269712264037 / 1000000000000 : ℝ) (269712264039 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1346 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1348 : ℝ := e1345 + e1347
lemma b1348 : Encl e1348 (4540430887 / 1000000000000 : ℝ) (4540430891 / 1000000000000 : ℝ) := by
  exact Encl.add b1345 b1347 (by norm_num) (by norm_num)

def e1349 : ℝ := e8 * e1348
lemma b1349 : Encl e1349 (4449622269 / 1000000000000 : ℝ) (2224811137 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1348 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1350 : ℝ := e1342 / e1344
lemma b1350 : Encl e1350 (275993813 / 1953125000 : ℝ) (141308832259 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1342 b1344 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1351 : ℝ := e1350 - e23
lemma b1351 : Encl e1351 (-3630256187 / 1953125000 : ℝ) (-1858691167741 / 1000000000000 : ℝ) := by
  exact Encl.sub b1350 b23 (by norm_num) (by norm_num)

def e1352 : ℝ := e23 * e1344
lemma b1352 : Encl e1352 (186367699963 / 100000000000 : ℝ) (116479812477 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1344 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1353 : ℝ := e1351 + e1352
lemma b1353 : Encl e1353 (2492915943 / 500000000000 : ℝ) (4985831891 / 1000000000000 : ℝ) := by
  exact Encl.add b1351 b1352 (by norm_num) (by norm_num)

def e1354 : ℝ := e1353 / e43
lemma b1354 : Encl e1354 (99716637 / 1000000000000 : ℝ) (49858319 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1353 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1355 : ℝ := e1349 - e1354
lemma b1355 : Encl e1355 (4349905631 / 1000000000000 : ℝ) (4349905637 / 1000000000000 : ℝ) := by
  exact Encl.sub b1349 b1354 (by norm_num) (by norm_num)

def e1356 : ℝ := e1341 * e1355
lemma b1356 : Encl e1356 (1314407469 / 125000000000 : ℝ) (10515259767 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1341 b1355 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1357 : ℝ := e1340 + e1356
lemma b1357 : Encl e1357 (-210443284787 / 500000000000 : ℝ) (-105221642389 / 250000000000 : ℝ) := by
  exact Encl.add b1340 b1356 (by norm_num) (by norm_num)

def e1358 : ℝ := e1328 ^ 2
lemma b1358 : Encl e1358 (603925954091 / 1000000000000 : ℝ) (37745372131 / 62500000000 : ℝ) := by
  exact Encl.pow b1328 (by norm_num) 2 (by norm_num) (by norm_num)

def e1359 : ℝ := e5 - e1358
lemma b1359 : Encl e1359 (24754627869 / 62500000000 : ℝ) (396074045909 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1358 (by norm_num) (by norm_num)

def e1360 : ℝ := Real.sqrt e1359
lemma b1360 : Encl e1360 (157336034871 / 250000000000 : ℝ) (629344139489 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1359 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1361 : ℝ := e5 + e1360
lemma b1361 : Encl e1361 (407336034871 / 250000000000 : ℝ) (1629344139489 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1360 (by norm_num) (by norm_num)

def e1362 : ℝ := e1328 / e1361
lemma b1362 : Encl e1362 (238478388609 / 500000000000 : ℝ) (476956777221 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1328 b1361 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1363 : ℝ := e1362 ^ 2
lemma b1363 : Encl e1363 (113743883667 / 500000000000 : ℝ) (113743883669 / 500000000000 : ℝ) := by
  exact Encl.pow b1362 (by norm_num) 2 (by norm_num) (by norm_num)

def e1364 : ℝ := e5 + e1363
lemma b1364 : Encl e1364 (613743883667 / 500000000000 : ℝ) (613743883669 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1363 (by norm_num) (by norm_num)

def e1365 : ℝ := Real.sqrt e1364
lemma b1365 : Encl e1365 (1107920469769 / 1000000000000 : ℝ) (276980117443 / 250000000000 : ℝ) := by
  exact Encl.sqrt b1364 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1366 : ℝ := e5 + e1365
lemma b1366 : Encl e1366 (2107920469769 / 1000000000000 : ℝ) (526980117443 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1365 (by norm_num) (by norm_num)

def e1367 : ℝ := e1362 / e1366
lemma b1367 : Encl e1367 (226268867377 / 1000000000000 : ℝ) (11313443369 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b1362 b1366 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1368 : ℝ := Real.arcsin e1328
lemma b1368 : Encl e1368 (890087359603 / 1000000000000 : ℝ) (6953807497 / 7812500000 : ℝ) := by
  apply Encl.arcsin (z := e1328) (a := (226268867377 / 1000000000000 : ℝ)) (b := (11313443369 / 50000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (3108506919 / 4000000000 : ℝ) by norm_num).trans b1328.1
        exact b1328.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1328) (226268867377 / 1000000000000 : ℝ) (11313443369 / 50000000000 : ℝ) from b1367) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1369 : ℝ := e59 * e1368
lemma b1369 : Encl e1369 (453944553397 / 1000000000000 : ℝ) (90788910681 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1368 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1370 : ℝ := e61 * e1328
lemma b1370 : Encl e1370 (380792097577 / 1000000000000 : ℝ) (380792097579 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1328 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1371 : ℝ := e1370 * e1360
lemma b1371 : Encl e1371 (239649274971 / 1000000000000 : ℝ) (7489039843 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b1370 b1360 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1372 : ℝ := e1369 - e1371
lemma b1372 : Encl e1372 (214295278421 / 1000000000000 : ℝ) (107147639217 / 500000000000 : ℝ) := by
  exact Encl.sub b1369 b1371 (by norm_num) (by norm_num)

def e1373 : ℝ := e43 * e1360
lemma b1373 : Encl e1373 (157336034871 / 5000000000 : ℝ) (629344139489 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1360 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1374 : ℝ := e1328 / e1373
lemma b1374 : Encl e1374 (24696399981 / 1000000000000 : ℝ) (24696399983 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1328 b1373 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1375 : ℝ := e1372 - e1374
lemma b1375 : Encl e1375 (94799439219 / 500000000000 : ℝ) (189598878453 / 1000000000000 : ℝ) := by
  exact Encl.sub b1372 b1374 (by norm_num) (by norm_num)

def e1376 : ℝ := e5 + e1344
lemma b1376 : Encl e1376 (386367699963 / 200000000000 : ℝ) (241479812477 / 125000000000 : ℝ) := by
  exact Encl.add b5 b1344 (by norm_num) (by norm_num)

def e1377 : ℝ := e1327 / e1376
lemma b1377 : Encl e1377 (18783830547 / 100000000000 : ℝ) (2934973523 / 15625000000 : ℝ) := by
  exact Encl.div_nonneg b1327 b1376 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1378 : ℝ := e1377 ^ 2
lemma b1378 : Encl e1378 (35283229001 / 1000000000000 : ℝ) (35283229003 / 1000000000000 : ℝ) := by
  exact Encl.pow b1377 (by norm_num) 2 (by norm_num) (by norm_num)

def e1379 : ℝ := e5 + e1378
lemma b1379 : Encl e1379 (1035283229001 / 1000000000000 : ℝ) (1035283229003 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1378 (by norm_num) (by norm_num)

def e1380 : ℝ := Real.sqrt e1379
lemma b1380 : Encl e1380 (508744343703 / 500000000000 : ℝ) (63593042963 / 62500000000 : ℝ) := by
  exact Encl.sqrt b1379 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1381 : ℝ := e5 + e1380
lemma b1381 : Encl e1381 (1008744343703 / 500000000000 : ℝ) (126093042963 / 62500000000 : ℝ) := by
  exact Encl.add b5 b1380 (by norm_num) (by norm_num)

def e1382 : ℝ := e1377 / e1381
lemma b1382 : Encl e1382 (46552505261 / 500000000000 : ℝ) (23276252631 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1377 b1381 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1383 : ℝ := Real.arcsin e1327

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
