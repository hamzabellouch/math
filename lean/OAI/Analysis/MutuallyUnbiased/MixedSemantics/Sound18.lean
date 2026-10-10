import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons18

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1152 node1152Labels = Sparse.eval nodeValue1152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1152) = mixedMoment B node1152 node1152Labels := rfl
  simpa [nodeValue1152, Sparse.eval] using hc.symm

theorem sound1153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1153 node1153Labels = Sparse.eval nodeValue1153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1153) = mixedMoment B node1153 node1153Labels := rfl
  simpa [nodeValue1153, Sparse.eval] using hc.symm

theorem sound1154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1154 node1154Labels = Sparse.eval nodeValue1154 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1154) = mixedMoment B node1154 node1154Labels := rfl
  simpa [nodeValue1154, Sparse.eval] using hc.symm

theorem sound1155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1155 node1155Labels = Sparse.eval nodeValue1155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1155) = mixedMoment B node1155 node1155Labels := rfl
  simpa [nodeValue1155, Sparse.eval] using hc.symm

theorem sound1156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1156 node1156Labels = Sparse.eval nodeValue1156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1156) = mixedMoment B node1156 node1156Labels := rfl
  simpa [nodeValue1156, Sparse.eval] using hc.symm

theorem sound1157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1157 node1157Labels = Sparse.eval nodeValue1157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1157) = mixedMoment B node1157 node1157Labels := rfl
  simpa [nodeValue1157, Sparse.eval] using hc.symm

theorem sound1158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1158 node1158Labels = Sparse.eval nodeValue1158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1158) = mixedMoment B node1158 node1158Labels := rfl
  simpa [nodeValue1158, Sparse.eval] using hc.symm

theorem sound1159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1159 node1159Labels = Sparse.eval nodeValue1159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1159) = mixedMoment B node1159 node1159Labels := rfl
  simpa [nodeValue1159, Sparse.eval] using hc.symm

theorem sound1160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1160 node1160Labels = Sparse.eval nodeValue1160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1160) = mixedMoment B node1160 node1160Labels := rfl
  simpa [nodeValue1160, Sparse.eval] using hc.symm

theorem sound1161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1161 node1161Labels = Sparse.eval nodeValue1161 (mixedVector B) := by
  have h := singleton1161 B _hB
  rw [sound125 B _hB _hF] at h
  norm_num [nodeValue1161, nodeValue125, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1162 node1162Labels = Sparse.eval nodeValue1162 (mixedVector B) := by
  have h := singleton1162 B _hB
  rw [sound120 B _hB _hF] at h
  norm_num [nodeValue1162, nodeValue120, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1163 node1163Labels = Sparse.eval nodeValue1163 (mixedVector B) := by
  have h := singleton1163 B _hB
  rw [sound126 B _hB _hF] at h
  norm_num [nodeValue1163, nodeValue126, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1164 node1164Labels = Sparse.eval nodeValue1164 (mixedVector B) := by
  have h := singleton1164 B _hB
  rw [sound118 B _hB _hF] at h
  norm_num [nodeValue1164, nodeValue118, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1165 node1165Labels = Sparse.eval nodeValue1165 (mixedVector B) := by
  have h := singleton1165 B _hB
  rw [sound121 B _hB _hF] at h
  norm_num [nodeValue1165, nodeValue121, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1166 node1166Labels = Sparse.eval nodeValue1166 (mixedVector B) := by
  have h := singleton1166 B _hB
  rw [sound127 B _hB _hF] at h
  norm_num [nodeValue1166, nodeValue127, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1167 node1167Labels = Sparse.eval nodeValue1167 (mixedVector B) := by
  have h := singleton1167 B _hB
  rw [sound128 B _hB _hF] at h
  norm_num [nodeValue1167, nodeValue128, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1168 node1168Labels = Sparse.eval nodeValue1168 (mixedVector B) := by
  have h := singleton1168 B _hB
  rw [sound129 B _hB _hF] at h
  norm_num [nodeValue1168, nodeValue129, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1169 node1169Labels = Sparse.eval nodeValue1169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1169) = mixedMoment B node1169 node1169Labels := rfl
  simpa [nodeValue1169, Sparse.eval] using hc.symm

theorem sound1170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1170 node1170Labels = Sparse.eval nodeValue1170 (mixedVector B) := by
  have h := singleton1170 B _hB
  rw [sound119 B _hB _hF] at h
  norm_num [nodeValue1170, nodeValue119, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1171 node1171Labels = Sparse.eval nodeValue1171 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1171) = mixedMoment B node1171 node1171Labels := rfl
  simpa [nodeValue1171, Sparse.eval] using hc.symm

theorem sound1172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1172 node1172Labels = Sparse.eval nodeValue1172 (mixedVector B) := by
  have h := singleton1172 B _hB
  rw [sound124 B _hB _hF] at h
  norm_num [nodeValue1172, nodeValue124, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1173 node1173Labels = Sparse.eval nodeValue1173 (mixedVector B) := by
  have h := singleton1173 B _hB
  rw [sound70 B _hB _hF] at h
  norm_num [nodeValue1173, nodeValue70, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1174 node1174Labels = Sparse.eval nodeValue1174 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1174) = mixedMoment B node1174 node1174Labels := rfl
  simpa [nodeValue1174, Sparse.eval] using hc.symm

theorem sound1175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1175 node1175Labels = Sparse.eval nodeValue1175 (mixedVector B) := by
  have h := singleton1175 B _hB
  rw [sound133 B _hB _hF] at h
  norm_num [nodeValue1175, nodeValue133, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1176 node1176Labels = Sparse.eval nodeValue1176 (mixedVector B) := by
  have h := singleton1176 B _hB
  rw [sound132 B _hB _hF] at h
  norm_num [nodeValue1176, nodeValue132, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1177 node1177Labels = Sparse.eval nodeValue1177 (mixedVector B) := by
  have h := singleton1177 B _hB
  rw [sound131 B _hB _hF] at h
  norm_num [nodeValue1177, nodeValue131, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1178 node1178Labels = Sparse.eval nodeValue1178 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1178) = mixedMoment B node1178 node1178Labels := rfl
  simpa [nodeValue1178, Sparse.eval] using hc.symm

theorem sound1179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1179 node1179Labels = Sparse.eval nodeValue1179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1179) = mixedMoment B node1179 node1179Labels := rfl
  simpa [nodeValue1179, Sparse.eval] using hc.symm

theorem sound1180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1180 node1180Labels = Sparse.eval nodeValue1180 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1180) = mixedMoment B node1180 node1180Labels := rfl
  simpa [nodeValue1180, Sparse.eval] using hc.symm

theorem sound1181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1181 node1181Labels = Sparse.eval nodeValue1181 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1181) = mixedMoment B node1181 node1181Labels := rfl
  simpa [nodeValue1181, Sparse.eval] using hc.symm

theorem sound1182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1182 node1182Labels = Sparse.eval nodeValue1182 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1182) = mixedMoment B node1182 node1182Labels := rfl
  simpa [nodeValue1182, Sparse.eval] using hc.symm

theorem sound1183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1183 node1183Labels = Sparse.eval nodeValue1183 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1183) = mixedMoment B node1183 node1183Labels := rfl
  simpa [nodeValue1183, Sparse.eval] using hc.symm

theorem sound1184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1184 node1184Labels = Sparse.eval nodeValue1184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1184) = mixedMoment B node1184 node1184Labels := rfl
  simpa [nodeValue1184, Sparse.eval] using hc.symm

theorem sound1185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1185 node1185Labels = Sparse.eval nodeValue1185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1185) = mixedMoment B node1185 node1185Labels := rfl
  simpa [nodeValue1185, Sparse.eval] using hc.symm

theorem sound1186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1186 node1186Labels = Sparse.eval nodeValue1186 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1186) = mixedMoment B node1186 node1186Labels := rfl
  simpa [nodeValue1186, Sparse.eval] using hc.symm

theorem sound1187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1187 node1187Labels = Sparse.eval nodeValue1187 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1187) = mixedMoment B node1187 node1187Labels := rfl
  simpa [nodeValue1187, Sparse.eval] using hc.symm

theorem sound1188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1188 node1188Labels = Sparse.eval nodeValue1188 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1188) = mixedMoment B node1188 node1188Labels := rfl
  simpa [nodeValue1188, Sparse.eval] using hc.symm

theorem sound1189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1189 node1189Labels = Sparse.eval nodeValue1189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1189) = mixedMoment B node1189 node1189Labels := rfl
  simpa [nodeValue1189, Sparse.eval] using hc.symm

theorem sound1190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1190 node1190Labels = Sparse.eval nodeValue1190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1190) = mixedMoment B node1190 node1190Labels := rfl
  simpa [nodeValue1190, Sparse.eval] using hc.symm

theorem sound1191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1191 node1191Labels = Sparse.eval nodeValue1191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1191) = mixedMoment B node1191 node1191Labels := rfl
  simpa [nodeValue1191, Sparse.eval] using hc.symm

theorem sound1192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1192 node1192Labels = Sparse.eval nodeValue1192 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1192) = mixedMoment B node1192 node1192Labels := rfl
  simpa [nodeValue1192, Sparse.eval] using hc.symm

theorem sound1193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1193 node1193Labels = Sparse.eval nodeValue1193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1193) = mixedMoment B node1193 node1193Labels := rfl
  simpa [nodeValue1193, Sparse.eval] using hc.symm

theorem sound1194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1194 node1194Labels = Sparse.eval nodeValue1194 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1194) = mixedMoment B node1194 node1194Labels := rfl
  simpa [nodeValue1194, Sparse.eval] using hc.symm

theorem sound1195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1195 node1195Labels = Sparse.eval nodeValue1195 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1195) = mixedMoment B node1195 node1195Labels := rfl
  simpa [nodeValue1195, Sparse.eval] using hc.symm

theorem sound1196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1196 node1196Labels = Sparse.eval nodeValue1196 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1196) = mixedMoment B node1196 node1196Labels := rfl
  simpa [nodeValue1196, Sparse.eval] using hc.symm

theorem sound1197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1197 node1197Labels = Sparse.eval nodeValue1197 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1197) = mixedMoment B node1197 node1197Labels := rfl
  simpa [nodeValue1197, Sparse.eval] using hc.symm

theorem sound1198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1198 node1198Labels = Sparse.eval nodeValue1198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1198) = mixedMoment B node1198 node1198Labels := rfl
  simpa [nodeValue1198, Sparse.eval] using hc.symm

theorem sound1199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1199 node1199Labels = Sparse.eval nodeValue1199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1199) = mixedMoment B node1199 node1199Labels := rfl
  simpa [nodeValue1199, Sparse.eval] using hc.symm

theorem sound1200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1200 node1200Labels = Sparse.eval nodeValue1200 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1200) = mixedMoment B node1200 node1200Labels := rfl
  simpa [nodeValue1200, Sparse.eval] using hc.symm

theorem sound1201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1201 node1201Labels = Sparse.eval nodeValue1201 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1201) = mixedMoment B node1201 node1201Labels := rfl
  simpa [nodeValue1201, Sparse.eval] using hc.symm

theorem sound1202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1202 node1202Labels = Sparse.eval nodeValue1202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1202) = mixedMoment B node1202 node1202Labels := rfl
  simpa [nodeValue1202, Sparse.eval] using hc.symm

theorem sound1203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1203 node1203Labels = Sparse.eval nodeValue1203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1203) = mixedMoment B node1203 node1203Labels := rfl
  simpa [nodeValue1203, Sparse.eval] using hc.symm

theorem sound1204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1204 node1204Labels = Sparse.eval nodeValue1204 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1204) = mixedMoment B node1204 node1204Labels := rfl
  simpa [nodeValue1204, Sparse.eval] using hc.symm

theorem sound1205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1205 node1205Labels = Sparse.eval nodeValue1205 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1205) = mixedMoment B node1205 node1205Labels := rfl
  simpa [nodeValue1205, Sparse.eval] using hc.symm

theorem sound1206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1206 node1206Labels = Sparse.eval nodeValue1206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1206) = mixedMoment B node1206 node1206Labels := rfl
  simpa [nodeValue1206, Sparse.eval] using hc.symm

theorem sound1207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1207 node1207Labels = Sparse.eval nodeValue1207 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1207) = mixedMoment B node1207 node1207Labels := rfl
  simpa [nodeValue1207, Sparse.eval] using hc.symm

theorem sound1208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1208 node1208Labels = Sparse.eval nodeValue1208 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1208) = mixedMoment B node1208 node1208Labels := rfl
  simpa [nodeValue1208, Sparse.eval] using hc.symm

theorem sound1209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1209 node1209Labels = Sparse.eval nodeValue1209 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1209) = mixedMoment B node1209 node1209Labels := rfl
  simpa [nodeValue1209, Sparse.eval] using hc.symm

theorem sound1210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1210 node1210Labels = Sparse.eval nodeValue1210 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1210) = mixedMoment B node1210 node1210Labels := rfl
  simpa [nodeValue1210, Sparse.eval] using hc.symm

theorem sound1211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1211 node1211Labels = Sparse.eval nodeValue1211 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1211) = mixedMoment B node1211 node1211Labels := rfl
  simpa [nodeValue1211, Sparse.eval] using hc.symm

theorem sound1212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1212 node1212Labels = Sparse.eval nodeValue1212 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1212) = mixedMoment B node1212 node1212Labels := rfl
  simpa [nodeValue1212, Sparse.eval] using hc.symm

theorem sound1213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1213 node1213Labels = Sparse.eval nodeValue1213 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1213) = mixedMoment B node1213 node1213Labels := rfl
  simpa [nodeValue1213, Sparse.eval] using hc.symm

theorem sound1214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1214 node1214Labels = Sparse.eval nodeValue1214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1214) = mixedMoment B node1214 node1214Labels := rfl
  simpa [nodeValue1214, Sparse.eval] using hc.symm

theorem sound1215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1215 node1215Labels = Sparse.eval nodeValue1215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1215) = mixedMoment B node1215 node1215Labels := rfl
  simpa [nodeValue1215, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
