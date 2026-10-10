import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical9

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4352 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4352 node4352Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node930 node930Labels + mixedMoment B node1690 node1690Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1143 singletonSmall4352
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4352) = raw1143Labels := by decide +kernel
  rw [hl, canonical1143 B hB] at h
  have hc0 : mixedMoment B raw1143 (Fin.cases (0 : Fin 2) singletonSmall4352) =
      mixedMoment B node930 node930Labels := by
    have ha : raw1143 = raw1144 := by apply Matrix.ext; unfold raw1143 raw1144; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4352 = raw1144Labels := by decide +kernel
    rw [ha, hj, canonical1144 B hB]
  have hc1 : mixedMoment B raw1143 (Fin.cases (1 : Fin 2) singletonSmall4352) =
      mixedMoment B node1690 node1690Labels := by
    have ha : raw1143 = raw1145 := by apply Matrix.ext; unfold raw1143 raw1145; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4352 = raw1145Labels := by decide +kernel
    rw [ha, hj, canonical1145 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4354 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4354 node4354Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node932 node932Labels + mixedMoment B node1681 node1681Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1146 singletonSmall4354
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4354) = raw1146Labels := by decide +kernel
  rw [hl, canonical1146 B hB] at h
  have hc0 : mixedMoment B raw1146 (Fin.cases (0 : Fin 2) singletonSmall4354) =
      mixedMoment B node932 node932Labels := by
    have ha : raw1146 = raw1147 := by apply Matrix.ext; unfold raw1146 raw1147; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4354 = raw1147Labels := by decide +kernel
    rw [ha, hj, canonical1147 B hB]
  have hc1 : mixedMoment B raw1146 (Fin.cases (1 : Fin 2) singletonSmall4354) =
      mixedMoment B node1681 node1681Labels := by
    have ha : raw1146 = raw1148 := by apply Matrix.ext; unfold raw1146 raw1148; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4354 = raw1148Labels := by decide +kernel
    rw [ha, hj, canonical1148 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4355 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4355 node4355Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node933 node933Labels + mixedMoment B node1691 node1691Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1149 singletonSmall4355
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4355) = raw1149Labels := by decide +kernel
  rw [hl, canonical1149 B hB] at h
  have hc0 : mixedMoment B raw1149 (Fin.cases (0 : Fin 2) singletonSmall4355) =
      mixedMoment B node933 node933Labels := by
    have ha : raw1149 = raw1150 := by apply Matrix.ext; unfold raw1149 raw1150; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4355 = raw1150Labels := by decide +kernel
    rw [ha, hj, canonical1150 B hB]
  have hc1 : mixedMoment B raw1149 (Fin.cases (1 : Fin 2) singletonSmall4355) =
      mixedMoment B node1691 node1691Labels := by
    have ha : raw1149 = raw1151 := by apply Matrix.ext; unfold raw1149 raw1151; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4355 = raw1151Labels := by decide +kernel
    rw [ha, hj, canonical1151 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4356 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4356 node4356Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node934 node934Labels + mixedMoment B node1692 node1692Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1152 singletonSmall4356
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4356) = raw1152Labels := by decide +kernel
  rw [hl, canonical1152 B hB] at h
  have hc0 : mixedMoment B raw1152 (Fin.cases (0 : Fin 2) singletonSmall4356) =
      mixedMoment B node934 node934Labels := by
    have ha : raw1152 = raw1153 := by apply Matrix.ext; unfold raw1152 raw1153; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4356 = raw1153Labels := by decide +kernel
    rw [ha, hj, canonical1153 B hB]
  have hc1 : mixedMoment B raw1152 (Fin.cases (1 : Fin 2) singletonSmall4356) =
      mixedMoment B node1692 node1692Labels := by
    have ha : raw1152 = raw1154 := by apply Matrix.ext; unfold raw1152 raw1154; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4356 = raw1154Labels := by decide +kernel
    rw [ha, hj, canonical1154 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4359 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4359 node4359Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node937 node937Labels + mixedMoment B node1683 node1683Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1155 singletonSmall4359
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4359) = raw1155Labels := by decide +kernel
  rw [hl, canonical1155 B hB] at h
  have hc0 : mixedMoment B raw1155 (Fin.cases (0 : Fin 2) singletonSmall4359) =
      mixedMoment B node937 node937Labels := by
    have ha : raw1155 = raw1156 := by apply Matrix.ext; unfold raw1155 raw1156; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4359 = raw1156Labels := by decide +kernel
    rw [ha, hj, canonical1156 B hB]
  have hc1 : mixedMoment B raw1155 (Fin.cases (1 : Fin 2) singletonSmall4359) =
      mixedMoment B node1683 node1683Labels := by
    have ha : raw1155 = raw1157 := by apply Matrix.ext; unfold raw1155 raw1157; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4359 = raw1157Labels := by decide +kernel
    rw [ha, hj, canonical1157 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4360 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4360 node4360Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node938 node938Labels + mixedMoment B node1693 node1693Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1158 singletonSmall4360
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4360) = raw1158Labels := by decide +kernel
  rw [hl, canonical1158 B hB] at h
  have hc0 : mixedMoment B raw1158 (Fin.cases (0 : Fin 2) singletonSmall4360) =
      mixedMoment B node938 node938Labels := by
    have ha : raw1158 = raw1159 := by apply Matrix.ext; unfold raw1158 raw1159; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4360 = raw1159Labels := by decide +kernel
    rw [ha, hj, canonical1159 B hB]
  have hc1 : mixedMoment B raw1158 (Fin.cases (1 : Fin 2) singletonSmall4360) =
      mixedMoment B node1693 node1693Labels := by
    have ha : raw1158 = raw1160 := by apply Matrix.ext; unfold raw1158 raw1160; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4360 = raw1160Labels := by decide +kernel
    rw [ha, hj, canonical1160 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4361 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4361 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4361 node4361Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node939 node939Labels + mixedMoment B node1694 node1694Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1161 singletonSmall4361
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4361) = raw1161Labels := by decide +kernel
  rw [hl, canonical1161 B hB] at h
  have hc0 : mixedMoment B raw1161 (Fin.cases (0 : Fin 2) singletonSmall4361) =
      mixedMoment B node939 node939Labels := by
    have ha : raw1161 = raw1162 := by apply Matrix.ext; unfold raw1161 raw1162; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4361 = raw1162Labels := by decide +kernel
    rw [ha, hj, canonical1162 B hB]
  have hc1 : mixedMoment B raw1161 (Fin.cases (1 : Fin 2) singletonSmall4361) =
      mixedMoment B node1694 node1694Labels := by
    have ha : raw1161 = raw1163 := by apply Matrix.ext; unfold raw1161 raw1163; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4361 = raw1163Labels := by decide +kernel
    rw [ha, hj, canonical1163 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4376 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4376 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4376 node4376Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node955 node955Labels + mixedMoment B node1542 node1542Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1164 singletonSmall4376
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4376) = raw1164Labels := by decide +kernel
  rw [hl, canonical1164 B hB] at h
  have hc0 : mixedMoment B raw1164 (Fin.cases (0 : Fin 2) singletonSmall4376) =
      mixedMoment B node955 node955Labels := by
    have ha : raw1164 = raw1165 := by apply Matrix.ext; unfold raw1164 raw1165; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4376 = raw1165Labels := by decide +kernel
    rw [ha, hj, canonical1165 B hB]
  have hc1 : mixedMoment B raw1164 (Fin.cases (1 : Fin 2) singletonSmall4376) =
      mixedMoment B node1542 node1542Labels := by
    have ha : raw1164 = raw1166 := by apply Matrix.ext; unfold raw1164 raw1166; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4376 = raw1166Labels := by decide +kernel
    rw [ha, hj, canonical1166 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4377 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4377 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4377 node4377Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node956 node956Labels + mixedMoment B node1543 node1543Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1167 singletonSmall4377
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4377) = raw1167Labels := by decide +kernel
  rw [hl, canonical1167 B hB] at h
  have hc0 : mixedMoment B raw1167 (Fin.cases (0 : Fin 2) singletonSmall4377) =
      mixedMoment B node956 node956Labels := by
    have ha : raw1167 = raw1168 := by apply Matrix.ext; unfold raw1167 raw1168; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4377 = raw1168Labels := by decide +kernel
    rw [ha, hj, canonical1168 B hB]
  have hc1 : mixedMoment B raw1167 (Fin.cases (1 : Fin 2) singletonSmall4377) =
      mixedMoment B node1543 node1543Labels := by
    have ha : raw1167 = raw1169 := by apply Matrix.ext; unfold raw1167 raw1169; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4377 = raw1169Labels := by decide +kernel
    rw [ha, hj, canonical1169 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4378 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4378 node4378Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node957 node957Labels + mixedMoment B node1544 node1544Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1170 singletonSmall4378
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4378) = raw1170Labels := by decide +kernel
  rw [hl, canonical1170 B hB] at h
  have hc0 : mixedMoment B raw1170 (Fin.cases (0 : Fin 2) singletonSmall4378) =
      mixedMoment B node957 node957Labels := by
    have ha : raw1170 = raw1171 := by apply Matrix.ext; unfold raw1170 raw1171; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4378 = raw1171Labels := by decide +kernel
    rw [ha, hj, canonical1171 B hB]
  have hc1 : mixedMoment B raw1170 (Fin.cases (1 : Fin 2) singletonSmall4378) =
      mixedMoment B node1544 node1544Labels := by
    have ha : raw1170 = raw1172 := by apply Matrix.ext; unfold raw1170 raw1172; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4378 = raw1172Labels := by decide +kernel
    rw [ha, hj, canonical1172 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4379 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4379 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4379 node4379Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node958 node958Labels + mixedMoment B node1545 node1545Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1173 singletonSmall4379
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4379) = raw1173Labels := by decide +kernel
  rw [hl, canonical1173 B hB] at h
  have hc0 : mixedMoment B raw1173 (Fin.cases (0 : Fin 2) singletonSmall4379) =
      mixedMoment B node958 node958Labels := by
    have ha : raw1173 = raw1174 := by apply Matrix.ext; unfold raw1173 raw1174; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4379 = raw1174Labels := by decide +kernel
    rw [ha, hj, canonical1174 B hB]
  have hc1 : mixedMoment B raw1173 (Fin.cases (1 : Fin 2) singletonSmall4379) =
      mixedMoment B node1545 node1545Labels := by
    have ha : raw1173 = raw1175 := by apply Matrix.ext; unfold raw1173 raw1175; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4379 = raw1175Labels := by decide +kernel
    rw [ha, hj, canonical1175 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4380 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4380 node4380Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node959 node959Labels + mixedMoment B node1546 node1546Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1176 singletonSmall4380
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4380) = raw1176Labels := by decide +kernel
  rw [hl, canonical1176 B hB] at h
  have hc0 : mixedMoment B raw1176 (Fin.cases (0 : Fin 2) singletonSmall4380) =
      mixedMoment B node959 node959Labels := by
    have ha : raw1176 = raw1177 := by apply Matrix.ext; unfold raw1176 raw1177; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4380 = raw1177Labels := by decide +kernel
    rw [ha, hj, canonical1177 B hB]
  have hc1 : mixedMoment B raw1176 (Fin.cases (1 : Fin 2) singletonSmall4380) =
      mixedMoment B node1546 node1546Labels := by
    have ha : raw1176 = raw1178 := by apply Matrix.ext; unfold raw1176 raw1178; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4380 = raw1178Labels := by decide +kernel
    rw [ha, hj, canonical1178 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4381 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4381 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4381 node4381Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node960 node960Labels + mixedMoment B node1547 node1547Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1179 singletonSmall4381
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4381) = raw1179Labels := by decide +kernel
  rw [hl, canonical1179 B hB] at h
  have hc0 : mixedMoment B raw1179 (Fin.cases (0 : Fin 2) singletonSmall4381) =
      mixedMoment B node960 node960Labels := by
    have ha : raw1179 = raw1180 := by apply Matrix.ext; unfold raw1179 raw1180; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4381 = raw1180Labels := by decide +kernel
    rw [ha, hj, canonical1180 B hB]
  have hc1 : mixedMoment B raw1179 (Fin.cases (1 : Fin 2) singletonSmall4381) =
      mixedMoment B node1547 node1547Labels := by
    have ha : raw1179 = raw1181 := by apply Matrix.ext; unfold raw1179 raw1181; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4381 = raw1181Labels := by decide +kernel
    rw [ha, hj, canonical1181 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4382 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4382 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4382 node4382Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node962 node962Labels + mixedMoment B node1548 node1548Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1182 singletonSmall4382
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4382) = raw1182Labels := by decide +kernel
  rw [hl, canonical1182 B hB] at h
  have hc0 : mixedMoment B raw1182 (Fin.cases (0 : Fin 2) singletonSmall4382) =
      mixedMoment B node962 node962Labels := by
    have ha : raw1182 = raw1183 := by apply Matrix.ext; unfold raw1182 raw1183; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4382 = raw1183Labels := by decide +kernel
    rw [ha, hj, canonical1183 B hB]
  have hc1 : mixedMoment B raw1182 (Fin.cases (1 : Fin 2) singletonSmall4382) =
      mixedMoment B node1548 node1548Labels := by
    have ha : raw1182 = raw1184 := by apply Matrix.ext; unfold raw1182 raw1184; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4382 = raw1184Labels := by decide +kernel
    rw [ha, hj, canonical1184 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4383 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4383 node4383Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node963 node963Labels + mixedMoment B node1549 node1549Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1185 singletonSmall4383
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4383) = raw1185Labels := by decide +kernel
  rw [hl, canonical1185 B hB] at h
  have hc0 : mixedMoment B raw1185 (Fin.cases (0 : Fin 2) singletonSmall4383) =
      mixedMoment B node963 node963Labels := by
    have ha : raw1185 = raw1186 := by apply Matrix.ext; unfold raw1185 raw1186; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4383 = raw1186Labels := by decide +kernel
    rw [ha, hj, canonical1186 B hB]
  have hc1 : mixedMoment B raw1185 (Fin.cases (1 : Fin 2) singletonSmall4383) =
      mixedMoment B node1549 node1549Labels := by
    have ha : raw1185 = raw1187 := by apply Matrix.ext; unfold raw1185 raw1187; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4383 = raw1187Labels := by decide +kernel
    rw [ha, hj, canonical1187 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4384 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4384 node4384Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node964 node964Labels + mixedMoment B node1580 node1580Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1188 singletonSmall4384
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4384) = raw1188Labels := by decide +kernel
  rw [hl, canonical1188 B hB] at h
  have hc0 : mixedMoment B raw1188 (Fin.cases (0 : Fin 2) singletonSmall4384) =
      mixedMoment B node964 node964Labels := by
    have ha : raw1188 = raw1189 := by apply Matrix.ext; unfold raw1188 raw1189; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4384 = raw1189Labels := by decide +kernel
    rw [ha, hj, canonical1189 B hB]
  have hc1 : mixedMoment B raw1188 (Fin.cases (1 : Fin 2) singletonSmall4384) =
      mixedMoment B node1580 node1580Labels := by
    have ha : raw1188 = raw1190 := by apply Matrix.ext; unfold raw1188 raw1190; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4384 = raw1190Labels := by decide +kernel
    rw [ha, hj, canonical1190 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4385 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4385 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4385 node4385Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node965 node965Labels + mixedMoment B node1581 node1581Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1191 singletonSmall4385
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4385) = raw1191Labels := by decide +kernel
  rw [hl, canonical1191 B hB] at h
  have hc0 : mixedMoment B raw1191 (Fin.cases (0 : Fin 2) singletonSmall4385) =
      mixedMoment B node965 node965Labels := by
    have ha : raw1191 = raw1192 := by apply Matrix.ext; unfold raw1191 raw1192; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4385 = raw1192Labels := by decide +kernel
    rw [ha, hj, canonical1192 B hB]
  have hc1 : mixedMoment B raw1191 (Fin.cases (1 : Fin 2) singletonSmall4385) =
      mixedMoment B node1581 node1581Labels := by
    have ha : raw1191 = raw1193 := by apply Matrix.ext; unfold raw1191 raw1193; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4385 = raw1193Labels := by decide +kernel
    rw [ha, hj, canonical1193 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4386 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4386 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4386 node4386Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node966 node966Labels + mixedMoment B node1582 node1582Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1194 singletonSmall4386
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4386) = raw1194Labels := by decide +kernel
  rw [hl, canonical1194 B hB] at h
  have hc0 : mixedMoment B raw1194 (Fin.cases (0 : Fin 2) singletonSmall4386) =
      mixedMoment B node966 node966Labels := by
    have ha : raw1194 = raw1195 := by apply Matrix.ext; unfold raw1194 raw1195; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4386 = raw1195Labels := by decide +kernel
    rw [ha, hj, canonical1195 B hB]
  have hc1 : mixedMoment B raw1194 (Fin.cases (1 : Fin 2) singletonSmall4386) =
      mixedMoment B node1582 node1582Labels := by
    have ha : raw1194 = raw1196 := by apply Matrix.ext; unfold raw1194 raw1196; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4386 = raw1196Labels := by decide +kernel
    rw [ha, hj, canonical1196 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4387 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4387 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4387 node4387Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node967 node967Labels + mixedMoment B node1583 node1583Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1197 singletonSmall4387
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4387) = raw1197Labels := by decide +kernel
  rw [hl, canonical1197 B hB] at h
  have hc0 : mixedMoment B raw1197 (Fin.cases (0 : Fin 2) singletonSmall4387) =
      mixedMoment B node967 node967Labels := by
    have ha : raw1197 = raw1198 := by apply Matrix.ext; unfold raw1197 raw1198; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4387 = raw1198Labels := by decide +kernel
    rw [ha, hj, canonical1198 B hB]
  have hc1 : mixedMoment B raw1197 (Fin.cases (1 : Fin 2) singletonSmall4387) =
      mixedMoment B node1583 node1583Labels := by
    have ha : raw1197 = raw1199 := by apply Matrix.ext; unfold raw1197 raw1199; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4387 = raw1199Labels := by decide +kernel
    rw [ha, hj, canonical1199 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4388 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4388 node4388Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node969 node969Labels + mixedMoment B node1584 node1584Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1200 singletonSmall4388
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4388) = raw1200Labels := by decide +kernel
  rw [hl, canonical1200 B hB] at h
  have hc0 : mixedMoment B raw1200 (Fin.cases (0 : Fin 2) singletonSmall4388) =
      mixedMoment B node969 node969Labels := by
    have ha : raw1200 = raw1201 := by apply Matrix.ext; unfold raw1200 raw1201; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4388 = raw1201Labels := by decide +kernel
    rw [ha, hj, canonical1201 B hB]
  have hc1 : mixedMoment B raw1200 (Fin.cases (1 : Fin 2) singletonSmall4388) =
      mixedMoment B node1584 node1584Labels := by
    have ha : raw1200 = raw1202 := by apply Matrix.ext; unfold raw1200 raw1202; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4388 = raw1202Labels := by decide +kernel
    rw [ha, hj, canonical1202 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4389 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4389 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4389 node4389Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node970 node970Labels + mixedMoment B node1585 node1585Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1203 singletonSmall4389
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4389) = raw1203Labels := by decide +kernel
  rw [hl, canonical1203 B hB] at h
  have hc0 : mixedMoment B raw1203 (Fin.cases (0 : Fin 2) singletonSmall4389) =
      mixedMoment B node970 node970Labels := by
    have ha : raw1203 = raw1204 := by apply Matrix.ext; unfold raw1203 raw1204; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4389 = raw1204Labels := by decide +kernel
    rw [ha, hj, canonical1204 B hB]
  have hc1 : mixedMoment B raw1203 (Fin.cases (1 : Fin 2) singletonSmall4389) =
      mixedMoment B node1585 node1585Labels := by
    have ha : raw1203 = raw1205 := by apply Matrix.ext; unfold raw1203 raw1205; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4389 = raw1205Labels := by decide +kernel
    rw [ha, hj, canonical1205 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4396 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4396 node4396Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node977 node977Labels + mixedMoment B node1597 node1597Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1206 singletonSmall4396
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4396) = raw1206Labels := by decide +kernel
  rw [hl, canonical1206 B hB] at h
  have hc0 : mixedMoment B raw1206 (Fin.cases (0 : Fin 2) singletonSmall4396) =
      mixedMoment B node977 node977Labels := by
    have ha : raw1206 = raw1207 := by apply Matrix.ext; unfold raw1206 raw1207; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4396 = raw1207Labels := by decide +kernel
    rw [ha, hj, canonical1207 B hB]
  have hc1 : mixedMoment B raw1206 (Fin.cases (1 : Fin 2) singletonSmall4396) =
      mixedMoment B node1597 node1597Labels := by
    have ha : raw1206 = raw1208 := by apply Matrix.ext; unfold raw1206 raw1208; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4396 = raw1208Labels := by decide +kernel
    rw [ha, hj, canonical1208 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4398 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4398 node4398Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node979 node979Labels + mixedMoment B node1599 node1599Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1209 singletonSmall4398
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4398) = raw1209Labels := by decide +kernel
  rw [hl, canonical1209 B hB] at h
  have hc0 : mixedMoment B raw1209 (Fin.cases (0 : Fin 2) singletonSmall4398) =
      mixedMoment B node979 node979Labels := by
    have ha : raw1209 = raw1210 := by apply Matrix.ext; unfold raw1209 raw1210; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4398 = raw1210Labels := by decide +kernel
    rw [ha, hj, canonical1210 B hB]
  have hc1 : mixedMoment B raw1209 (Fin.cases (1 : Fin 2) singletonSmall4398) =
      mixedMoment B node1599 node1599Labels := by
    have ha : raw1209 = raw1211 := by apply Matrix.ext; unfold raw1209 raw1211; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4398 = raw1211Labels := by decide +kernel
    rw [ha, hj, canonical1211 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4399 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4399 node4399Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node980 node980Labels + mixedMoment B node1616 node1616Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1212 singletonSmall4399
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4399) = raw1212Labels := by decide +kernel
  rw [hl, canonical1212 B hB] at h
  have hc0 : mixedMoment B raw1212 (Fin.cases (0 : Fin 2) singletonSmall4399) =
      mixedMoment B node980 node980Labels := by
    have ha : raw1212 = raw1213 := by apply Matrix.ext; unfold raw1212 raw1213; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4399 = raw1213Labels := by decide +kernel
    rw [ha, hj, canonical1213 B hB]
  have hc1 : mixedMoment B raw1212 (Fin.cases (1 : Fin 2) singletonSmall4399) =
      mixedMoment B node1616 node1616Labels := by
    have ha : raw1212 = raw1214 := by apply Matrix.ext; unfold raw1212 raw1214; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4399 = raw1214Labels := by decide +kernel
    rw [ha, hj, canonical1214 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4401 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4401 node4401Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node982 node982Labels + mixedMoment B node1617 node1617Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1215 singletonSmall4401
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4401) = raw1215Labels := by decide +kernel
  rw [hl, canonical1215 B hB] at h
  have hc0 : mixedMoment B raw1215 (Fin.cases (0 : Fin 2) singletonSmall4401) =
      mixedMoment B node982 node982Labels := by
    have ha : raw1215 = raw1216 := by apply Matrix.ext; unfold raw1215 raw1216; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4401 = raw1216Labels := by decide +kernel
    rw [ha, hj, canonical1216 B hB]
  have hc1 : mixedMoment B raw1215 (Fin.cases (1 : Fin 2) singletonSmall4401) =
      mixedMoment B node1617 node1617Labels := by
    have ha : raw1215 = raw1217 := by apply Matrix.ext; unfold raw1215 raw1217; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4401 = raw1217Labels := by decide +kernel
    rw [ha, hj, canonical1217 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4404 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4404 node4404Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node985 node985Labels + mixedMoment B node1618 node1618Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1218 singletonSmall4404
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4404) = raw1218Labels := by decide +kernel
  rw [hl, canonical1218 B hB] at h
  have hc0 : mixedMoment B raw1218 (Fin.cases (0 : Fin 2) singletonSmall4404) =
      mixedMoment B node985 node985Labels := by
    have ha : raw1218 = raw1219 := by apply Matrix.ext; unfold raw1218 raw1219; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4404 = raw1219Labels := by decide +kernel
    rw [ha, hj, canonical1219 B hB]
  have hc1 : mixedMoment B raw1218 (Fin.cases (1 : Fin 2) singletonSmall4404) =
      mixedMoment B node1618 node1618Labels := by
    have ha : raw1218 = raw1220 := by apply Matrix.ext; unfold raw1218 raw1220; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4404 = raw1220Labels := by decide +kernel
    rw [ha, hj, canonical1220 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4405 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4405 node4405Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node986 node986Labels + mixedMoment B node1620 node1620Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1221 singletonSmall4405
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4405) = raw1221Labels := by decide +kernel
  rw [hl, canonical1221 B hB] at h
  have hc0 : mixedMoment B raw1221 (Fin.cases (0 : Fin 2) singletonSmall4405) =
      mixedMoment B node986 node986Labels := by
    have ha : raw1221 = raw1222 := by apply Matrix.ext; unfold raw1221 raw1222; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4405 = raw1222Labels := by decide +kernel
    rw [ha, hj, canonical1222 B hB]
  have hc1 : mixedMoment B raw1221 (Fin.cases (1 : Fin 2) singletonSmall4405) =
      mixedMoment B node1620 node1620Labels := by
    have ha : raw1221 = raw1223 := by apply Matrix.ext; unfold raw1221 raw1223; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4405 = raw1223Labels := by decide +kernel
    rw [ha, hj, canonical1223 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
