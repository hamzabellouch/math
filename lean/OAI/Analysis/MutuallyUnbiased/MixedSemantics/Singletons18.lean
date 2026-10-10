import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical0

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1161 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1161 node1161Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node125 node125Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw18 singletonSmall1161
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1161) = raw18Labels := by decide +kernel
  rw [hl, canonical18 B hB] at h
  have hc0 : mixedMoment B raw18 (Fin.cases (0 : Fin 1) singletonSmall1161) =
      mixedMoment B node125 node125Labels := by
    have ha : raw18 = raw19 := by apply Matrix.ext; unfold raw18 raw19; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1161 = raw19Labels := by decide +kernel
    rw [ha, hj, canonical19 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1162 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1162 node1162Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node120 node120Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw20 singletonSmall1162
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1162) = raw20Labels := by decide +kernel
  rw [hl, canonical20 B hB] at h
  have hc0 : mixedMoment B raw20 (Fin.cases (0 : Fin 1) singletonSmall1162) =
      mixedMoment B node120 node120Labels := by
    have ha : raw20 = raw21 := by apply Matrix.ext; unfold raw20 raw21; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1162 = raw21Labels := by decide +kernel
    rw [ha, hj, canonical21 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1163 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1163 node1163Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node126 node126Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw22 singletonSmall1163
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1163) = raw22Labels := by decide +kernel
  rw [hl, canonical22 B hB] at h
  have hc0 : mixedMoment B raw22 (Fin.cases (0 : Fin 1) singletonSmall1163) =
      mixedMoment B node126 node126Labels := by
    have ha : raw22 = raw23 := by apply Matrix.ext; unfold raw22 raw23; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1163 = raw23Labels := by decide +kernel
    rw [ha, hj, canonical23 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1164 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1164 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1164 node1164Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node118 node118Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw24 singletonSmall1164
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1164) = raw24Labels := by decide +kernel
  rw [hl, canonical24 B hB] at h
  have hc0 : mixedMoment B raw24 (Fin.cases (0 : Fin 1) singletonSmall1164) =
      mixedMoment B node118 node118Labels := by
    have ha : raw24 = raw25 := by apply Matrix.ext; unfold raw24 raw25; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1164 = raw25Labels := by decide +kernel
    rw [ha, hj, canonical25 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1165 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1165 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1165 node1165Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node121 node121Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw26 singletonSmall1165
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1165) = raw26Labels := by decide +kernel
  rw [hl, canonical26 B hB] at h
  have hc0 : mixedMoment B raw26 (Fin.cases (0 : Fin 1) singletonSmall1165) =
      mixedMoment B node121 node121Labels := by
    have ha : raw26 = raw27 := by apply Matrix.ext; unfold raw26 raw27; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1165 = raw27Labels := by decide +kernel
    rw [ha, hj, canonical27 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1166 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1166 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1166 node1166Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node127 node127Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw28 singletonSmall1166
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1166) = raw28Labels := by decide +kernel
  rw [hl, canonical28 B hB] at h
  have hc0 : mixedMoment B raw28 (Fin.cases (0 : Fin 1) singletonSmall1166) =
      mixedMoment B node127 node127Labels := by
    have ha : raw28 = raw29 := by apply Matrix.ext; unfold raw28 raw29; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1166 = raw29Labels := by decide +kernel
    rw [ha, hj, canonical29 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1167 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1167 node1167Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node128 node128Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw30 singletonSmall1167
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1167) = raw30Labels := by decide +kernel
  rw [hl, canonical30 B hB] at h
  have hc0 : mixedMoment B raw30 (Fin.cases (0 : Fin 1) singletonSmall1167) =
      mixedMoment B node128 node128Labels := by
    have ha : raw30 = raw31 := by apply Matrix.ext; unfold raw30 raw31; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1167 = raw31Labels := by decide +kernel
    rw [ha, hj, canonical31 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1168 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1168 node1168Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node129 node129Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw32 singletonSmall1168
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1168) = raw32Labels := by decide +kernel
  rw [hl, canonical32 B hB] at h
  have hc0 : mixedMoment B raw32 (Fin.cases (0 : Fin 1) singletonSmall1168) =
      mixedMoment B node129 node129Labels := by
    have ha : raw32 = raw33 := by apply Matrix.ext; unfold raw32 raw33; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1168 = raw33Labels := by decide +kernel
    rw [ha, hj, canonical33 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1170 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1170 node1170Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node119 node119Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw34 singletonSmall1170
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1170) = raw34Labels := by decide +kernel
  rw [hl, canonical34 B hB] at h
  have hc0 : mixedMoment B raw34 (Fin.cases (0 : Fin 1) singletonSmall1170) =
      mixedMoment B node119 node119Labels := by
    have ha : raw34 = raw35 := by apply Matrix.ext; unfold raw34 raw35; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1170 = raw35Labels := by decide +kernel
    rw [ha, hj, canonical35 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1172 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1172 node1172Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node124 node124Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw36 singletonSmall1172
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1172) = raw36Labels := by decide +kernel
  rw [hl, canonical36 B hB] at h
  have hc0 : mixedMoment B raw36 (Fin.cases (0 : Fin 1) singletonSmall1172) =
      mixedMoment B node124 node124Labels := by
    have ha : raw36 = raw37 := by apply Matrix.ext; unfold raw36 raw37; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1172 = raw37Labels := by decide +kernel
    rw [ha, hj, canonical37 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1173 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1173 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1173 node1173Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node70 node70Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw38 singletonSmall1173
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1173) = raw38Labels := by decide +kernel
  rw [hl, canonical38 B hB] at h
  have hc0 : mixedMoment B raw38 (Fin.cases (0 : Fin 1) singletonSmall1173) =
      mixedMoment B node70 node70Labels := by
    have ha : raw38 = raw39 := by apply Matrix.ext; unfold raw38 raw39; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1173 = raw39Labels := by decide +kernel
    rw [ha, hj, canonical39 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1175 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1175 node1175Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node133 node133Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw40 singletonSmall1175
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1175) = raw40Labels := by decide +kernel
  rw [hl, canonical40 B hB] at h
  have hc0 : mixedMoment B raw40 (Fin.cases (0 : Fin 1) singletonSmall1175) =
      mixedMoment B node133 node133Labels := by
    have ha : raw40 = raw41 := by apply Matrix.ext; unfold raw40 raw41; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1175 = raw41Labels := by decide +kernel
    rw [ha, hj, canonical41 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1176 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1176 node1176Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node132 node132Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw42 singletonSmall1176
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1176) = raw42Labels := by decide +kernel
  rw [hl, canonical42 B hB] at h
  have hc0 : mixedMoment B raw42 (Fin.cases (0 : Fin 1) singletonSmall1176) =
      mixedMoment B node132 node132Labels := by
    have ha : raw42 = raw43 := by apply Matrix.ext; unfold raw42 raw43; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1176 = raw43Labels := by decide +kernel
    rw [ha, hj, canonical43 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1177 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1177 node1177Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node131 node131Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw44 singletonSmall1177
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1177) = raw44Labels := by decide +kernel
  rw [hl, canonical44 B hB] at h
  have hc0 : mixedMoment B raw44 (Fin.cases (0 : Fin 1) singletonSmall1177) =
      mixedMoment B node131 node131Labels := by
    have ha : raw44 = raw45 := by apply Matrix.ext; unfold raw44 raw45; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1177 = raw45Labels := by decide +kernel
    rw [ha, hj, canonical45 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
