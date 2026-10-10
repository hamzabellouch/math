import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical0

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1281 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1281 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1281 node1281Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node135 node135Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw66 singletonSmall1281
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1281) = raw66Labels := by decide +kernel
  rw [hl, canonical66 B hB] at h
  have hc0 : mixedMoment B raw66 (Fin.cases (0 : Fin 1) singletonSmall1281) =
      mixedMoment B node135 node135Labels := by
    have ha : raw66 = raw67 := by apply Matrix.ext; unfold raw66 raw67; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1281 = raw67Labels := by decide +kernel
    rw [ha, hj, canonical67 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1284 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1284 node1284Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node136 node136Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw68 singletonSmall1284
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1284) = raw68Labels := by decide +kernel
  rw [hl, canonical68 B hB] at h
  have hc0 : mixedMoment B raw68 (Fin.cases (0 : Fin 1) singletonSmall1284) =
      mixedMoment B node136 node136Labels := by
    have ha : raw68 = raw69 := by apply Matrix.ext; unfold raw68 raw69; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1284 = raw69Labels := by decide +kernel
    rw [ha, hj, canonical69 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1285 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1285 node1285Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node57 node57Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw70 singletonSmall1285
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1285) = raw70Labels := by decide +kernel
  rw [hl, canonical70 B hB] at h
  have hc0 : mixedMoment B raw70 (Fin.cases (0 : Fin 1) singletonSmall1285) =
      mixedMoment B node57 node57Labels := by
    have ha : raw70 = raw71 := by apply Matrix.ext; unfold raw70 raw71; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1285 = raw71Labels := by decide +kernel
    rw [ha, hj, canonical71 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1298 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1298 node1298Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node151 node151Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw72 singletonSmall1298
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1298) = raw72Labels := by decide +kernel
  rw [hl, canonical72 B hB] at h
  have hc0 : mixedMoment B raw72 (Fin.cases (0 : Fin 1) singletonSmall1298) =
      mixedMoment B node151 node151Labels := by
    have ha : raw72 = raw73 := by apply Matrix.ext; unfold raw72 raw73; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1298 = raw73Labels := by decide +kernel
    rw [ha, hj, canonical73 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1299 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1299 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1299 node1299Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node155 node155Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw74 singletonSmall1299
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1299) = raw74Labels := by decide +kernel
  rw [hl, canonical74 B hB] at h
  have hc0 : mixedMoment B raw74 (Fin.cases (0 : Fin 1) singletonSmall1299) =
      mixedMoment B node155 node155Labels := by
    have ha : raw74 = raw75 := by apply Matrix.ext; unfold raw74 raw75; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1299 = raw75Labels := by decide +kernel
    rw [ha, hj, canonical75 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1300 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1300 node1300Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node156 node156Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw76 singletonSmall1300
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1300) = raw76Labels := by decide +kernel
  rw [hl, canonical76 B hB] at h
  have hc0 : mixedMoment B raw76 (Fin.cases (0 : Fin 1) singletonSmall1300) =
      mixedMoment B node156 node156Labels := by
    have ha : raw76 = raw77 := by apply Matrix.ext; unfold raw76 raw77; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1300 = raw77Labels := by decide +kernel
    rw [ha, hj, canonical77 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1301 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1301 node1301Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node157 node157Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw78 singletonSmall1301
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1301) = raw78Labels := by decide +kernel
  rw [hl, canonical78 B hB] at h
  have hc0 : mixedMoment B raw78 (Fin.cases (0 : Fin 1) singletonSmall1301) =
      mixedMoment B node157 node157Labels := by
    have ha : raw78 = raw79 := by apply Matrix.ext; unfold raw78 raw79; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1301 = raw79Labels := by decide +kernel
    rw [ha, hj, canonical79 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1302 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1302 node1302Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node152 node152Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw80 singletonSmall1302
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1302) = raw80Labels := by decide +kernel
  rw [hl, canonical80 B hB] at h
  have hc0 : mixedMoment B raw80 (Fin.cases (0 : Fin 1) singletonSmall1302) =
      mixedMoment B node152 node152Labels := by
    have ha : raw80 = raw81 := by apply Matrix.ext; unfold raw80 raw81; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1302 = raw81Labels := by decide +kernel
    rw [ha, hj, canonical81 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1304 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1304 node1304Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node158 node158Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw82 singletonSmall1304
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1304) = raw82Labels := by decide +kernel
  rw [hl, canonical82 B hB] at h
  have hc0 : mixedMoment B raw82 (Fin.cases (0 : Fin 1) singletonSmall1304) =
      mixedMoment B node158 node158Labels := by
    have ha : raw82 = raw83 := by apply Matrix.ext; unfold raw82 raw83; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1304 = raw83Labels := by decide +kernel
    rw [ha, hj, canonical83 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1305 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1305 node1305Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node156 node156Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw84 singletonSmall1305
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1305) = raw84Labels := by decide +kernel
  rw [hl, canonical84 B hB] at h
  have hc0 : mixedMoment B raw84 (Fin.cases (0 : Fin 1) singletonSmall1305) =
      mixedMoment B node156 node156Labels := by
    have ha : raw84 = raw85 := by apply Matrix.ext; unfold raw84 raw85; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1305 = raw85Labels := by decide +kernel
    rw [ha, hj, canonical85 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1307 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1307 node1307Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node158 node158Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw86 singletonSmall1307
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1307) = raw86Labels := by decide +kernel
  rw [hl, canonical86 B hB] at h
  have hc0 : mixedMoment B raw86 (Fin.cases (0 : Fin 1) singletonSmall1307) =
      mixedMoment B node158 node158Labels := by
    have ha : raw86 = raw87 := by apply Matrix.ext; unfold raw86 raw87; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1307 = raw87Labels := by decide +kernel
    rw [ha, hj, canonical87 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1308 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1308 node1308Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node154 node154Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw88 singletonSmall1308
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1308) = raw88Labels := by decide +kernel
  rw [hl, canonical88 B hB] at h
  have hc0 : mixedMoment B raw88 (Fin.cases (0 : Fin 1) singletonSmall1308) =
      mixedMoment B node154 node154Labels := by
    have ha : raw88 = raw89 := by apply Matrix.ext; unfold raw88 raw89; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1308 = raw89Labels := by decide +kernel
    rw [ha, hj, canonical89 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1311 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1311 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1311 node1311Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node160 node160Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw90 singletonSmall1311
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1311) = raw90Labels := by decide +kernel
  rw [hl, canonical90 B hB] at h
  have hc0 : mixedMoment B raw90 (Fin.cases (0 : Fin 1) singletonSmall1311) =
      mixedMoment B node160 node160Labels := by
    have ha : raw90 = raw91 := by apply Matrix.ext; unfold raw90 raw91; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1311 = raw91Labels := by decide +kernel
    rw [ha, hj, canonical91 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1312 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1312 node1312Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node161 node161Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw92 singletonSmall1312
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1312) = raw92Labels := by decide +kernel
  rw [hl, canonical92 B hB] at h
  have hc0 : mixedMoment B raw92 (Fin.cases (0 : Fin 1) singletonSmall1312) =
      mixedMoment B node161 node161Labels := by
    have ha : raw92 = raw93 := by apply Matrix.ext; unfold raw92 raw93; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1312 = raw93Labels := by decide +kernel
    rw [ha, hj, canonical93 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1313 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1313 node1313Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node162 node162Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw94 singletonSmall1313
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1313) = raw94Labels := by decide +kernel
  rw [hl, canonical94 B hB] at h
  have hc0 : mixedMoment B raw94 (Fin.cases (0 : Fin 1) singletonSmall1313) =
      mixedMoment B node162 node162Labels := by
    have ha : raw94 = raw95 := by apply Matrix.ext; unfold raw94 raw95; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1313 = raw95Labels := by decide +kernel
    rw [ha, hj, canonical95 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1339 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1339 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1339 node1339Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node63 node63Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw96 singletonSmall1339
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1339) = raw96Labels := by decide +kernel
  rw [hl, canonical96 B hB] at h
  have hc0 : mixedMoment B raw96 (Fin.cases (0 : Fin 1) singletonSmall1339) =
      mixedMoment B node63 node63Labels := by
    have ha : raw96 = raw97 := by apply Matrix.ext; unfold raw96 raw97; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1339 = raw97Labels := by decide +kernel
    rw [ha, hj, canonical97 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1340 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1340 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1340 node1340Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node66 node66Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw98 singletonSmall1340
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1340) = raw98Labels := by decide +kernel
  rw [hl, canonical98 B hB] at h
  have hc0 : mixedMoment B raw98 (Fin.cases (0 : Fin 1) singletonSmall1340) =
      mixedMoment B node66 node66Labels := by
    have ha : raw98 = raw99 := by apply Matrix.ext; unfold raw98 raw99; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1340 = raw99Labels := by decide +kernel
    rw [ha, hj, canonical99 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1341 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1341 node1341Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node61 node61Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw100 singletonSmall1341
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1341) = raw100Labels := by decide +kernel
  rw [hl, canonical100 B hB] at h
  have hc0 : mixedMoment B raw100 (Fin.cases (0 : Fin 1) singletonSmall1341) =
      mixedMoment B node61 node61Labels := by
    have ha : raw100 = raw101 := by apply Matrix.ext; unfold raw100 raw101; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1341 = raw101Labels := by decide +kernel
    rw [ha, hj, canonical101 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1342 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1342 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1342 node1342Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node64 node64Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw102 singletonSmall1342
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1342) = raw102Labels := by decide +kernel
  rw [hl, canonical102 B hB] at h
  have hc0 : mixedMoment B raw102 (Fin.cases (0 : Fin 1) singletonSmall1342) =
      mixedMoment B node64 node64Labels := by
    have ha : raw102 = raw103 := by apply Matrix.ext; unfold raw102 raw103; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1342 = raw103Labels := by decide +kernel
    rw [ha, hj, canonical103 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1343 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1343 node1343Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node68 node68Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw104 singletonSmall1343
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1343) = raw104Labels := by decide +kernel
  rw [hl, canonical104 B hB] at h
  have hc0 : mixedMoment B raw104 (Fin.cases (0 : Fin 1) singletonSmall1343) =
      mixedMoment B node68 node68Labels := by
    have ha : raw104 = raw105 := by apply Matrix.ext; unfold raw104 raw105; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1343 = raw105Labels := by decide +kernel
    rw [ha, hj, canonical105 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
