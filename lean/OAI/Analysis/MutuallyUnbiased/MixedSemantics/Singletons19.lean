import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical0

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1251 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1251 node1251Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node137 node137Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw46 singletonSmall1251
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1251) = raw46Labels := by decide +kernel
  rw [hl, canonical46 B hB] at h
  have hc0 : mixedMoment B raw46 (Fin.cases (0 : Fin 1) singletonSmall1251) =
      mixedMoment B node137 node137Labels := by
    have ha : raw46 = raw47 := by apply Matrix.ext; unfold raw46 raw47; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1251 = raw47Labels := by decide +kernel
    rw [ha, hj, canonical47 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1254 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1254 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1254 node1254Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node138 node138Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw48 singletonSmall1254
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1254) = raw48Labels := by decide +kernel
  rw [hl, canonical48 B hB] at h
  have hc0 : mixedMoment B raw48 (Fin.cases (0 : Fin 1) singletonSmall1254) =
      mixedMoment B node138 node138Labels := by
    have ha : raw48 = raw49 := by apply Matrix.ext; unfold raw48 raw49; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1254 = raw49Labels := by decide +kernel
    rw [ha, hj, canonical49 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1255 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1255 node1255Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node49 node49Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw50 singletonSmall1255
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1255) = raw50Labels := by decide +kernel
  rw [hl, canonical50 B hB] at h
  have hc0 : mixedMoment B raw50 (Fin.cases (0 : Fin 1) singletonSmall1255) =
      mixedMoment B node49 node49Labels := by
    have ha : raw50 = raw51 := by apply Matrix.ext; unfold raw50 raw51; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1255 = raw51Labels := by decide +kernel
    rw [ha, hj, canonical51 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1265 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1265 node1265Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node141 node141Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw52 singletonSmall1265
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1265) = raw52Labels := by decide +kernel
  rw [hl, canonical52 B hB] at h
  have hc0 : mixedMoment B raw52 (Fin.cases (0 : Fin 1) singletonSmall1265) =
      mixedMoment B node141 node141Labels := by
    have ha : raw52 = raw53 := by apply Matrix.ext; unfold raw52 raw53; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1265 = raw53Labels := by decide +kernel
    rw [ha, hj, canonical53 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1266 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1266 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1266 node1266Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node144 node144Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw54 singletonSmall1266
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1266) = raw54Labels := by decide +kernel
  rw [hl, canonical54 B hB] at h
  have hc0 : mixedMoment B raw54 (Fin.cases (0 : Fin 1) singletonSmall1266) =
      mixedMoment B node144 node144Labels := by
    have ha : raw54 = raw55 := by apply Matrix.ext; unfold raw54 raw55; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1266 = raw55Labels := by decide +kernel
    rw [ha, hj, canonical55 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1267 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1267 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1267 node1267Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node142 node142Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw56 singletonSmall1267
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1267) = raw56Labels := by decide +kernel
  rw [hl, canonical56 B hB] at h
  have hc0 : mixedMoment B raw56 (Fin.cases (0 : Fin 1) singletonSmall1267) =
      mixedMoment B node142 node142Labels := by
    have ha : raw56 = raw57 := by apply Matrix.ext; unfold raw56 raw57; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1267 = raw57Labels := by decide +kernel
    rw [ha, hj, canonical57 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1269 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1269 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1269 node1269Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node146 node146Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw58 singletonSmall1269
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1269) = raw58Labels := by decide +kernel
  rw [hl, canonical58 B hB] at h
  have hc0 : mixedMoment B raw58 (Fin.cases (0 : Fin 1) singletonSmall1269) =
      mixedMoment B node146 node146Labels := by
    have ha : raw58 = raw59 := by apply Matrix.ext; unfold raw58 raw59; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1269 = raw59Labels := by decide +kernel
    rw [ha, hj, canonical59 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1271 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1271 node1271Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node143 node143Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw60 singletonSmall1271
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1271) = raw60Labels := by decide +kernel
  rw [hl, canonical60 B hB] at h
  have hc0 : mixedMoment B raw60 (Fin.cases (0 : Fin 1) singletonSmall1271) =
      mixedMoment B node143 node143Labels := by
    have ha : raw60 = raw61 := by apply Matrix.ext; unfold raw60 raw61; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1271 = raw61Labels := by decide +kernel
    rw [ha, hj, canonical61 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1274 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1274 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1274 node1274Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node149 node149Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw62 singletonSmall1274
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1274) = raw62Labels := by decide +kernel
  rw [hl, canonical62 B hB] at h
  have hc0 : mixedMoment B raw62 (Fin.cases (0 : Fin 1) singletonSmall1274) =
      mixedMoment B node149 node149Labels := by
    have ha : raw62 = raw63 := by apply Matrix.ext; unfold raw62 raw63; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1274 = raw63Labels := by decide +kernel
    rw [ha, hj, canonical63 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1275 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1275 node1275Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node100 node100Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw64 singletonSmall1275
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1275) = raw64Labels := by decide +kernel
  rw [hl, canonical64 B hB] at h
  have hc0 : mixedMoment B raw64 (Fin.cases (0 : Fin 1) singletonSmall1275) =
      mixedMoment B node100 node100Labels := by
    have ha : raw64 = raw65 := by apply Matrix.ext; unfold raw64 raw65; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1275 = raw65Labels := by decide +kernel
    rw [ha, hj, canonical65 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
