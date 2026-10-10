import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical1

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2526 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2526 node2526Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node294 node294Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw206 singletonSmall2526
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2526) = raw206Labels := by decide +kernel
  rw [hl, canonical206 B hB] at h
  have hc0 : mixedMoment B raw206 (Fin.cases (0 : Fin 1) singletonSmall2526) =
      mixedMoment B node294 node294Labels := by
    have ha : raw206 = raw207 := by apply Matrix.ext; unfold raw206 raw207; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2526 = raw207Labels := by decide +kernel
    rw [ha, hj, canonical207 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2527 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2527 node2527Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node317 node317Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw208 singletonSmall2527
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2527) = raw208Labels := by decide +kernel
  rw [hl, canonical208 B hB] at h
  have hc0 : mixedMoment B raw208 (Fin.cases (0 : Fin 1) singletonSmall2527) =
      mixedMoment B node317 node317Labels := by
    have ha : raw208 = raw209 := by apply Matrix.ext; unfold raw208 raw209; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2527 = raw209Labels := by decide +kernel
    rw [ha, hj, canonical209 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2528 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2528 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2528 node2528Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node207 node207Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw210 singletonSmall2528
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2528) = raw210Labels := by decide +kernel
  rw [hl, canonical210 B hB] at h
  have hc0 : mixedMoment B raw210 (Fin.cases (0 : Fin 1) singletonSmall2528) =
      mixedMoment B node207 node207Labels := by
    have ha : raw210 = raw211 := by apply Matrix.ext; unfold raw210 raw211; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2528 = raw211Labels := by decide +kernel
    rw [ha, hj, canonical211 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2530 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2530 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2530 node2530Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node318 node318Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw212 singletonSmall2530
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2530) = raw212Labels := by decide +kernel
  rw [hl, canonical212 B hB] at h
  have hc0 : mixedMoment B raw212 (Fin.cases (0 : Fin 1) singletonSmall2530) =
      mixedMoment B node318 node318Labels := by
    have ha : raw212 = raw213 := by apply Matrix.ext; unfold raw212 raw213; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2530 = raw213Labels := by decide +kernel
    rw [ha, hj, canonical213 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2531 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2531 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2531 node2531Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node274 node274Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw214 singletonSmall2531
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2531) = raw214Labels := by decide +kernel
  rw [hl, canonical214 B hB] at h
  have hc0 : mixedMoment B raw214 (Fin.cases (0 : Fin 1) singletonSmall2531) =
      mixedMoment B node274 node274Labels := by
    have ha : raw214 = raw215 := by apply Matrix.ext; unfold raw214 raw215; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2531 = raw215Labels := by decide +kernel
    rw [ha, hj, canonical215 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2532 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2532 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2532 node2532Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node180 node180Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw216 singletonSmall2532
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2532) = raw216Labels := by decide +kernel
  rw [hl, canonical216 B hB] at h
  have hc0 : mixedMoment B raw216 (Fin.cases (0 : Fin 1) singletonSmall2532) =
      mixedMoment B node180 node180Labels := by
    have ha : raw216 = raw217 := by apply Matrix.ext; unfold raw216 raw217; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2532 = raw217Labels := by decide +kernel
    rw [ha, hj, canonical217 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
