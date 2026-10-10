import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical1

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2357 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2357 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2357 node2357Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node284 node284Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw196 singletonSmall2357
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2357) = raw196Labels := by decide +kernel
  rw [hl, canonical196 B hB] at h
  have hc0 : mixedMoment B raw196 (Fin.cases (0 : Fin 1) singletonSmall2357) =
      mixedMoment B node284 node284Labels := by
    have ha : raw196 = raw197 := by apply Matrix.ext; unfold raw196 raw197; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2357 = raw197Labels := by decide +kernel
    rw [ha, hj, canonical197 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2358 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2358 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2358 node2358Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node285 node285Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw198 singletonSmall2358
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2358) = raw198Labels := by decide +kernel
  rw [hl, canonical198 B hB] at h
  have hc0 : mixedMoment B raw198 (Fin.cases (0 : Fin 1) singletonSmall2358) =
      mixedMoment B node285 node285Labels := by
    have ha : raw198 = raw199 := by apply Matrix.ext; unfold raw198 raw199; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2358 = raw199Labels := by decide +kernel
    rw [ha, hj, canonical199 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2359 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2359 node2359Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node286 node286Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw200 singletonSmall2359
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2359) = raw200Labels := by decide +kernel
  rw [hl, canonical200 B hB] at h
  have hc0 : mixedMoment B raw200 (Fin.cases (0 : Fin 1) singletonSmall2359) =
      mixedMoment B node286 node286Labels := by
    have ha : raw200 = raw201 := by apply Matrix.ext; unfold raw200 raw201; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2359 = raw201Labels := by decide +kernel
    rw [ha, hj, canonical201 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2360 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2360 node2360Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node287 node287Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw202 singletonSmall2360
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2360) = raw202Labels := by decide +kernel
  rw [hl, canonical202 B hB] at h
  have hc0 : mixedMoment B raw202 (Fin.cases (0 : Fin 1) singletonSmall2360) =
      mixedMoment B node287 node287Labels := by
    have ha : raw202 = raw203 := by apply Matrix.ext; unfold raw202 raw203; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2360 = raw203Labels := by decide +kernel
    rw [ha, hj, canonical203 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2363 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2363 node2363Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node187 node187Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw204 singletonSmall2363
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2363) = raw204Labels := by decide +kernel
  rw [hl, canonical204 B hB] at h
  have hc0 : mixedMoment B raw204 (Fin.cases (0 : Fin 1) singletonSmall2363) =
      mixedMoment B node187 node187Labels := by
    have ha : raw204 = raw205 := by apply Matrix.ext; unfold raw204 raw205; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2363 = raw205Labels := by decide +kernel
    rw [ha, hj, canonical205 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
