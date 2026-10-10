import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical1

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2563 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2563 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2563 node2563Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node199 node199Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw218 singletonSmall2563
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2563) = raw218Labels := by decide +kernel
  rw [hl, canonical218 B hB] at h
  have hc0 : mixedMoment B raw218 (Fin.cases (0 : Fin 1) singletonSmall2563) =
      mixedMoment B node199 node199Labels := by
    have ha : raw218 = raw219 := by apply Matrix.ext; unfold raw218 raw219; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2563 = raw219Labels := by decide +kernel
    rw [ha, hj, canonical219 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2570 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2570 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2570 node2570Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node326 node326Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw220 singletonSmall2570
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2570) = raw220Labels := by decide +kernel
  rw [hl, canonical220 B hB] at h
  have hc0 : mixedMoment B raw220 (Fin.cases (0 : Fin 1) singletonSmall2570) =
      mixedMoment B node326 node326Labels := by
    have ha : raw220 = raw221 := by apply Matrix.ext; unfold raw220 raw221; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2570 = raw221Labels := by decide +kernel
    rw [ha, hj, canonical221 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2572 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2572 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2572 node2572Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node305 node305Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw222 singletonSmall2572
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2572) = raw222Labels := by decide +kernel
  rw [hl, canonical222 B hB] at h
  have hc0 : mixedMoment B raw222 (Fin.cases (0 : Fin 1) singletonSmall2572) =
      mixedMoment B node305 node305Labels := by
    have ha : raw222 = raw223 := by apply Matrix.ext; unfold raw222 raw223; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2572 = raw223Labels := by decide +kernel
    rw [ha, hj, canonical223 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2574 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2574 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2574 node2574Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node224 node224Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw224 singletonSmall2574
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2574) = raw224Labels := by decide +kernel
  rw [hl, canonical224 B hB] at h
  have hc0 : mixedMoment B raw224 (Fin.cases (0 : Fin 1) singletonSmall2574) =
      mixedMoment B node224 node224Labels := by
    have ha : raw224 = raw225 := by apply Matrix.ext; unfold raw224 raw225; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2574 = raw225Labels := by decide +kernel
    rw [ha, hj, canonical225 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2576 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2576 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2576 node2576Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node329 node329Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw226 singletonSmall2576
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2576) = raw226Labels := by decide +kernel
  rw [hl, canonical226 B hB] at h
  have hc0 : mixedMoment B raw226 (Fin.cases (0 : Fin 1) singletonSmall2576) =
      mixedMoment B node329 node329Labels := by
    have ha : raw226 = raw227 := by apply Matrix.ext; unfold raw226 raw227; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2576 = raw227Labels := by decide +kernel
    rw [ha, hj, canonical227 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2581 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2581 node2581Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node203 node203Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw228 singletonSmall2581
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2581) = raw228Labels := by decide +kernel
  rw [hl, canonical228 B hB] at h
  have hc0 : mixedMoment B raw228 (Fin.cases (0 : Fin 1) singletonSmall2581) =
      mixedMoment B node203 node203Labels := by
    have ha : raw228 = raw229 := by apply Matrix.ext; unfold raw228 raw229; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2581 = raw229Labels := by decide +kernel
    rw [ha, hj, canonical229 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2593 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2593 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2593 node2593Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node334 node334Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw230 singletonSmall2593
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2593) = raw230Labels := by decide +kernel
  rw [hl, canonical230 B hB] at h
  have hc0 : mixedMoment B raw230 (Fin.cases (0 : Fin 1) singletonSmall2593) =
      mixedMoment B node334 node334Labels := by
    have ha : raw230 = raw231 := by apply Matrix.ext; unfold raw230 raw231; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2593 = raw231Labels := by decide +kernel
    rw [ha, hj, canonical231 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2594 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2594 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2594 node2594Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node335 node335Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw232 singletonSmall2594
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2594) = raw232Labels := by decide +kernel
  rw [hl, canonical232 B hB] at h
  have hc0 : mixedMoment B raw232 (Fin.cases (0 : Fin 1) singletonSmall2594) =
      mixedMoment B node335 node335Labels := by
    have ha : raw232 = raw233 := by apply Matrix.ext; unfold raw232 raw233; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2594 = raw233Labels := by decide +kernel
    rw [ha, hj, canonical233 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2595 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2595 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2595 node2595Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node336 node336Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw234 singletonSmall2595
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2595) = raw234Labels := by decide +kernel
  rw [hl, canonical234 B hB] at h
  have hc0 : mixedMoment B raw234 (Fin.cases (0 : Fin 1) singletonSmall2595) =
      mixedMoment B node336 node336Labels := by
    have ha : raw234 = raw235 := by apply Matrix.ext; unfold raw234 raw235; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2595 = raw235Labels := by decide +kernel
    rw [ha, hj, canonical235 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2596 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2596 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2596 node2596Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node337 node337Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw236 singletonSmall2596
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2596) = raw236Labels := by decide +kernel
  rw [hl, canonical236 B hB] at h
  have hc0 : mixedMoment B raw236 (Fin.cases (0 : Fin 1) singletonSmall2596) =
      mixedMoment B node337 node337Labels := by
    have ha : raw236 = raw237 := by apply Matrix.ext; unfold raw236 raw237; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2596 = raw237Labels := by decide +kernel
    rw [ha, hj, canonical237 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2598 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2598 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2598 node2598Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node338 node338Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw238 singletonSmall2598
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2598) = raw238Labels := by decide +kernel
  rw [hl, canonical238 B hB] at h
  have hc0 : mixedMoment B raw238 (Fin.cases (0 : Fin 1) singletonSmall2598) =
      mixedMoment B node338 node338Labels := by
    have ha : raw238 = raw239 := by apply Matrix.ext; unfold raw238 raw239; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2598 = raw239Labels := by decide +kernel
    rw [ha, hj, canonical239 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2599 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2599 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2599 node2599Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node339 node339Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw240 singletonSmall2599
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2599) = raw240Labels := by decide +kernel
  rw [hl, canonical240 B hB] at h
  have hc0 : mixedMoment B raw240 (Fin.cases (0 : Fin 1) singletonSmall2599) =
      mixedMoment B node339 node339Labels := by
    have ha : raw240 = raw241 := by apply Matrix.ext; unfold raw240 raw241; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2599 = raw241Labels := by decide +kernel
    rw [ha, hj, canonical241 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2601 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2601 node2601Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node341 node341Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw242 singletonSmall2601
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2601) = raw242Labels := by decide +kernel
  rw [hl, canonical242 B hB] at h
  have hc0 : mixedMoment B raw242 (Fin.cases (0 : Fin 1) singletonSmall2601) =
      mixedMoment B node341 node341Labels := by
    have ha : raw242 = raw243 := by apply Matrix.ext; unfold raw242 raw243; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2601 = raw243Labels := by decide +kernel
    rw [ha, hj, canonical243 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2602 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2602 node2602Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node249 node249Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw244 singletonSmall2602
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2602) = raw244Labels := by decide +kernel
  rw [hl, canonical244 B hB] at h
  have hc0 : mixedMoment B raw244 (Fin.cases (0 : Fin 1) singletonSmall2602) =
      mixedMoment B node249 node249Labels := by
    have ha : raw244 = raw245 := by apply Matrix.ext; unfold raw244 raw245; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2602 = raw245Labels := by decide +kernel
    rw [ha, hj, canonical245 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2604 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2604 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2604 node2604Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node343 node343Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw246 singletonSmall2604
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2604) = raw246Labels := by decide +kernel
  rw [hl, canonical246 B hB] at h
  have hc0 : mixedMoment B raw246 (Fin.cases (0 : Fin 1) singletonSmall2604) =
      mixedMoment B node343 node343Labels := by
    have ha : raw246 = raw247 := by apply Matrix.ext; unfold raw246 raw247; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2604 = raw247Labels := by decide +kernel
    rw [ha, hj, canonical247 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2605 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2605 node2605Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node344 node344Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw248 singletonSmall2605
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2605) = raw248Labels := by decide +kernel
  rw [hl, canonical248 B hB] at h
  have hc0 : mixedMoment B raw248 (Fin.cases (0 : Fin 1) singletonSmall2605) =
      mixedMoment B node344 node344Labels := by
    have ha : raw248 = raw249 := by apply Matrix.ext; unfold raw248 raw249; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2605 = raw249Labels := by decide +kernel
    rw [ha, hj, canonical249 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
