import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical3

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3200 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3200 node3200Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node215 node215Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw446 singletonSmall3200
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3200) = raw446Labels := by decide +kernel
  rw [hl, canonical446 B hB] at h
  have hc0 : mixedMoment B raw446 (Fin.cases (0 : Fin 1) singletonSmall3200) =
      mixedMoment B node215 node215Labels := by
    have ha : raw446 = raw447 := by apply Matrix.ext; unfold raw446 raw447; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3200 = raw447Labels := by decide +kernel
    rw [ha, hj, canonical447 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3201 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3201 node3201Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node217 node217Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw448 singletonSmall3201
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3201) = raw448Labels := by decide +kernel
  rw [hl, canonical448 B hB] at h
  have hc0 : mixedMoment B raw448 (Fin.cases (0 : Fin 1) singletonSmall3201) =
      mixedMoment B node217 node217Labels := by
    have ha : raw448 = raw449 := by apply Matrix.ext; unfold raw448 raw449; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3201 = raw449Labels := by decide +kernel
    rw [ha, hj, canonical449 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3203 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3203 node3203Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node223 node223Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw450 singletonSmall3203
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3203) = raw450Labels := by decide +kernel
  rw [hl, canonical450 B hB] at h
  have hc0 : mixedMoment B raw450 (Fin.cases (0 : Fin 1) singletonSmall3203) =
      mixedMoment B node223 node223Labels := by
    have ha : raw450 = raw451 := by apply Matrix.ext; unfold raw450 raw451; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3203 = raw451Labels := by decide +kernel
    rw [ha, hj, canonical451 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3204 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3204 node3204Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node221 node221Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw452 singletonSmall3204
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3204) = raw452Labels := by decide +kernel
  rw [hl, canonical452 B hB] at h
  have hc0 : mixedMoment B raw452 (Fin.cases (0 : Fin 1) singletonSmall3204) =
      mixedMoment B node221 node221Labels := by
    have ha : raw452 = raw453 := by apply Matrix.ext; unfold raw452 raw453; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3204 = raw453Labels := by decide +kernel
    rw [ha, hj, canonical453 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3205 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3205 node3205Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node220 node220Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw454 singletonSmall3205
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3205) = raw454Labels := by decide +kernel
  rw [hl, canonical454 B hB] at h
  have hc0 : mixedMoment B raw454 (Fin.cases (0 : Fin 1) singletonSmall3205) =
      mixedMoment B node220 node220Labels := by
    have ha : raw454 = raw455 := by apply Matrix.ext; unfold raw454 raw455; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3205 = raw455Labels := by decide +kernel
    rw [ha, hj, canonical455 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3206 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3206 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3206 node3206Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node226 node226Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw456 singletonSmall3206
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3206) = raw456Labels := by decide +kernel
  rw [hl, canonical456 B hB] at h
  have hc0 : mixedMoment B raw456 (Fin.cases (0 : Fin 1) singletonSmall3206) =
      mixedMoment B node226 node226Labels := by
    have ha : raw456 = raw457 := by apply Matrix.ext; unfold raw456 raw457; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3206 = raw457Labels := by decide +kernel
    rw [ha, hj, canonical457 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3207 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3207 node3207Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node227 node227Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw458 singletonSmall3207
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3207) = raw458Labels := by decide +kernel
  rw [hl, canonical458 B hB] at h
  have hc0 : mixedMoment B raw458 (Fin.cases (0 : Fin 1) singletonSmall3207) =
      mixedMoment B node227 node227Labels := by
    have ha : raw458 = raw459 := by apply Matrix.ext; unfold raw458 raw459; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3207 = raw459Labels := by decide +kernel
    rw [ha, hj, canonical459 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3209 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3209 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3209 node3209Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node232 node232Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw460 singletonSmall3209
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3209) = raw460Labels := by decide +kernel
  rw [hl, canonical460 B hB] at h
  have hc0 : mixedMoment B raw460 (Fin.cases (0 : Fin 1) singletonSmall3209) =
      mixedMoment B node232 node232Labels := by
    have ha : raw460 = raw461 := by apply Matrix.ext; unfold raw460 raw461; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3209 = raw461Labels := by decide +kernel
    rw [ha, hj, canonical461 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3210 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3210 node3210Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node235 node235Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw462 singletonSmall3210
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3210) = raw462Labels := by decide +kernel
  rw [hl, canonical462 B hB] at h
  have hc0 : mixedMoment B raw462 (Fin.cases (0 : Fin 1) singletonSmall3210) =
      mixedMoment B node235 node235Labels := by
    have ha : raw462 = raw463 := by apply Matrix.ext; unfold raw462 raw463; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3210 = raw463Labels := by decide +kernel
    rw [ha, hj, canonical463 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3211 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3211 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3211 node3211Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node234 node234Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw464 singletonSmall3211
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3211) = raw464Labels := by decide +kernel
  rw [hl, canonical464 B hB] at h
  have hc0 : mixedMoment B raw464 (Fin.cases (0 : Fin 1) singletonSmall3211) =
      mixedMoment B node234 node234Labels := by
    have ha : raw464 = raw465 := by apply Matrix.ext; unfold raw464 raw465; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3211 = raw465Labels := by decide +kernel
    rw [ha, hj, canonical465 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3218 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3218 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3218 node3218Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node200 node200Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw466 singletonSmall3218
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3218) = raw466Labels := by decide +kernel
  rw [hl, canonical466 B hB] at h
  have hc0 : mixedMoment B raw466 (Fin.cases (0 : Fin 1) singletonSmall3218) =
      mixedMoment B node200 node200Labels := by
    have ha : raw466 = raw467 := by apply Matrix.ext; unfold raw466 raw467; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3218 = raw467Labels := by decide +kernel
    rw [ha, hj, canonical467 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3219 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3219 node3219Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node204 node204Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw468 singletonSmall3219
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3219) = raw468Labels := by decide +kernel
  rw [hl, canonical468 B hB] at h
  have hc0 : mixedMoment B raw468 (Fin.cases (0 : Fin 1) singletonSmall3219) =
      mixedMoment B node204 node204Labels := by
    have ha : raw468 = raw469 := by apply Matrix.ext; unfold raw468 raw469; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3219 = raw469Labels := by decide +kernel
    rw [ha, hj, canonical469 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3223 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3223 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3223 node3223Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node261 node261Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw470 singletonSmall3223
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3223) = raw470Labels := by decide +kernel
  rw [hl, canonical470 B hB] at h
  have hc0 : mixedMoment B raw470 (Fin.cases (0 : Fin 1) singletonSmall3223) =
      mixedMoment B node261 node261Labels := by
    have ha : raw470 = raw471 := by apply Matrix.ext; unfold raw470 raw471; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3223 = raw471Labels := by decide +kernel
    rw [ha, hj, canonical471 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3224 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3224 node3224Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node269 node269Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw472 singletonSmall3224
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3224) = raw472Labels := by decide +kernel
  rw [hl, canonical472 B hB] at h
  have hc0 : mixedMoment B raw472 (Fin.cases (0 : Fin 1) singletonSmall3224) =
      mixedMoment B node269 node269Labels := by
    have ha : raw472 = raw473 := by apply Matrix.ext; unfold raw472 raw473; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3224 = raw473Labels := by decide +kernel
    rw [ha, hj, canonical473 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3225 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3225 node3225Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node268 node268Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw474 singletonSmall3225
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3225) = raw474Labels := by decide +kernel
  rw [hl, canonical474 B hB] at h
  have hc0 : mixedMoment B raw474 (Fin.cases (0 : Fin 1) singletonSmall3225) =
      mixedMoment B node268 node268Labels := by
    have ha : raw474 = raw475 := by apply Matrix.ext; unfold raw474 raw475; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3225 = raw475Labels := by decide +kernel
    rw [ha, hj, canonical475 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3226 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3226 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3226 node3226Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node259 node259Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw476 singletonSmall3226
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3226) = raw476Labels := by decide +kernel
  rw [hl, canonical476 B hB] at h
  have hc0 : mixedMoment B raw476 (Fin.cases (0 : Fin 1) singletonSmall3226) =
      mixedMoment B node259 node259Labels := by
    have ha : raw476 = raw477 := by apply Matrix.ext; unfold raw476 raw477; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3226 = raw477Labels := by decide +kernel
    rw [ha, hj, canonical477 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3227 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3227 node3227Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node260 node260Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw478 singletonSmall3227
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3227) = raw478Labels := by decide +kernel
  rw [hl, canonical478 B hB] at h
  have hc0 : mixedMoment B raw478 (Fin.cases (0 : Fin 1) singletonSmall3227) =
      mixedMoment B node260 node260Labels := by
    have ha : raw478 = raw479 := by apply Matrix.ext; unfold raw478 raw479; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3227 = raw479Labels := by decide +kernel
    rw [ha, hj, canonical479 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
