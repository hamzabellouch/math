import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical3

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3726 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3726 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3726 node3726Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node442 node442Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw482 singletonSmall3726
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3726) = raw482Labels := by decide +kernel
  rw [hl, canonical482 B hB] at h
  have hc0 : mixedMoment B raw482 (Fin.cases (0 : Fin 1) singletonSmall3726) =
      mixedMoment B node442 node442Labels := by
    have ha : raw482 = raw483 := by apply Matrix.ext; unfold raw482 raw483; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3726 = raw483Labels := by decide +kernel
    rw [ha, hj, canonical483 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3727 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3727 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3727 node3727Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node441 node441Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw484 singletonSmall3727
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3727) = raw484Labels := by decide +kernel
  rw [hl, canonical484 B hB] at h
  have hc0 : mixedMoment B raw484 (Fin.cases (0 : Fin 1) singletonSmall3727) =
      mixedMoment B node441 node441Labels := by
    have ha : raw484 = raw485 := by apply Matrix.ext; unfold raw484 raw485; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3727 = raw485Labels := by decide +kernel
    rw [ha, hj, canonical485 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3728 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3728 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3728 node3728Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node432 node432Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw486 singletonSmall3728
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3728) = raw486Labels := by decide +kernel
  rw [hl, canonical486 B hB] at h
  have hc0 : mixedMoment B raw486 (Fin.cases (0 : Fin 1) singletonSmall3728) =
      mixedMoment B node432 node432Labels := by
    have ha : raw486 = raw487 := by apply Matrix.ext; unfold raw486 raw487; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3728 = raw487Labels := by decide +kernel
    rw [ha, hj, canonical487 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3734 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3734 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3734 node3734Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node445 node445Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw488 singletonSmall3734
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3734) = raw488Labels := by decide +kernel
  rw [hl, canonical488 B hB] at h
  have hc0 : mixedMoment B raw488 (Fin.cases (0 : Fin 1) singletonSmall3734) =
      mixedMoment B node445 node445Labels := by
    have ha : raw488 = raw489 := by apply Matrix.ext; unfold raw488 raw489; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3734 = raw489Labels := by decide +kernel
    rw [ha, hj, canonical489 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3735 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3735 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3735 node3735Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node448 node448Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw490 singletonSmall3735
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3735) = raw490Labels := by decide +kernel
  rw [hl, canonical490 B hB] at h
  have hc0 : mixedMoment B raw490 (Fin.cases (0 : Fin 1) singletonSmall3735) =
      mixedMoment B node448 node448Labels := by
    have ha : raw490 = raw491 := by apply Matrix.ext; unfold raw490 raw491; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3735 = raw491Labels := by decide +kernel
    rw [ha, hj, canonical491 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3736 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3736 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3736 node3736Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node449 node449Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw492 singletonSmall3736
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3736) = raw492Labels := by decide +kernel
  rw [hl, canonical492 B hB] at h
  have hc0 : mixedMoment B raw492 (Fin.cases (0 : Fin 1) singletonSmall3736) =
      mixedMoment B node449 node449Labels := by
    have ha : raw492 = raw493 := by apply Matrix.ext; unfold raw492 raw493; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3736 = raw493Labels := by decide +kernel
    rw [ha, hj, canonical493 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3737 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3737 node3737Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node450 node450Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw494 singletonSmall3737
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3737) = raw494Labels := by decide +kernel
  rw [hl, canonical494 B hB] at h
  have hc0 : mixedMoment B raw494 (Fin.cases (0 : Fin 1) singletonSmall3737) =
      mixedMoment B node450 node450Labels := by
    have ha : raw494 = raw495 := by apply Matrix.ext; unfold raw494 raw495; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3737 = raw495Labels := by decide +kernel
    rw [ha, hj, canonical495 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3738 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3738 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3738 node3738Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node446 node446Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw496 singletonSmall3738
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3738) = raw496Labels := by decide +kernel
  rw [hl, canonical496 B hB] at h
  have hc0 : mixedMoment B raw496 (Fin.cases (0 : Fin 1) singletonSmall3738) =
      mixedMoment B node446 node446Labels := by
    have ha : raw496 = raw497 := by apply Matrix.ext; unfold raw496 raw497; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3738 = raw497Labels := by decide +kernel
    rw [ha, hj, canonical497 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3739 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3739 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3739 node3739Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node449 node449Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw498 singletonSmall3739
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3739) = raw498Labels := by decide +kernel
  rw [hl, canonical498 B hB] at h
  have hc0 : mixedMoment B raw498 (Fin.cases (0 : Fin 1) singletonSmall3739) =
      mixedMoment B node449 node449Labels := by
    have ha : raw498 = raw499 := by apply Matrix.ext; unfold raw498 raw499; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3739 = raw499Labels := by decide +kernel
    rw [ha, hj, canonical499 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3740 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3740 node3740Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node451 node451Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw500 singletonSmall3740
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3740) = raw500Labels := by decide +kernel
  rw [hl, canonical500 B hB] at h
  have hc0 : mixedMoment B raw500 (Fin.cases (0 : Fin 1) singletonSmall3740) =
      mixedMoment B node451 node451Labels := by
    have ha : raw500 = raw501 := by apply Matrix.ext; unfold raw500 raw501; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3740 = raw501Labels := by decide +kernel
    rw [ha, hj, canonical501 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3741 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3741 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3741 node3741Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node452 node452Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw502 singletonSmall3741
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3741) = raw502Labels := by decide +kernel
  rw [hl, canonical502 B hB] at h
  have hc0 : mixedMoment B raw502 (Fin.cases (0 : Fin 1) singletonSmall3741) =
      mixedMoment B node452 node452Labels := by
    have ha : raw502 = raw503 := by apply Matrix.ext; unfold raw502 raw503; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3741 = raw503Labels := by decide +kernel
    rw [ha, hj, canonical503 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
