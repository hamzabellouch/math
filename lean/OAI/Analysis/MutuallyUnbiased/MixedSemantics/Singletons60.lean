import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical4

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3847 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3847 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3847 node3847Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node462 node462Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw522 singletonSmall3847
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3847) = raw522Labels := by decide +kernel
  rw [hl, canonical522 B hB] at h
  have hc0 : mixedMoment B raw522 (Fin.cases (0 : Fin 1) singletonSmall3847) =
      mixedMoment B node462 node462Labels := by
    have ha : raw522 = raw523 := by apply Matrix.ext; unfold raw522 raw523; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3847 = raw523Labels := by decide +kernel
    rw [ha, hj, canonical523 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3851 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3851 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3851 node3851Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node488 node488Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw524 singletonSmall3851
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3851) = raw524Labels := by decide +kernel
  rw [hl, canonical524 B hB] at h
  have hc0 : mixedMoment B raw524 (Fin.cases (0 : Fin 1) singletonSmall3851) =
      mixedMoment B node488 node488Labels := by
    have ha : raw524 = raw525 := by apply Matrix.ext; unfold raw524 raw525; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3851 = raw525Labels := by decide +kernel
    rw [ha, hj, canonical525 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3852 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3852 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3852 node3852Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node489 node489Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw526 singletonSmall3852
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3852) = raw526Labels := by decide +kernel
  rw [hl, canonical526 B hB] at h
  have hc0 : mixedMoment B raw526 (Fin.cases (0 : Fin 1) singletonSmall3852) =
      mixedMoment B node489 node489Labels := by
    have ha : raw526 = raw527 := by apply Matrix.ext; unfold raw526 raw527; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3852 = raw527Labels := by decide +kernel
    rw [ha, hj, canonical527 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3853 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3853 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3853 node3853Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node490 node490Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw528 singletonSmall3853
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3853) = raw528Labels := by decide +kernel
  rw [hl, canonical528 B hB] at h
  have hc0 : mixedMoment B raw528 (Fin.cases (0 : Fin 1) singletonSmall3853) =
      mixedMoment B node490 node490Labels := by
    have ha : raw528 = raw529 := by apply Matrix.ext; unfold raw528 raw529; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3853 = raw529Labels := by decide +kernel
    rw [ha, hj, canonical529 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3855 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3855 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3855 node3855Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node492 node492Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw530 singletonSmall3855
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3855) = raw530Labels := by decide +kernel
  rw [hl, canonical530 B hB] at h
  have hc0 : mixedMoment B raw530 (Fin.cases (0 : Fin 1) singletonSmall3855) =
      mixedMoment B node492 node492Labels := by
    have ha : raw530 = raw531 := by apply Matrix.ext; unfold raw530 raw531; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3855 = raw531Labels := by decide +kernel
    rw [ha, hj, canonical531 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3856 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3856 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3856 node3856Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node468 node468Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw532 singletonSmall3856
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3856) = raw532Labels := by decide +kernel
  rw [hl, canonical532 B hB] at h
  have hc0 : mixedMoment B raw532 (Fin.cases (0 : Fin 1) singletonSmall3856) =
      mixedMoment B node468 node468Labels := by
    have ha : raw532 = raw533 := by apply Matrix.ext; unfold raw532 raw533; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3856 = raw533Labels := by decide +kernel
    rw [ha, hj, canonical533 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3858 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3858 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3858 node3858Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node494 node494Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw534 singletonSmall3858
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3858) = raw534Labels := by decide +kernel
  rw [hl, canonical534 B hB] at h
  have hc0 : mixedMoment B raw534 (Fin.cases (0 : Fin 1) singletonSmall3858) =
      mixedMoment B node494 node494Labels := by
    have ha : raw534 = raw535 := by apply Matrix.ext; unfold raw534 raw535; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3858 = raw535Labels := by decide +kernel
    rw [ha, hj, canonical535 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3862 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3862 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3862 node3862Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node496 node496Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw536 singletonSmall3862
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3862) = raw536Labels := by decide +kernel
  rw [hl, canonical536 B hB] at h
  have hc0 : mixedMoment B raw536 (Fin.cases (0 : Fin 1) singletonSmall3862) =
      mixedMoment B node496 node496Labels := by
    have ha : raw536 = raw537 := by apply Matrix.ext; unfold raw536 raw537; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3862 = raw537Labels := by decide +kernel
    rw [ha, hj, canonical537 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3882 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3882 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3882 node3882Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node499 node499Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw538 singletonSmall3882
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3882) = raw538Labels := by decide +kernel
  rw [hl, canonical538 B hB] at h
  have hc0 : mixedMoment B raw538 (Fin.cases (0 : Fin 1) singletonSmall3882) =
      mixedMoment B node499 node499Labels := by
    have ha : raw538 = raw539 := by apply Matrix.ext; unfold raw538 raw539; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3882 = raw539Labels := by decide +kernel
    rw [ha, hj, canonical539 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3883 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3883 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3883 node3883Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node467 node467Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw540 singletonSmall3883
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3883) = raw540Labels := by decide +kernel
  rw [hl, canonical540 B hB] at h
  have hc0 : mixedMoment B raw540 (Fin.cases (0 : Fin 1) singletonSmall3883) =
      mixedMoment B node467 node467Labels := by
    have ha : raw540 = raw541 := by apply Matrix.ext; unfold raw540 raw541; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3883 = raw541Labels := by decide +kernel
    rw [ha, hj, canonical541 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3887 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3887 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3887 node3887Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node502 node502Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw542 singletonSmall3887
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3887) = raw542Labels := by decide +kernel
  rw [hl, canonical542 B hB] at h
  have hc0 : mixedMoment B raw542 (Fin.cases (0 : Fin 1) singletonSmall3887) =
      mixedMoment B node502 node502Labels := by
    have ha : raw542 = raw543 := by apply Matrix.ext; unfold raw542 raw543; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3887 = raw543Labels := by decide +kernel
    rw [ha, hj, canonical543 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3888 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3888 node3888Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node503 node503Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw544 singletonSmall3888
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3888) = raw544Labels := by decide +kernel
  rw [hl, canonical544 B hB] at h
  have hc0 : mixedMoment B raw544 (Fin.cases (0 : Fin 1) singletonSmall3888) =
      mixedMoment B node503 node503Labels := by
    have ha : raw544 = raw545 := by apply Matrix.ext; unfold raw544 raw545; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3888 = raw545Labels := by decide +kernel
    rw [ha, hj, canonical545 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3889 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3889 node3889Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node496 node496Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw546 singletonSmall3889
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3889) = raw546Labels := by decide +kernel
  rw [hl, canonical546 B hB] at h
  have hc0 : mixedMoment B raw546 (Fin.cases (0 : Fin 1) singletonSmall3889) =
      mixedMoment B node496 node496Labels := by
    have ha : raw546 = raw547 := by apply Matrix.ext; unfold raw546 raw547; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3889 = raw547Labels := by decide +kernel
    rw [ha, hj, canonical547 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
