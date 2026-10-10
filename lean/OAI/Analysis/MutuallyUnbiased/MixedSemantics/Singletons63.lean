import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical5

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4032 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4032 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4032 node4032Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node478 node478Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw648 singletonSmall4032
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4032) = raw648Labels := by decide +kernel
  rw [hl, canonical648 B hB] at h
  have hc0 : mixedMoment B raw648 (Fin.cases (0 : Fin 1) singletonSmall4032) =
      mixedMoment B node478 node478Labels := by
    have ha : raw648 = raw649 := by apply Matrix.ext; unfold raw648 raw649; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4032 = raw649Labels := by decide +kernel
    rw [ha, hj, canonical649 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4033 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4033 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4033 node4033Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node488 node488Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw650 singletonSmall4033
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4033) = raw650Labels := by decide +kernel
  rw [hl, canonical650 B hB] at h
  have hc0 : mixedMoment B raw650 (Fin.cases (0 : Fin 1) singletonSmall4033) =
      mixedMoment B node488 node488Labels := by
    have ha : raw650 = raw651 := by apply Matrix.ext; unfold raw650 raw651; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4033 = raw651Labels := by decide +kernel
    rw [ha, hj, canonical651 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4039 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4039 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4039 node4039Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node504 node504Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw652 singletonSmall4039
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4039) = raw652Labels := by decide +kernel
  rw [hl, canonical652 B hB] at h
  have hc0 : mixedMoment B raw652 (Fin.cases (0 : Fin 1) singletonSmall4039) =
      mixedMoment B node504 node504Labels := by
    have ha : raw652 = raw653 := by apply Matrix.ext; unfold raw652 raw653; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4039 = raw653Labels := by decide +kernel
    rw [ha, hj, canonical653 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4050 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4050 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4050 node4050Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node526 node526Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw654 singletonSmall4050
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4050) = raw654Labels := by decide +kernel
  rw [hl, canonical654 B hB] at h
  have hc0 : mixedMoment B raw654 (Fin.cases (0 : Fin 1) singletonSmall4050) =
      mixedMoment B node526 node526Labels := by
    have ha : raw654 = raw655 := by apply Matrix.ext; unfold raw654 raw655; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4050 = raw655Labels := by decide +kernel
    rw [ha, hj, canonical655 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4051 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4051 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4051 node4051Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node531 node531Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw656 singletonSmall4051
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4051) = raw656Labels := by decide +kernel
  rw [hl, canonical656 B hB] at h
  have hc0 : mixedMoment B raw656 (Fin.cases (0 : Fin 1) singletonSmall4051) =
      mixedMoment B node531 node531Labels := by
    have ha : raw656 = raw657 := by apply Matrix.ext; unfold raw656 raw657; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4051 = raw657Labels := by decide +kernel
    rw [ha, hj, canonical657 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4053 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4053 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4053 node4053Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node533 node533Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw658 singletonSmall4053
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4053) = raw658Labels := by decide +kernel
  rw [hl, canonical658 B hB] at h
  have hc0 : mixedMoment B raw658 (Fin.cases (0 : Fin 1) singletonSmall4053) =
      mixedMoment B node533 node533Labels := by
    have ha : raw658 = raw659 := by apply Matrix.ext; unfold raw658 raw659; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4053 = raw659Labels := by decide +kernel
    rw [ha, hj, canonical659 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4093 : Fin 1 → Fin 1 := ![0]

theorem singleton4093 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4093 node4093Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node5 node5Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw660 singletonSmall4093
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4093) = raw660Labels := by decide +kernel
  rw [hl, canonical660 B hB] at h
  have hc0 : mixedMoment B raw660 (Fin.cases (0 : Fin 1) singletonSmall4093) =
      mixedMoment B node5 node5Labels := by
    have ha : raw660 = raw661 := by apply Matrix.ext; unfold raw660 raw661; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4093 = raw661Labels := by decide +kernel
    rw [ha, hj, canonical661 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4094 : Fin 1 → Fin 1 := ![0]

theorem singleton4094 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4094 node4094Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node6 node6Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw662 singletonSmall4094
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4094) = raw662Labels := by decide +kernel
  rw [hl, canonical662 B hB] at h
  have hc0 : mixedMoment B raw662 (Fin.cases (0 : Fin 1) singletonSmall4094) =
      mixedMoment B node6 node6Labels := by
    have ha : raw662 = raw663 := by apply Matrix.ext; unfold raw662 raw663; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4094 = raw663Labels := by decide +kernel
    rw [ha, hj, canonical663 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
