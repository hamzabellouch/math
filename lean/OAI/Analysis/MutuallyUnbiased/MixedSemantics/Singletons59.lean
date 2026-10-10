import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical4

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3818 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3818 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3818 node3818Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node431 node431Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw504 singletonSmall3818
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3818) = raw504Labels := by decide +kernel
  rw [hl, canonical504 B hB] at h
  have hc0 : mixedMoment B raw504 (Fin.cases (0 : Fin 1) singletonSmall3818) =
      mixedMoment B node431 node431Labels := by
    have ha : raw504 = raw505 := by apply Matrix.ext; unfold raw504 raw505; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3818 = raw505Labels := by decide +kernel
    rw [ha, hj, canonical505 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3820 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3820 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3820 node3820Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node471 node471Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw506 singletonSmall3820
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3820) = raw506Labels := by decide +kernel
  rw [hl, canonical506 B hB] at h
  have hc0 : mixedMoment B raw506 (Fin.cases (0 : Fin 1) singletonSmall3820) =
      mixedMoment B node471 node471Labels := by
    have ha : raw506 = raw507 := by apply Matrix.ext; unfold raw506 raw507; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3820 = raw507Labels := by decide +kernel
    rw [ha, hj, canonical507 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3821 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3821 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3821 node3821Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node472 node472Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw508 singletonSmall3821
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3821) = raw508Labels := by decide +kernel
  rw [hl, canonical508 B hB] at h
  have hc0 : mixedMoment B raw508 (Fin.cases (0 : Fin 1) singletonSmall3821) =
      mixedMoment B node472 node472Labels := by
    have ha : raw508 = raw509 := by apply Matrix.ext; unfold raw508 raw509; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3821 = raw509Labels := by decide +kernel
    rw [ha, hj, canonical509 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3822 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3822 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3822 node3822Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node459 node459Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw510 singletonSmall3822
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3822) = raw510Labels := by decide +kernel
  rw [hl, canonical510 B hB] at h
  have hc0 : mixedMoment B raw510 (Fin.cases (0 : Fin 1) singletonSmall3822) =
      mixedMoment B node459 node459Labels := by
    have ha : raw510 = raw511 := by apply Matrix.ext; unfold raw510 raw511; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3822 = raw511Labels := by decide +kernel
    rw [ha, hj, canonical511 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3823 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3823 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3823 node3823Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node473 node473Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw512 singletonSmall3823
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3823) = raw512Labels := by decide +kernel
  rw [hl, canonical512 B hB] at h
  have hc0 : mixedMoment B raw512 (Fin.cases (0 : Fin 1) singletonSmall3823) =
      mixedMoment B node473 node473Labels := by
    have ha : raw512 = raw513 := by apply Matrix.ext; unfold raw512 raw513; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3823 = raw513Labels := by decide +kernel
    rw [ha, hj, canonical513 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3824 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3824 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3824 node3824Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node474 node474Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw514 singletonSmall3824
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3824) = raw514Labels := by decide +kernel
  rw [hl, canonical514 B hB] at h
  have hc0 : mixedMoment B raw514 (Fin.cases (0 : Fin 1) singletonSmall3824) =
      mixedMoment B node474 node474Labels := by
    have ha : raw514 = raw515 := by apply Matrix.ext; unfold raw514 raw515; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3824 = raw515Labels := by decide +kernel
    rw [ha, hj, canonical515 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3829 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3829 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3829 node3829Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node477 node477Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw516 singletonSmall3829
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3829) = raw516Labels := by decide +kernel
  rw [hl, canonical516 B hB] at h
  have hc0 : mixedMoment B raw516 (Fin.cases (0 : Fin 1) singletonSmall3829) =
      mixedMoment B node477 node477Labels := by
    have ha : raw516 = raw517 := by apply Matrix.ext; unfold raw516 raw517; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3829 = raw517Labels := by decide +kernel
    rw [ha, hj, canonical517 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3830 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3830 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3830 node3830Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node455 node455Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw518 singletonSmall3830
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3830) = raw518Labels := by decide +kernel
  rw [hl, canonical518 B hB] at h
  have hc0 : mixedMoment B raw518 (Fin.cases (0 : Fin 1) singletonSmall3830) =
      mixedMoment B node455 node455Labels := by
    have ha : raw518 = raw519 := by apply Matrix.ext; unfold raw518 raw519; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3830 = raw519Labels := by decide +kernel
    rw [ha, hj, canonical519 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3831 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3831 node3831Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node438 node438Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw520 singletonSmall3831
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3831) = raw520Labels := by decide +kernel
  rw [hl, canonical520 B hB] at h
  have hc0 : mixedMoment B raw520 (Fin.cases (0 : Fin 1) singletonSmall3831) =
      mixedMoment B node438 node438Labels := by
    have ha : raw520 = raw521 := by apply Matrix.ext; unfold raw520 raw521; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3831 = raw521Labels := by decide +kernel
    rw [ha, hj, canonical521 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
