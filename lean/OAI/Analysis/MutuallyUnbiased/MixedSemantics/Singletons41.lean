import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical2

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2626 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2626 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2626 node2626Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node201 node201Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw250 singletonSmall2626
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2626) = raw250Labels := by decide +kernel
  rw [hl, canonical250 B hB] at h
  have hc0 : mixedMoment B raw250 (Fin.cases (0 : Fin 1) singletonSmall2626) =
      mixedMoment B node201 node201Labels := by
    have ha : raw250 = raw251 := by apply Matrix.ext; unfold raw250 raw251; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2626 = raw251Labels := by decide +kernel
    rw [ha, hj, canonical251 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2636 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2636 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2636 node2636Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node351 node351Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw252 singletonSmall2636
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2636) = raw252Labels := by decide +kernel
  rw [hl, canonical252 B hB] at h
  have hc0 : mixedMoment B raw252 (Fin.cases (0 : Fin 1) singletonSmall2636) =
      mixedMoment B node351 node351Labels := by
    have ha : raw252 = raw253 := by apply Matrix.ext; unfold raw252 raw253; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2636 = raw253Labels := by decide +kernel
    rw [ha, hj, canonical253 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2637 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2637 node2637Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node352 node352Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw254 singletonSmall2637
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2637) = raw254Labels := by decide +kernel
  rw [hl, canonical254 B hB] at h
  have hc0 : mixedMoment B raw254 (Fin.cases (0 : Fin 1) singletonSmall2637) =
      mixedMoment B node352 node352Labels := by
    have ha : raw254 = raw255 := by apply Matrix.ext; unfold raw254 raw255; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2637 = raw255Labels := by decide +kernel
    rw [ha, hj, canonical255 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2638 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2638 node2638Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node353 node353Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw256 singletonSmall2638
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2638) = raw256Labels := by decide +kernel
  rw [hl, canonical256 B hB] at h
  have hc0 : mixedMoment B raw256 (Fin.cases (0 : Fin 1) singletonSmall2638) =
      mixedMoment B node353 node353Labels := by
    have ha : raw256 = raw257 := by apply Matrix.ext; unfold raw256 raw257; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2638 = raw257Labels := by decide +kernel
    rw [ha, hj, canonical257 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2640 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2640 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2640 node2640Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node315 node315Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw258 singletonSmall2640
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2640) = raw258Labels := by decide +kernel
  rw [hl, canonical258 B hB] at h
  have hc0 : mixedMoment B raw258 (Fin.cases (0 : Fin 1) singletonSmall2640) =
      mixedMoment B node315 node315Labels := by
    have ha : raw258 = raw259 := by apply Matrix.ext; unfold raw258 raw259; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2640 = raw259Labels := by decide +kernel
    rw [ha, hj, canonical259 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2642 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2642 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2642 node2642Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node236 node236Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw260 singletonSmall2642
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2642) = raw260Labels := by decide +kernel
  rw [hl, canonical260 B hB] at h
  have hc0 : mixedMoment B raw260 (Fin.cases (0 : Fin 1) singletonSmall2642) =
      mixedMoment B node236 node236Labels := by
    have ha : raw260 = raw261 := by apply Matrix.ext; unfold raw260 raw261; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2642 = raw261Labels := by decide +kernel
    rw [ha, hj, canonical261 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2644 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2644 node2644Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node355 node355Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw262 singletonSmall2644
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2644) = raw262Labels := by decide +kernel
  rw [hl, canonical262 B hB] at h
  have hc0 : mixedMoment B raw262 (Fin.cases (0 : Fin 1) singletonSmall2644) =
      mixedMoment B node355 node355Labels := by
    have ha : raw262 = raw263 := by apply Matrix.ext; unfold raw262 raw263; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2644 = raw263Labels := by decide +kernel
    rw [ha, hj, canonical263 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
