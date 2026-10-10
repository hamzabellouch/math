import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical4

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3911 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3911 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3911 node3911Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node504 node504Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw548 singletonSmall3911
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3911) = raw548Labels := by decide +kernel
  rw [hl, canonical548 B hB] at h
  have hc0 : mixedMoment B raw548 (Fin.cases (0 : Fin 1) singletonSmall3911) =
      mixedMoment B node504 node504Labels := by
    have ha : raw548 = raw549 := by apply Matrix.ext; unfold raw548 raw549; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3911 = raw549Labels := by decide +kernel
    rw [ha, hj, canonical549 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3912 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3912 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3912 node3912Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node505 node505Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw550 singletonSmall3912
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3912) = raw550Labels := by decide +kernel
  rw [hl, canonical550 B hB] at h
  have hc0 : mixedMoment B raw550 (Fin.cases (0 : Fin 1) singletonSmall3912) =
      mixedMoment B node505 node505Labels := by
    have ha : raw550 = raw551 := by apply Matrix.ext; unfold raw550 raw551; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3912 = raw551Labels := by decide +kernel
    rw [ha, hj, canonical551 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3915 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3915 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3915 node3915Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node505 node505Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw552 singletonSmall3915
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3915) = raw552Labels := by decide +kernel
  rw [hl, canonical552 B hB] at h
  have hc0 : mixedMoment B raw552 (Fin.cases (0 : Fin 1) singletonSmall3915) =
      mixedMoment B node505 node505Labels := by
    have ha : raw552 = raw553 := by apply Matrix.ext; unfold raw552 raw553; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3915 = raw553Labels := by decide +kernel
    rw [ha, hj, canonical553 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3916 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3916 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3916 node3916Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node507 node507Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw554 singletonSmall3916
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3916) = raw554Labels := by decide +kernel
  rw [hl, canonical554 B hB] at h
  have hc0 : mixedMoment B raw554 (Fin.cases (0 : Fin 1) singletonSmall3916) =
      mixedMoment B node507 node507Labels := by
    have ha : raw554 = raw555 := by apply Matrix.ext; unfold raw554 raw555; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3916 = raw555Labels := by decide +kernel
    rw [ha, hj, canonical555 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3919 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3919 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3919 node3919Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node425 node425Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw556 singletonSmall3919
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3919) = raw556Labels := by decide +kernel
  rw [hl, canonical556 B hB] at h
  have hc0 : mixedMoment B raw556 (Fin.cases (0 : Fin 1) singletonSmall3919) =
      mixedMoment B node425 node425Labels := by
    have ha : raw556 = raw557 := by apply Matrix.ext; unfold raw556 raw557; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3919 = raw557Labels := by decide +kernel
    rw [ha, hj, canonical557 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3925 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3925 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3925 node3925Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node453 node453Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw558 singletonSmall3925
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3925) = raw558Labels := by decide +kernel
  rw [hl, canonical558 B hB] at h
  have hc0 : mixedMoment B raw558 (Fin.cases (0 : Fin 1) singletonSmall3925) =
      mixedMoment B node453 node453Labels := by
    have ha : raw558 = raw559 := by apply Matrix.ext; unfold raw558 raw559; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3925 = raw559Labels := by decide +kernel
    rw [ha, hj, canonical559 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3926 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3926 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3926 node3926Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node433 node433Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw560 singletonSmall3926
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3926) = raw560Labels := by decide +kernel
  rw [hl, canonical560 B hB] at h
  have hc0 : mixedMoment B raw560 (Fin.cases (0 : Fin 1) singletonSmall3926) =
      mixedMoment B node433 node433Labels := by
    have ha : raw560 = raw561 := by apply Matrix.ext; unfold raw560 raw561; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3926 = raw561Labels := by decide +kernel
    rw [ha, hj, canonical561 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3930 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3930 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3930 node3930Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node508 node508Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw562 singletonSmall3930
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3930) = raw562Labels := by decide +kernel
  rw [hl, canonical562 B hB] at h
  have hc0 : mixedMoment B raw562 (Fin.cases (0 : Fin 1) singletonSmall3930) =
      mixedMoment B node508 node508Labels := by
    have ha : raw562 = raw563 := by apply Matrix.ext; unfold raw562 raw563; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3930 = raw563Labels := by decide +kernel
    rw [ha, hj, canonical563 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3931 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3931 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3931 node3931Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node509 node509Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw564 singletonSmall3931
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3931) = raw564Labels := by decide +kernel
  rw [hl, canonical564 B hB] at h
  have hc0 : mixedMoment B raw564 (Fin.cases (0 : Fin 1) singletonSmall3931) =
      mixedMoment B node509 node509Labels := by
    have ha : raw564 = raw565 := by apply Matrix.ext; unfold raw564 raw565; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3931 = raw565Labels := by decide +kernel
    rw [ha, hj, canonical565 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3932 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3932 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3932 node3932Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node460 node460Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw566 singletonSmall3932
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3932) = raw566Labels := by decide +kernel
  rw [hl, canonical566 B hB] at h
  have hc0 : mixedMoment B raw566 (Fin.cases (0 : Fin 1) singletonSmall3932) =
      mixedMoment B node460 node460Labels := by
    have ha : raw566 = raw567 := by apply Matrix.ext; unfold raw566 raw567; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3932 = raw567Labels := by decide +kernel
    rw [ha, hj, canonical567 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3933 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3933 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3933 node3933Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node474 node474Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw568 singletonSmall3933
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3933) = raw568Labels := by decide +kernel
  rw [hl, canonical568 B hB] at h
  have hc0 : mixedMoment B raw568 (Fin.cases (0 : Fin 1) singletonSmall3933) =
      mixedMoment B node474 node474Labels := by
    have ha : raw568 = raw569 := by apply Matrix.ext; unfold raw568 raw569; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3933 = raw569Labels := by decide +kernel
    rw [ha, hj, canonical569 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3934 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3934 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3934 node3934Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node510 node510Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw570 singletonSmall3934
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3934) = raw570Labels := by decide +kernel
  rw [hl, canonical570 B hB] at h
  have hc0 : mixedMoment B raw570 (Fin.cases (0 : Fin 1) singletonSmall3934) =
      mixedMoment B node510 node510Labels := by
    have ha : raw570 = raw571 := by apply Matrix.ext; unfold raw570 raw571; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3934 = raw571Labels := by decide +kernel
    rw [ha, hj, canonical571 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3936 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3936 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3936 node3936Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node430 node430Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw572 singletonSmall3936
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3936) = raw572Labels := by decide +kernel
  rw [hl, canonical572 B hB] at h
  have hc0 : mixedMoment B raw572 (Fin.cases (0 : Fin 1) singletonSmall3936) =
      mixedMoment B node430 node430Labels := by
    have ha : raw572 = raw573 := by apply Matrix.ext; unfold raw572 raw573; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3936 = raw573Labels := by decide +kernel
    rw [ha, hj, canonical573 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3937 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3937 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3937 node3937Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node429 node429Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw574 singletonSmall3937
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3937) = raw574Labels := by decide +kernel
  rw [hl, canonical574 B hB] at h
  have hc0 : mixedMoment B raw574 (Fin.cases (0 : Fin 1) singletonSmall3937) =
      mixedMoment B node429 node429Labels := by
    have ha : raw574 = raw575 := by apply Matrix.ext; unfold raw574 raw575; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3937 = raw575Labels := by decide +kernel
    rw [ha, hj, canonical575 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3938 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3938 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3938 node3938Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node436 node436Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw576 singletonSmall3938
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3938) = raw576Labels := by decide +kernel
  rw [hl, canonical576 B hB] at h
  have hc0 : mixedMoment B raw576 (Fin.cases (0 : Fin 1) singletonSmall3938) =
      mixedMoment B node436 node436Labels := by
    have ha : raw576 = raw577 := by apply Matrix.ext; unfold raw576 raw577; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3938 = raw577Labels := by decide +kernel
    rw [ha, hj, canonical577 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3939 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3939 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3939 node3939Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node437 node437Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw578 singletonSmall3939
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3939) = raw578Labels := by decide +kernel
  rw [hl, canonical578 B hB] at h
  have hc0 : mixedMoment B raw578 (Fin.cases (0 : Fin 1) singletonSmall3939) =
      mixedMoment B node437 node437Labels := by
    have ha : raw578 = raw579 := by apply Matrix.ext; unfold raw578 raw579; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3939 = raw579Labels := by decide +kernel
    rw [ha, hj, canonical579 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3965 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3965 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3965 node3965Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node517 node517Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw580 singletonSmall3965
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3965) = raw580Labels := by decide +kernel
  rw [hl, canonical580 B hB] at h
  have hc0 : mixedMoment B raw580 (Fin.cases (0 : Fin 1) singletonSmall3965) =
      mixedMoment B node517 node517Labels := by
    have ha : raw580 = raw581 := by apply Matrix.ext; unfold raw580 raw581; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3965 = raw581Labels := by decide +kernel
    rw [ha, hj, canonical581 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3966 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3966 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3966 node3966Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node457 node457Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw582 singletonSmall3966
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3966) = raw582Labels := by decide +kernel
  rw [hl, canonical582 B hB] at h
  have hc0 : mixedMoment B raw582 (Fin.cases (0 : Fin 1) singletonSmall3966) =
      mixedMoment B node457 node457Labels := by
    have ha : raw582 = raw583 := by apply Matrix.ext; unfold raw582 raw583; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3966 = raw583Labels := by decide +kernel
    rw [ha, hj, canonical583 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3967 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3967 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3967 node3967Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node472 node472Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw584 singletonSmall3967
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3967) = raw584Labels := by decide +kernel
  rw [hl, canonical584 B hB] at h
  have hc0 : mixedMoment B raw584 (Fin.cases (0 : Fin 1) singletonSmall3967) =
      mixedMoment B node472 node472Labels := by
    have ha : raw584 = raw585 := by apply Matrix.ext; unfold raw584 raw585; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3967 = raw585Labels := by decide +kernel
    rw [ha, hj, canonical585 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
