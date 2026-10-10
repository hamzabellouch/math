import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical0

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall644 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node644 node644Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node26 node26Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw0 singletonSmall644
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall644) = raw0Labels := by decide +kernel
  rw [hl, canonical0 B hB] at h
  have hc0 : mixedMoment B raw0 (Fin.cases (0 : Fin 1) singletonSmall644) =
      mixedMoment B node26 node26Labels := by
    have ha : raw0 = raw1 := by apply Matrix.ext; unfold raw0 raw1; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall644 = raw1Labels := by decide +kernel
    rw [ha, hj, canonical1 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall645 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton645 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node645 node645Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node31 node31Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw2 singletonSmall645
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall645) = raw2Labels := by decide +kernel
  rw [hl, canonical2 B hB] at h
  have hc0 : mixedMoment B raw2 (Fin.cases (0 : Fin 1) singletonSmall645) =
      mixedMoment B node31 node31Labels := by
    have ha : raw2 = raw3 := by apply Matrix.ext; unfold raw2 raw3; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall645 = raw3Labels := by decide +kernel
    rw [ha, hj, canonical3 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall646 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton646 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node646 node646Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node23 node23Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw4 singletonSmall646
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall646) = raw4Labels := by decide +kernel
  rw [hl, canonical4 B hB] at h
  have hc0 : mixedMoment B raw4 (Fin.cases (0 : Fin 1) singletonSmall646) =
      mixedMoment B node23 node23Labels := by
    have ha : raw4 = raw5 := by apply Matrix.ext; unfold raw4 raw5; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall646 = raw5Labels := by decide +kernel
    rw [ha, hj, canonical5 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall647 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton647 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node647 node647Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node28 node28Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw6 singletonSmall647
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall647) = raw6Labels := by decide +kernel
  rw [hl, canonical6 B hB] at h
  have hc0 : mixedMoment B raw6 (Fin.cases (0 : Fin 1) singletonSmall647) =
      mixedMoment B node28 node28Labels := by
    have ha : raw6 = raw7 := by apply Matrix.ext; unfold raw6 raw7; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall647 = raw7Labels := by decide +kernel
    rw [ha, hj, canonical7 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall648 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton648 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node648 node648Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node33 node33Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw8 singletonSmall648
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall648) = raw8Labels := by decide +kernel
  rw [hl, canonical8 B hB] at h
  have hc0 : mixedMoment B raw8 (Fin.cases (0 : Fin 1) singletonSmall648) =
      mixedMoment B node33 node33Labels := by
    have ha : raw8 = raw9 := by apply Matrix.ext; unfold raw8 raw9; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall648 = raw9Labels := by decide +kernel
    rw [ha, hj, canonical9 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall649 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton649 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node649 node649Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node34 node34Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw10 singletonSmall649
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall649) = raw10Labels := by decide +kernel
  rw [hl, canonical10 B hB] at h
  have hc0 : mixedMoment B raw10 (Fin.cases (0 : Fin 1) singletonSmall649) =
      mixedMoment B node34 node34Labels := by
    have ha : raw10 = raw11 := by apply Matrix.ext; unfold raw10 raw11; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall649 = raw11Labels := by decide +kernel
    rw [ha, hj, canonical11 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall650 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton650 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node650 node650Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node35 node35Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw12 singletonSmall650
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall650) = raw12Labels := by decide +kernel
  rw [hl, canonical12 B hB] at h
  have hc0 : mixedMoment B raw12 (Fin.cases (0 : Fin 1) singletonSmall650) =
      mixedMoment B node35 node35Labels := by
    have ha : raw12 = raw13 := by apply Matrix.ext; unfold raw12 raw13; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall650 = raw13Labels := by decide +kernel
    rw [ha, hj, canonical13 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall652 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton652 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node652 node652Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node25 node25Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw14 singletonSmall652
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall652) = raw14Labels := by decide +kernel
  rw [hl, canonical14 B hB] at h
  have hc0 : mixedMoment B raw14 (Fin.cases (0 : Fin 1) singletonSmall652) =
      mixedMoment B node25 node25Labels := by
    have ha : raw14 = raw15 := by apply Matrix.ext; unfold raw14 raw15; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall652 = raw15Labels := by decide +kernel
    rw [ha, hj, canonical15 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall655 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton655 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node655 node655Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node38 node38Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw16 singletonSmall655
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall655) = raw16Labels := by decide +kernel
  rw [hl, canonical16 B hB] at h
  have hc0 : mixedMoment B raw16 (Fin.cases (0 : Fin 1) singletonSmall655) =
      mixedMoment B node38 node38Labels := by
    have ha : raw16 = raw17 := by apply Matrix.ext; unfold raw16 raw17; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall655 = raw17Labels := by decide +kernel
    rw [ha, hj, canonical17 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
