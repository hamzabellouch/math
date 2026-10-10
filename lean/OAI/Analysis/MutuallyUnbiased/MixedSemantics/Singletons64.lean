import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical6

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4096 : Fin 1 → Fin 1 := ![0]

theorem singleton4096 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4096 node4096Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node7 node7Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw664 singletonSmall4096
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4096) = raw664Labels := by decide +kernel
  rw [hl, canonical664 B hB] at h
  have hc0 : mixedMoment B raw664 (Fin.cases (0 : Fin 1) singletonSmall4096) =
      mixedMoment B node7 node7Labels := by
    have ha : raw664 = raw665 := by apply Matrix.ext; unfold raw664 raw665; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4096 = raw665Labels := by decide +kernel
    rw [ha, hj, canonical665 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4098 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4098 node4098Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node535 node535Labels + mixedMoment B node656 node656Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw666 singletonSmall4098
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4098) = raw666Labels := by decide +kernel
  rw [hl, canonical666 B hB] at h
  have hc0 : mixedMoment B raw666 (Fin.cases (0 : Fin 2) singletonSmall4098) =
      mixedMoment B node535 node535Labels := by
    have ha : raw666 = raw667 := by apply Matrix.ext; unfold raw666 raw667; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4098 = raw667Labels := by decide +kernel
    rw [ha, hj, canonical667 B hB]
  have hc1 : mixedMoment B raw666 (Fin.cases (1 : Fin 2) singletonSmall4098) =
      mixedMoment B node656 node656Labels := by
    have ha : raw666 = raw668 := by apply Matrix.ext; unfold raw666 raw668; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4098 = raw668Labels := by decide +kernel
    rw [ha, hj, canonical668 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4099 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4099 node4099Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node536 node536Labels + mixedMoment B node657 node657Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw669 singletonSmall4099
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4099) = raw669Labels := by decide +kernel
  rw [hl, canonical669 B hB] at h
  have hc0 : mixedMoment B raw669 (Fin.cases (0 : Fin 2) singletonSmall4099) =
      mixedMoment B node536 node536Labels := by
    have ha : raw669 = raw670 := by apply Matrix.ext; unfold raw669 raw670; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4099 = raw670Labels := by decide +kernel
    rw [ha, hj, canonical670 B hB]
  have hc1 : mixedMoment B raw669 (Fin.cases (1 : Fin 2) singletonSmall4099) =
      mixedMoment B node657 node657Labels := by
    have ha : raw669 = raw671 := by apply Matrix.ext; unfold raw669 raw671; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4099 = raw671Labels := by decide +kernel
    rw [ha, hj, canonical671 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4100 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4100 node4100Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node537 node537Labels + mixedMoment B node662 node662Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw672 singletonSmall4100
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4100) = raw672Labels := by decide +kernel
  rw [hl, canonical672 B hB] at h
  have hc0 : mixedMoment B raw672 (Fin.cases (0 : Fin 2) singletonSmall4100) =
      mixedMoment B node537 node537Labels := by
    have ha : raw672 = raw673 := by apply Matrix.ext; unfold raw672 raw673; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4100 = raw673Labels := by decide +kernel
    rw [ha, hj, canonical673 B hB]
  have hc1 : mixedMoment B raw672 (Fin.cases (1 : Fin 2) singletonSmall4100) =
      mixedMoment B node662 node662Labels := by
    have ha : raw672 = raw674 := by apply Matrix.ext; unfold raw672 raw674; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4100 = raw674Labels := by decide +kernel
    rw [ha, hj, canonical674 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4101 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4101 node4101Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node538 node538Labels + mixedMoment B node663 node663Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw675 singletonSmall4101
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4101) = raw675Labels := by decide +kernel
  rw [hl, canonical675 B hB] at h
  have hc0 : mixedMoment B raw675 (Fin.cases (0 : Fin 2) singletonSmall4101) =
      mixedMoment B node538 node538Labels := by
    have ha : raw675 = raw676 := by apply Matrix.ext; unfold raw675 raw676; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4101 = raw676Labels := by decide +kernel
    rw [ha, hj, canonical676 B hB]
  have hc1 : mixedMoment B raw675 (Fin.cases (1 : Fin 2) singletonSmall4101) =
      mixedMoment B node663 node663Labels := by
    have ha : raw675 = raw677 := by apply Matrix.ext; unfold raw675 raw677; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4101 = raw677Labels := by decide +kernel
    rw [ha, hj, canonical677 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4102 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4102 node4102Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node539 node539Labels + mixedMoment B node664 node664Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw678 singletonSmall4102
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4102) = raw678Labels := by decide +kernel
  rw [hl, canonical678 B hB] at h
  have hc0 : mixedMoment B raw678 (Fin.cases (0 : Fin 2) singletonSmall4102) =
      mixedMoment B node539 node539Labels := by
    have ha : raw678 = raw679 := by apply Matrix.ext; unfold raw678 raw679; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4102 = raw679Labels := by decide +kernel
    rw [ha, hj, canonical679 B hB]
  have hc1 : mixedMoment B raw678 (Fin.cases (1 : Fin 2) singletonSmall4102) =
      mixedMoment B node664 node664Labels := by
    have ha : raw678 = raw680 := by apply Matrix.ext; unfold raw678 raw680; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4102 = raw680Labels := by decide +kernel
    rw [ha, hj, canonical680 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4103 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4103 node4103Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node540 node540Labels + mixedMoment B node665 node665Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw681 singletonSmall4103
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4103) = raw681Labels := by decide +kernel
  rw [hl, canonical681 B hB] at h
  have hc0 : mixedMoment B raw681 (Fin.cases (0 : Fin 2) singletonSmall4103) =
      mixedMoment B node540 node540Labels := by
    have ha : raw681 = raw682 := by apply Matrix.ext; unfold raw681 raw682; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4103 = raw682Labels := by decide +kernel
    rw [ha, hj, canonical682 B hB]
  have hc1 : mixedMoment B raw681 (Fin.cases (1 : Fin 2) singletonSmall4103) =
      mixedMoment B node665 node665Labels := by
    have ha : raw681 = raw683 := by apply Matrix.ext; unfold raw681 raw683; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4103 = raw683Labels := by decide +kernel
    rw [ha, hj, canonical683 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4104 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4104 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4104 node4104Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node541 node541Labels + mixedMoment B node674 node674Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw684 singletonSmall4104
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4104) = raw684Labels := by decide +kernel
  rw [hl, canonical684 B hB] at h
  have hc0 : mixedMoment B raw684 (Fin.cases (0 : Fin 2) singletonSmall4104) =
      mixedMoment B node541 node541Labels := by
    have ha : raw684 = raw685 := by apply Matrix.ext; unfold raw684 raw685; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4104 = raw685Labels := by decide +kernel
    rw [ha, hj, canonical685 B hB]
  have hc1 : mixedMoment B raw684 (Fin.cases (1 : Fin 2) singletonSmall4104) =
      mixedMoment B node674 node674Labels := by
    have ha : raw684 = raw686 := by apply Matrix.ext; unfold raw684 raw686; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4104 = raw686Labels := by decide +kernel
    rw [ha, hj, canonical686 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4105 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4105 node4105Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node542 node542Labels + mixedMoment B node681 node681Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw687 singletonSmall4105
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4105) = raw687Labels := by decide +kernel
  rw [hl, canonical687 B hB] at h
  have hc0 : mixedMoment B raw687 (Fin.cases (0 : Fin 2) singletonSmall4105) =
      mixedMoment B node542 node542Labels := by
    have ha : raw687 = raw688 := by apply Matrix.ext; unfold raw687 raw688; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4105 = raw688Labels := by decide +kernel
    rw [ha, hj, canonical688 B hB]
  have hc1 : mixedMoment B raw687 (Fin.cases (1 : Fin 2) singletonSmall4105) =
      mixedMoment B node681 node681Labels := by
    have ha : raw687 = raw689 := by apply Matrix.ext; unfold raw687 raw689; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4105 = raw689Labels := by decide +kernel
    rw [ha, hj, canonical689 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4106 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4106 node4106Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node543 node543Labels + mixedMoment B node675 node675Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw690 singletonSmall4106
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4106) = raw690Labels := by decide +kernel
  rw [hl, canonical690 B hB] at h
  have hc0 : mixedMoment B raw690 (Fin.cases (0 : Fin 2) singletonSmall4106) =
      mixedMoment B node543 node543Labels := by
    have ha : raw690 = raw691 := by apply Matrix.ext; unfold raw690 raw691; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4106 = raw691Labels := by decide +kernel
    rw [ha, hj, canonical691 B hB]
  have hc1 : mixedMoment B raw690 (Fin.cases (1 : Fin 2) singletonSmall4106) =
      mixedMoment B node675 node675Labels := by
    have ha : raw690 = raw692 := by apply Matrix.ext; unfold raw690 raw692; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4106 = raw692Labels := by decide +kernel
    rw [ha, hj, canonical692 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4107 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4107 node4107Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node544 node544Labels + mixedMoment B node682 node682Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw693 singletonSmall4107
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4107) = raw693Labels := by decide +kernel
  rw [hl, canonical693 B hB] at h
  have hc0 : mixedMoment B raw693 (Fin.cases (0 : Fin 2) singletonSmall4107) =
      mixedMoment B node544 node544Labels := by
    have ha : raw693 = raw694 := by apply Matrix.ext; unfold raw693 raw694; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4107 = raw694Labels := by decide +kernel
    rw [ha, hj, canonical694 B hB]
  have hc1 : mixedMoment B raw693 (Fin.cases (1 : Fin 2) singletonSmall4107) =
      mixedMoment B node682 node682Labels := by
    have ha : raw693 = raw695 := by apply Matrix.ext; unfold raw693 raw695; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4107 = raw695Labels := by decide +kernel
    rw [ha, hj, canonical695 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4108 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4108 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4108 node4108Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node545 node545Labels + mixedMoment B node683 node683Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw696 singletonSmall4108
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4108) = raw696Labels := by decide +kernel
  rw [hl, canonical696 B hB] at h
  have hc0 : mixedMoment B raw696 (Fin.cases (0 : Fin 2) singletonSmall4108) =
      mixedMoment B node545 node545Labels := by
    have ha : raw696 = raw697 := by apply Matrix.ext; unfold raw696 raw697; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4108 = raw697Labels := by decide +kernel
    rw [ha, hj, canonical697 B hB]
  have hc1 : mixedMoment B raw696 (Fin.cases (1 : Fin 2) singletonSmall4108) =
      mixedMoment B node683 node683Labels := by
    have ha : raw696 = raw698 := by apply Matrix.ext; unfold raw696 raw698; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4108 = raw698Labels := by decide +kernel
    rw [ha, hj, canonical698 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4109 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4109 node4109Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node546 node546Labels + mixedMoment B node676 node676Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw699 singletonSmall4109
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4109) = raw699Labels := by decide +kernel
  rw [hl, canonical699 B hB] at h
  have hc0 : mixedMoment B raw699 (Fin.cases (0 : Fin 2) singletonSmall4109) =
      mixedMoment B node546 node546Labels := by
    have ha : raw699 = raw700 := by apply Matrix.ext; unfold raw699 raw700; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4109 = raw700Labels := by decide +kernel
    rw [ha, hj, canonical700 B hB]
  have hc1 : mixedMoment B raw699 (Fin.cases (1 : Fin 2) singletonSmall4109) =
      mixedMoment B node676 node676Labels := by
    have ha : raw699 = raw701 := by apply Matrix.ext; unfold raw699 raw701; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4109 = raw701Labels := by decide +kernel
    rw [ha, hj, canonical701 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4110 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4110 node4110Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node547 node547Labels + mixedMoment B node684 node684Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw702 singletonSmall4110
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4110) = raw702Labels := by decide +kernel
  rw [hl, canonical702 B hB] at h
  have hc0 : mixedMoment B raw702 (Fin.cases (0 : Fin 2) singletonSmall4110) =
      mixedMoment B node547 node547Labels := by
    have ha : raw702 = raw703 := by apply Matrix.ext; unfold raw702 raw703; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4110 = raw703Labels := by decide +kernel
    rw [ha, hj, canonical703 B hB]
  have hc1 : mixedMoment B raw702 (Fin.cases (1 : Fin 2) singletonSmall4110) =
      mixedMoment B node684 node684Labels := by
    have ha : raw702 = raw704 := by apply Matrix.ext; unfold raw702 raw704; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4110 = raw704Labels := by decide +kernel
    rw [ha, hj, canonical704 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4111 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4111 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4111 node4111Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node548 node548Labels + mixedMoment B node685 node685Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw705 singletonSmall4111
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4111) = raw705Labels := by decide +kernel
  rw [hl, canonical705 B hB] at h
  have hc0 : mixedMoment B raw705 (Fin.cases (0 : Fin 2) singletonSmall4111) =
      mixedMoment B node548 node548Labels := by
    have ha : raw705 = raw706 := by apply Matrix.ext; unfold raw705 raw706; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4111 = raw706Labels := by decide +kernel
    rw [ha, hj, canonical706 B hB]
  have hc1 : mixedMoment B raw705 (Fin.cases (1 : Fin 2) singletonSmall4111) =
      mixedMoment B node685 node685Labels := by
    have ha : raw705 = raw707 := by apply Matrix.ext; unfold raw705 raw707; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4111 = raw707Labels := by decide +kernel
    rw [ha, hj, canonical707 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4112 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4112 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4112 node4112Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node549 node549Labels + mixedMoment B node686 node686Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw708 singletonSmall4112
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4112) = raw708Labels := by decide +kernel
  rw [hl, canonical708 B hB] at h
  have hc0 : mixedMoment B raw708 (Fin.cases (0 : Fin 2) singletonSmall4112) =
      mixedMoment B node549 node549Labels := by
    have ha : raw708 = raw709 := by apply Matrix.ext; unfold raw708 raw709; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4112 = raw709Labels := by decide +kernel
    rw [ha, hj, canonical709 B hB]
  have hc1 : mixedMoment B raw708 (Fin.cases (1 : Fin 2) singletonSmall4112) =
      mixedMoment B node686 node686Labels := by
    have ha : raw708 = raw710 := by apply Matrix.ext; unfold raw708 raw710; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4112 = raw710Labels := by decide +kernel
    rw [ha, hj, canonical710 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4113 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4113 node4113Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node550 node550Labels + mixedMoment B node658 node658Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw711 singletonSmall4113
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4113) = raw711Labels := by decide +kernel
  rw [hl, canonical711 B hB] at h
  have hc0 : mixedMoment B raw711 (Fin.cases (0 : Fin 2) singletonSmall4113) =
      mixedMoment B node550 node550Labels := by
    have ha : raw711 = raw712 := by apply Matrix.ext; unfold raw711 raw712; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4113 = raw712Labels := by decide +kernel
    rw [ha, hj, canonical712 B hB]
  have hc1 : mixedMoment B raw711 (Fin.cases (1 : Fin 2) singletonSmall4113) =
      mixedMoment B node658 node658Labels := by
    have ha : raw711 = raw713 := by apply Matrix.ext; unfold raw711 raw713; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4113 = raw713Labels := by decide +kernel
    rw [ha, hj, canonical713 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4114 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4114 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4114 node4114Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node551 node551Labels + mixedMoment B node659 node659Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw714 singletonSmall4114
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4114) = raw714Labels := by decide +kernel
  rw [hl, canonical714 B hB] at h
  have hc0 : mixedMoment B raw714 (Fin.cases (0 : Fin 2) singletonSmall4114) =
      mixedMoment B node551 node551Labels := by
    have ha : raw714 = raw715 := by apply Matrix.ext; unfold raw714 raw715; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4114 = raw715Labels := by decide +kernel
    rw [ha, hj, canonical715 B hB]
  have hc1 : mixedMoment B raw714 (Fin.cases (1 : Fin 2) singletonSmall4114) =
      mixedMoment B node659 node659Labels := by
    have ha : raw714 = raw716 := by apply Matrix.ext; unfold raw714 raw716; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4114 = raw716Labels := by decide +kernel
    rw [ha, hj, canonical716 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4115 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4115 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4115 node4115Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node552 node552Labels + mixedMoment B node660 node660Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw717 singletonSmall4115
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4115) = raw717Labels := by decide +kernel
  rw [hl, canonical717 B hB] at h
  have hc0 : mixedMoment B raw717 (Fin.cases (0 : Fin 2) singletonSmall4115) =
      mixedMoment B node552 node552Labels := by
    have ha : raw717 = raw718 := by apply Matrix.ext; unfold raw717 raw718; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4115 = raw718Labels := by decide +kernel
    rw [ha, hj, canonical718 B hB]
  have hc1 : mixedMoment B raw717 (Fin.cases (1 : Fin 2) singletonSmall4115) =
      mixedMoment B node660 node660Labels := by
    have ha : raw717 = raw719 := by apply Matrix.ext; unfold raw717 raw719; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4115 = raw719Labels := by decide +kernel
    rw [ha, hj, canonical719 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4116 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4116 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4116 node4116Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node553 node553Labels + mixedMoment B node661 node661Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw720 singletonSmall4116
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4116) = raw720Labels := by decide +kernel
  rw [hl, canonical720 B hB] at h
  have hc0 : mixedMoment B raw720 (Fin.cases (0 : Fin 2) singletonSmall4116) =
      mixedMoment B node553 node553Labels := by
    have ha : raw720 = raw721 := by apply Matrix.ext; unfold raw720 raw721; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4116 = raw721Labels := by decide +kernel
    rw [ha, hj, canonical721 B hB]
  have hc1 : mixedMoment B raw720 (Fin.cases (1 : Fin 2) singletonSmall4116) =
      mixedMoment B node661 node661Labels := by
    have ha : raw720 = raw722 := by apply Matrix.ext; unfold raw720 raw722; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4116 = raw722Labels := by decide +kernel
    rw [ha, hj, canonical722 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4119 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4119 node4119Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node554 node554Labels + mixedMoment B node668 node668Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw723 singletonSmall4119
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4119) = raw723Labels := by decide +kernel
  rw [hl, canonical723 B hB] at h
  have hc0 : mixedMoment B raw723 (Fin.cases (0 : Fin 2) singletonSmall4119) =
      mixedMoment B node554 node554Labels := by
    have ha : raw723 = raw724 := by apply Matrix.ext; unfold raw723 raw724; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4119 = raw724Labels := by decide +kernel
    rw [ha, hj, canonical724 B hB]
  have hc1 : mixedMoment B raw723 (Fin.cases (1 : Fin 2) singletonSmall4119) =
      mixedMoment B node668 node668Labels := by
    have ha : raw723 = raw725 := by apply Matrix.ext; unfold raw723 raw725; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4119 = raw725Labels := by decide +kernel
    rw [ha, hj, canonical725 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4121 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4121 node4121Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node555 node555Labels + mixedMoment B node671 node671Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw726 singletonSmall4121
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4121) = raw726Labels := by decide +kernel
  rw [hl, canonical726 B hB] at h
  have hc0 : mixedMoment B raw726 (Fin.cases (0 : Fin 2) singletonSmall4121) =
      mixedMoment B node555 node555Labels := by
    have ha : raw726 = raw727 := by apply Matrix.ext; unfold raw726 raw727; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4121 = raw727Labels := by decide +kernel
    rw [ha, hj, canonical727 B hB]
  have hc1 : mixedMoment B raw726 (Fin.cases (1 : Fin 2) singletonSmall4121) =
      mixedMoment B node671 node671Labels := by
    have ha : raw726 = raw728 := by apply Matrix.ext; unfold raw726 raw728; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4121 = raw728Labels := by decide +kernel
    rw [ha, hj, canonical728 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4122 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4122 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4122 node4122Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node556 node556Labels + mixedMoment B node670 node670Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw729 singletonSmall4122
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4122) = raw729Labels := by decide +kernel
  rw [hl, canonical729 B hB] at h
  have hc0 : mixedMoment B raw729 (Fin.cases (0 : Fin 2) singletonSmall4122) =
      mixedMoment B node556 node556Labels := by
    have ha : raw729 = raw730 := by apply Matrix.ext; unfold raw729 raw730; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4122 = raw730Labels := by decide +kernel
    rw [ha, hj, canonical730 B hB]
  have hc1 : mixedMoment B raw729 (Fin.cases (1 : Fin 2) singletonSmall4122) =
      mixedMoment B node670 node670Labels := by
    have ha : raw729 = raw731 := by apply Matrix.ext; unfold raw729 raw731; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4122 = raw731Labels := by decide +kernel
    rw [ha, hj, canonical731 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4126 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4126 node4126Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node557 node557Labels + mixedMoment B node677 node677Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw732 singletonSmall4126
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4126) = raw732Labels := by decide +kernel
  rw [hl, canonical732 B hB] at h
  have hc0 : mixedMoment B raw732 (Fin.cases (0 : Fin 2) singletonSmall4126) =
      mixedMoment B node557 node557Labels := by
    have ha : raw732 = raw733 := by apply Matrix.ext; unfold raw732 raw733; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4126 = raw733Labels := by decide +kernel
    rw [ha, hj, canonical733 B hB]
  have hc1 : mixedMoment B raw732 (Fin.cases (1 : Fin 2) singletonSmall4126) =
      mixedMoment B node677 node677Labels := by
    have ha : raw732 = raw734 := by apply Matrix.ext; unfold raw732 raw734; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4126 = raw734Labels := by decide +kernel
    rw [ha, hj, canonical734 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4128 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4128 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4128 node4128Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node559 node559Labels + mixedMoment B node690 node690Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw735 singletonSmall4128
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4128) = raw735Labels := by decide +kernel
  rw [hl, canonical735 B hB] at h
  have hc0 : mixedMoment B raw735 (Fin.cases (0 : Fin 2) singletonSmall4128) =
      mixedMoment B node559 node559Labels := by
    have ha : raw735 = raw736 := by apply Matrix.ext; unfold raw735 raw736; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4128 = raw736Labels := by decide +kernel
    rw [ha, hj, canonical736 B hB]
  have hc1 : mixedMoment B raw735 (Fin.cases (1 : Fin 2) singletonSmall4128) =
      mixedMoment B node690 node690Labels := by
    have ha : raw735 = raw737 := by apply Matrix.ext; unfold raw735 raw737; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4128 = raw737Labels := by decide +kernel
    rw [ha, hj, canonical737 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4129 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4129 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4129 node4129Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node560 node560Labels + mixedMoment B node678 node678Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw738 singletonSmall4129
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4129) = raw738Labels := by decide +kernel
  rw [hl, canonical738 B hB] at h
  have hc0 : mixedMoment B raw738 (Fin.cases (0 : Fin 2) singletonSmall4129) =
      mixedMoment B node560 node560Labels := by
    have ha : raw738 = raw739 := by apply Matrix.ext; unfold raw738 raw739; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4129 = raw739Labels := by decide +kernel
    rw [ha, hj, canonical739 B hB]
  have hc1 : mixedMoment B raw738 (Fin.cases (1 : Fin 2) singletonSmall4129) =
      mixedMoment B node678 node678Labels := by
    have ha : raw738 = raw740 := by apply Matrix.ext; unfold raw738 raw740; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4129 = raw740Labels := by decide +kernel
    rw [ha, hj, canonical740 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4132 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4132 node4132Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node562 node562Labels + mixedMoment B node679 node679Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw741 singletonSmall4132
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4132) = raw741Labels := by decide +kernel
  rw [hl, canonical741 B hB] at h
  have hc0 : mixedMoment B raw741 (Fin.cases (0 : Fin 2) singletonSmall4132) =
      mixedMoment B node562 node562Labels := by
    have ha : raw741 = raw742 := by apply Matrix.ext; unfold raw741 raw742; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4132 = raw742Labels := by decide +kernel
    rw [ha, hj, canonical742 B hB]
  have hc1 : mixedMoment B raw741 (Fin.cases (1 : Fin 2) singletonSmall4132) =
      mixedMoment B node679 node679Labels := by
    have ha : raw741 = raw743 := by apply Matrix.ext; unfold raw741 raw743; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4132 = raw743Labels := by decide +kernel
    rw [ha, hj, canonical743 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4133 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4133 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4133 node4133Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node563 node563Labels + mixedMoment B node692 node692Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw744 singletonSmall4133
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4133) = raw744Labels := by decide +kernel
  rw [hl, canonical744 B hB] at h
  have hc0 : mixedMoment B raw744 (Fin.cases (0 : Fin 2) singletonSmall4133) =
      mixedMoment B node563 node563Labels := by
    have ha : raw744 = raw745 := by apply Matrix.ext; unfold raw744 raw745; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4133 = raw745Labels := by decide +kernel
    rw [ha, hj, canonical745 B hB]
  have hc1 : mixedMoment B raw744 (Fin.cases (1 : Fin 2) singletonSmall4133) =
      mixedMoment B node692 node692Labels := by
    have ha : raw744 = raw746 := by apply Matrix.ext; unfold raw744 raw746; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4133 = raw746Labels := by decide +kernel
    rw [ha, hj, canonical746 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4134 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4134 node4134Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node564 node564Labels + mixedMoment B node695 node695Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw747 singletonSmall4134
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4134) = raw747Labels := by decide +kernel
  rw [hl, canonical747 B hB] at h
  have hc0 : mixedMoment B raw747 (Fin.cases (0 : Fin 2) singletonSmall4134) =
      mixedMoment B node564 node564Labels := by
    have ha : raw747 = raw748 := by apply Matrix.ext; unfold raw747 raw748; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4134 = raw748Labels := by decide +kernel
    rw [ha, hj, canonical748 B hB]
  have hc1 : mixedMoment B raw747 (Fin.cases (1 : Fin 2) singletonSmall4134) =
      mixedMoment B node695 node695Labels := by
    have ha : raw747 = raw749 := by apply Matrix.ext; unfold raw747 raw749; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4134 = raw749Labels := by decide +kernel
    rw [ha, hj, canonical749 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4135 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4135 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4135 node4135Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node565 node565Labels + mixedMoment B node680 node680Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw750 singletonSmall4135
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4135) = raw750Labels := by decide +kernel
  rw [hl, canonical750 B hB] at h
  have hc0 : mixedMoment B raw750 (Fin.cases (0 : Fin 2) singletonSmall4135) =
      mixedMoment B node565 node565Labels := by
    have ha : raw750 = raw751 := by apply Matrix.ext; unfold raw750 raw751; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4135 = raw751Labels := by decide +kernel
    rw [ha, hj, canonical751 B hB]
  have hc1 : mixedMoment B raw750 (Fin.cases (1 : Fin 2) singletonSmall4135) =
      mixedMoment B node680 node680Labels := by
    have ha : raw750 = raw752 := by apply Matrix.ext; unfold raw750 raw752; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4135 = raw752Labels := by decide +kernel
    rw [ha, hj, canonical752 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4138 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4138 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4138 node4138Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node566 node566Labels + mixedMoment B node694 node694Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw753 singletonSmall4138
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4138) = raw753Labels := by decide +kernel
  rw [hl, canonical753 B hB] at h
  have hc0 : mixedMoment B raw753 (Fin.cases (0 : Fin 2) singletonSmall4138) =
      mixedMoment B node566 node566Labels := by
    have ha : raw753 = raw754 := by apply Matrix.ext; unfold raw753 raw754; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4138 = raw754Labels := by decide +kernel
    rw [ha, hj, canonical754 B hB]
  have hc1 : mixedMoment B raw753 (Fin.cases (1 : Fin 2) singletonSmall4138) =
      mixedMoment B node694 node694Labels := by
    have ha : raw753 = raw755 := by apply Matrix.ext; unfold raw753 raw755; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4138 = raw755Labels := by decide +kernel
    rw [ha, hj, canonical755 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4139 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4139 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4139 node4139Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node567 node567Labels + mixedMoment B node1488 node1488Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw756 singletonSmall4139
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4139) = raw756Labels := by decide +kernel
  rw [hl, canonical756 B hB] at h
  have hc0 : mixedMoment B raw756 (Fin.cases (0 : Fin 2) singletonSmall4139) =
      mixedMoment B node567 node567Labels := by
    have ha : raw756 = raw757 := by apply Matrix.ext; unfold raw756 raw757; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4139 = raw757Labels := by decide +kernel
    rw [ha, hj, canonical757 B hB]
  have hc1 : mixedMoment B raw756 (Fin.cases (1 : Fin 2) singletonSmall4139) =
      mixedMoment B node1488 node1488Labels := by
    have ha : raw756 = raw758 := by apply Matrix.ext; unfold raw756 raw758; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4139 = raw758Labels := by decide +kernel
    rw [ha, hj, canonical758 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4140 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4140 node4140Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node568 node568Labels + mixedMoment B node1489 node1489Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw759 singletonSmall4140
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4140) = raw759Labels := by decide +kernel
  rw [hl, canonical759 B hB] at h
  have hc0 : mixedMoment B raw759 (Fin.cases (0 : Fin 2) singletonSmall4140) =
      mixedMoment B node568 node568Labels := by
    have ha : raw759 = raw760 := by apply Matrix.ext; unfold raw759 raw760; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4140 = raw760Labels := by decide +kernel
    rw [ha, hj, canonical760 B hB]
  have hc1 : mixedMoment B raw759 (Fin.cases (1 : Fin 2) singletonSmall4140) =
      mixedMoment B node1489 node1489Labels := by
    have ha : raw759 = raw761 := by apply Matrix.ext; unfold raw759 raw761; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4140 = raw761Labels := by decide +kernel
    rw [ha, hj, canonical761 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4141 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4141 node4141Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node569 node569Labels + mixedMoment B node1490 node1490Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw762 singletonSmall4141
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4141) = raw762Labels := by decide +kernel
  rw [hl, canonical762 B hB] at h
  have hc0 : mixedMoment B raw762 (Fin.cases (0 : Fin 2) singletonSmall4141) =
      mixedMoment B node569 node569Labels := by
    have ha : raw762 = raw763 := by apply Matrix.ext; unfold raw762 raw763; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4141 = raw763Labels := by decide +kernel
    rw [ha, hj, canonical763 B hB]
  have hc1 : mixedMoment B raw762 (Fin.cases (1 : Fin 2) singletonSmall4141) =
      mixedMoment B node1490 node1490Labels := by
    have ha : raw762 = raw764 := by apply Matrix.ext; unfold raw762 raw764; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4141 = raw764Labels := by decide +kernel
    rw [ha, hj, canonical764 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4142 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4142 node4142Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node570 node570Labels + mixedMoment B node765 node765Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw765 singletonSmall4142
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4142) = raw765Labels := by decide +kernel
  rw [hl, canonical765 B hB] at h
  have hc0 : mixedMoment B raw765 (Fin.cases (0 : Fin 2) singletonSmall4142) =
      mixedMoment B node570 node570Labels := by
    have ha : raw765 = raw766 := by apply Matrix.ext; unfold raw765 raw766; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4142 = raw766Labels := by decide +kernel
    rw [ha, hj, canonical766 B hB]
  have hc1 : mixedMoment B raw765 (Fin.cases (1 : Fin 2) singletonSmall4142) =
      mixedMoment B node765 node765Labels := by
    have ha : raw765 = raw767 := by apply Matrix.ext; unfold raw765 raw767; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4142 = raw767Labels := by decide +kernel
    rw [ha, hj, canonical767 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4143 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4143 node4143Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node571 node571Labels + mixedMoment B node1491 node1491Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw768 singletonSmall4143
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4143) = raw768Labels := by decide +kernel
  rw [hl, canonical768 B hB] at h
  have hc0 : mixedMoment B raw768 (Fin.cases (0 : Fin 2) singletonSmall4143) =
      mixedMoment B node571 node571Labels := by
    have ha : raw768 = raw769 := by apply Matrix.ext; unfold raw768 raw769; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4143 = raw769Labels := by decide +kernel
    rw [ha, hj, canonical769 B hB]
  have hc1 : mixedMoment B raw768 (Fin.cases (1 : Fin 2) singletonSmall4143) =
      mixedMoment B node1491 node1491Labels := by
    have ha : raw768 = raw770 := by apply Matrix.ext; unfold raw768 raw770; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4143 = raw770Labels := by decide +kernel
    rw [ha, hj, canonical770 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4144 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4144 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4144 node4144Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node572 node572Labels + mixedMoment B node1492 node1492Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw771 singletonSmall4144
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4144) = raw771Labels := by decide +kernel
  rw [hl, canonical771 B hB] at h
  have hc0 : mixedMoment B raw771 (Fin.cases (0 : Fin 2) singletonSmall4144) =
      mixedMoment B node572 node572Labels := by
    have ha : raw771 = raw772 := by apply Matrix.ext; unfold raw771 raw772; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4144 = raw772Labels := by decide +kernel
    rw [ha, hj, canonical772 B hB]
  have hc1 : mixedMoment B raw771 (Fin.cases (1 : Fin 2) singletonSmall4144) =
      mixedMoment B node1492 node1492Labels := by
    have ha : raw771 = raw773 := by apply Matrix.ext; unfold raw771 raw773; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4144 = raw773Labels := by decide +kernel
    rw [ha, hj, canonical773 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4145 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4145 node4145Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node573 node573Labels + mixedMoment B node1493 node1493Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw774 singletonSmall4145
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4145) = raw774Labels := by decide +kernel
  rw [hl, canonical774 B hB] at h
  have hc0 : mixedMoment B raw774 (Fin.cases (0 : Fin 2) singletonSmall4145) =
      mixedMoment B node573 node573Labels := by
    have ha : raw774 = raw775 := by apply Matrix.ext; unfold raw774 raw775; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4145 = raw775Labels := by decide +kernel
    rw [ha, hj, canonical775 B hB]
  have hc1 : mixedMoment B raw774 (Fin.cases (1 : Fin 2) singletonSmall4145) =
      mixedMoment B node1493 node1493Labels := by
    have ha : raw774 = raw776 := by apply Matrix.ext; unfold raw774 raw776; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4145 = raw776Labels := by decide +kernel
    rw [ha, hj, canonical776 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4146 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4146 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4146 node4146Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node574 node574Labels + mixedMoment B node1494 node1494Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw777 singletonSmall4146
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4146) = raw777Labels := by decide +kernel
  rw [hl, canonical777 B hB] at h
  have hc0 : mixedMoment B raw777 (Fin.cases (0 : Fin 2) singletonSmall4146) =
      mixedMoment B node574 node574Labels := by
    have ha : raw777 = raw778 := by apply Matrix.ext; unfold raw777 raw778; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4146 = raw778Labels := by decide +kernel
    rw [ha, hj, canonical778 B hB]
  have hc1 : mixedMoment B raw777 (Fin.cases (1 : Fin 2) singletonSmall4146) =
      mixedMoment B node1494 node1494Labels := by
    have ha : raw777 = raw779 := by apply Matrix.ext; unfold raw777 raw779; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4146 = raw779Labels := by decide +kernel
    rw [ha, hj, canonical779 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4147 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4147 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4147 node4147Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node575 node575Labels + mixedMoment B node1495 node1495Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw780 singletonSmall4147
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4147) = raw780Labels := by decide +kernel
  rw [hl, canonical780 B hB] at h
  have hc0 : mixedMoment B raw780 (Fin.cases (0 : Fin 2) singletonSmall4147) =
      mixedMoment B node575 node575Labels := by
    have ha : raw780 = raw781 := by apply Matrix.ext; unfold raw780 raw781; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4147 = raw781Labels := by decide +kernel
    rw [ha, hj, canonical781 B hB]
  have hc1 : mixedMoment B raw780 (Fin.cases (1 : Fin 2) singletonSmall4147) =
      mixedMoment B node1495 node1495Labels := by
    have ha : raw780 = raw782 := by apply Matrix.ext; unfold raw780 raw782; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4147 = raw782Labels := by decide +kernel
    rw [ha, hj, canonical782 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4148 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4148 node4148Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node576 node576Labels + mixedMoment B node1496 node1496Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw783 singletonSmall4148
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4148) = raw783Labels := by decide +kernel
  rw [hl, canonical783 B hB] at h
  have hc0 : mixedMoment B raw783 (Fin.cases (0 : Fin 2) singletonSmall4148) =
      mixedMoment B node576 node576Labels := by
    have ha : raw783 = raw784 := by apply Matrix.ext; unfold raw783 raw784; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4148 = raw784Labels := by decide +kernel
    rw [ha, hj, canonical784 B hB]
  have hc1 : mixedMoment B raw783 (Fin.cases (1 : Fin 2) singletonSmall4148) =
      mixedMoment B node1496 node1496Labels := by
    have ha : raw783 = raw785 := by apply Matrix.ext; unfold raw783 raw785; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4148 = raw785Labels := by decide +kernel
    rw [ha, hj, canonical785 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
