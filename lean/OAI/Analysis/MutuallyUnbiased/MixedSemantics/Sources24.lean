import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical91
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical93
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical97
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical99
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical100
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical101
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical102
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical103

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA768 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB768 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC768 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceForm768 : Integer.Sparse Master := [(Sum.inr 4469, 1), (Sum.inr 4470, 1), (Sum.inr 4471, 1), (Sum.inr 4475, 1), (Sum.inr 4486, 1), (Sum.inr 5082, 1), (Sum.inr 5083, 1), (Sum.inr 5086, 1), (Sum.inr 5091, 1), (Sum.inr 5151, 1), (Sum.inr 5173, 1), (Sum.inr 5197, 1), (Sum.inr 5198, 1), (Sum.inr 5199, 1), (Sum.inr 5204, 1), (Sum.inr 5231, 1), (Sum.inr 5232, 1), (Sum.inr 5233, 1), (Sum.inr 5263, 1), (Sum.inr 5264, 1), (Sum.inr 5267, 1), (Sum.inr 5295, 1), (Sum.inr 5299, 1), (Sum.inr 5300, 1), (Sum.inr 5302, 1), (Sum.inr 5430, 1), (Sum.inr 5432, 1), (Sum.inr 5438, 1), (Sum.inr 5451, 1), (Sum.inr 5473, 1)]

theorem sourceEq768 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm768 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA768 + difference 0 1) (sourceB768 + difference 1 0) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA768 + difference 0 1) (sourceB768 + difference 1 0) sourceC768) = raw12765 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12765; decide +kernel
    rw [ha]
    exact (canonical12765 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA768 + difference 0 2) (sourceB768 + difference 2 0) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA768 + difference 0 2) (sourceB768 + difference 2 0) sourceC768) = raw12766 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12766; decide +kernel
    rw [ha]
    exact (canonical12766 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA768 + difference 0 3) (sourceB768 + difference 3 0) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA768 + difference 0 3) (sourceB768 + difference 3 0) sourceC768) = raw12767 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12767; decide +kernel
    rw [ha]
    exact (canonical12767 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA768 + difference 0 4) (sourceB768 + difference 4 0) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA768 + difference 0 4) (sourceB768 + difference 4 0) sourceC768) = raw12768 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12768; decide +kernel
    rw [ha]
    exact (canonical12768 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA768 + difference 0 5) (sourceB768 + difference 5 0) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA768 + difference 0 5) (sourceB768 + difference 5 0) sourceC768) = raw12769 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12769; decide +kernel
    rw [ha]
    exact (canonical12769 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA768 + difference 1 0) (sourceB768 + difference 0 1) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4469) := by
    have ha : (tripleCharges (sourceA768 + difference 1 0) (sourceB768 + difference 0 1) sourceC768) = raw12770 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12770; decide +kernel
    rw [ha]
    exact (canonical12770 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA768 + difference 1 2) (sourceB768 + difference 2 1) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA768 + difference 1 2) (sourceB768 + difference 2 1) sourceC768) = raw12771 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12771; decide +kernel
    rw [ha]
    exact (canonical12771 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA768 + difference 1 3) (sourceB768 + difference 3 1) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA768 + difference 1 3) (sourceB768 + difference 3 1) sourceC768) = raw12772 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12772; decide +kernel
    rw [ha]
    exact (canonical12772 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA768 + difference 1 4) (sourceB768 + difference 4 1) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA768 + difference 1 4) (sourceB768 + difference 4 1) sourceC768) = raw12773 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12773; decide +kernel
    rw [ha]
    exact (canonical12773 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA768 + difference 1 5) (sourceB768 + difference 5 1) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA768 + difference 1 5) (sourceB768 + difference 5 1) sourceC768) = raw12774 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12774; decide +kernel
    rw [ha]
    exact (canonical12774 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA768 + difference 2 0) (sourceB768 + difference 0 2) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4486) := by
    have ha : (tripleCharges (sourceA768 + difference 2 0) (sourceB768 + difference 0 2) sourceC768) = raw12775 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12775; decide +kernel
    rw [ha]
    exact (canonical12775 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA768 + difference 2 1) (sourceB768 + difference 1 2) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5091) := by
    have ha : (tripleCharges (sourceA768 + difference 2 1) (sourceB768 + difference 1 2) sourceC768) = raw12776 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12776; decide +kernel
    rw [ha]
    exact (canonical12776 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA768 + difference 2 3) (sourceB768 + difference 3 2) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA768 + difference 2 3) (sourceB768 + difference 3 2) sourceC768) = raw12777 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12777; decide +kernel
    rw [ha]
    exact (canonical12777 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA768 + difference 2 4) (sourceB768 + difference 4 2) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA768 + difference 2 4) (sourceB768 + difference 4 2) sourceC768) = raw12778 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12778; decide +kernel
    rw [ha]
    exact (canonical12778 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA768 + difference 2 5) (sourceB768 + difference 5 2) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA768 + difference 2 5) (sourceB768 + difference 5 2) sourceC768) = raw12779 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12779; decide +kernel
    rw [ha]
    exact (canonical12779 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA768 + difference 3 0) (sourceB768 + difference 0 3) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA768 + difference 3 0) (sourceB768 + difference 0 3) sourceC768) = raw12780 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12780; decide +kernel
    rw [ha]
    exact (canonical12780 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA768 + difference 3 1) (sourceB768 + difference 1 3) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA768 + difference 3 1) (sourceB768 + difference 1 3) sourceC768) = raw12781 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12781; decide +kernel
    rw [ha]
    exact (canonical12781 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA768 + difference 3 2) (sourceB768 + difference 2 3) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA768 + difference 3 2) (sourceB768 + difference 2 3) sourceC768) = raw12782 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12782; decide +kernel
    rw [ha]
    exact (canonical12782 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA768 + difference 3 4) (sourceB768 + difference 4 3) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA768 + difference 3 4) (sourceB768 + difference 4 3) sourceC768) = raw12783 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12783; decide +kernel
    rw [ha]
    exact (canonical12783 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA768 + difference 3 5) (sourceB768 + difference 5 3) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA768 + difference 3 5) (sourceB768 + difference 5 3) sourceC768) = raw12784 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12784; decide +kernel
    rw [ha]
    exact (canonical12784 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA768 + difference 4 0) (sourceB768 + difference 0 4) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4471) := by
    have ha : (tripleCharges (sourceA768 + difference 4 0) (sourceB768 + difference 0 4) sourceC768) = raw12785 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12785; decide +kernel
    rw [ha]
    exact (canonical12785 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA768 + difference 4 1) (sourceB768 + difference 1 4) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5083) := by
    have ha : (tripleCharges (sourceA768 + difference 4 1) (sourceB768 + difference 1 4) sourceC768) = raw12786 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12786; decide +kernel
    rw [ha]
    exact (canonical12786 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA768 + difference 4 2) (sourceB768 + difference 2 4) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA768 + difference 4 2) (sourceB768 + difference 2 4) sourceC768) = raw12787 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12787; decide +kernel
    rw [ha]
    exact (canonical12787 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA768 + difference 4 3) (sourceB768 + difference 3 4) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA768 + difference 4 3) (sourceB768 + difference 3 4) sourceC768) = raw12788 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12788; decide +kernel
    rw [ha]
    exact (canonical12788 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA768 + difference 4 5) (sourceB768 + difference 5 4) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA768 + difference 4 5) (sourceB768 + difference 5 4) sourceC768) = raw12789 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12789; decide +kernel
    rw [ha]
    exact (canonical12789 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA768 + difference 5 0) (sourceB768 + difference 0 5) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4470) := by
    have ha : (tripleCharges (sourceA768 + difference 5 0) (sourceB768 + difference 0 5) sourceC768) = raw12790 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12790; decide +kernel
    rw [ha]
    exact (canonical12790 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA768 + difference 5 1) (sourceB768 + difference 1 5) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5082) := by
    have ha : (tripleCharges (sourceA768 + difference 5 1) (sourceB768 + difference 1 5) sourceC768) = raw12791 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12791; decide +kernel
    rw [ha]
    exact (canonical12791 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA768 + difference 5 2) (sourceB768 + difference 2 5) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA768 + difference 5 2) (sourceB768 + difference 2 5) sourceC768) = raw12792 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12792; decide +kernel
    rw [ha]
    exact (canonical12792 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA768 + difference 5 3) (sourceB768 + difference 3 5) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA768 + difference 5 3) (sourceB768 + difference 3 5) sourceC768) = raw12793 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12793; decide +kernel
    rw [ha]
    exact (canonical12793 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA768 + difference 5 4) (sourceB768 + difference 4 5) sourceC768) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA768 + difference 5 4) (sourceB768 + difference 4 5) sourceC768) = raw12794 := by
      apply Matrix.ext; unfold tripleCharges sourceA768 sourceB768 sourceC768 difference raw12794; decide +kernel
    rw [ha]
    exact (canonical12794 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA768 sourceB768 sourceC768
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm768, Integer.Sparse.eval]
  linarith only [hs]

def sourceA769 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB769 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC769 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceForm769 : Integer.Sparse Master := [(Sum.inr 1052, 1), (Sum.inr 1053, 1), (Sum.inr 1054, 1), (Sum.inr 1058, 1), (Sum.inr 1070, 1), (Sum.inr 2490, 1), (Sum.inr 2491, 1), (Sum.inr 2494, 1), (Sum.inr 2500, 1), (Sum.inr 2631, 1), (Sum.inr 2632, 1), (Sum.inr 2633, 1), (Sum.inr 2638, 1), (Sum.inr 2676, 1), (Sum.inr 2677, 1), (Sum.inr 2678, 1), (Sum.inr 2681, 1), (Sum.inr 2728, 1), (Sum.inr 2729, 1), (Sum.inr 2732, 1), (Sum.inr 2735, 1), (Sum.inr 2773, 1), (Sum.inr 2774, 1), (Sum.inr 2776, 1), (Sum.inr 2781, 1), (Sum.inr 3850, 1), (Sum.inr 3871, 1), (Sum.inr 3876, 1), (Sum.inr 3888, 1), (Sum.inr 3995, 1)]

theorem sourceEq769 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm769 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA769 + difference 0 1) (sourceB769 + difference 1 0) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA769 + difference 0 1) (sourceB769 + difference 1 0) sourceC769) = raw12795 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12795; decide +kernel
    rw [ha]
    exact (canonical12795 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA769 + difference 0 2) (sourceB769 + difference 2 0) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA769 + difference 0 2) (sourceB769 + difference 2 0) sourceC769) = raw12796 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12796; decide +kernel
    rw [ha]
    exact (canonical12796 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA769 + difference 0 3) (sourceB769 + difference 3 0) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA769 + difference 0 3) (sourceB769 + difference 3 0) sourceC769) = raw12797 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12797; decide +kernel
    rw [ha]
    exact (canonical12797 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA769 + difference 0 4) (sourceB769 + difference 4 0) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA769 + difference 0 4) (sourceB769 + difference 4 0) sourceC769) = raw12798 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12798; decide +kernel
    rw [ha]
    exact (canonical12798 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA769 + difference 0 5) (sourceB769 + difference 5 0) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA769 + difference 0 5) (sourceB769 + difference 5 0) sourceC769) = raw12799 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12799; decide +kernel
    rw [ha]
    exact (canonical12799 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA769 + difference 1 0) (sourceB769 + difference 0 1) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1052) := by
    have ha : (tripleCharges (sourceA769 + difference 1 0) (sourceB769 + difference 0 1) sourceC769) = raw12800 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12800; decide +kernel
    rw [ha]
    exact (canonical12800 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA769 + difference 1 2) (sourceB769 + difference 2 1) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2631) := by
    have ha : (tripleCharges (sourceA769 + difference 1 2) (sourceB769 + difference 2 1) sourceC769) = raw12801 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12801; decide +kernel
    rw [ha]
    exact (canonical12801 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA769 + difference 1 3) (sourceB769 + difference 3 1) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA769 + difference 1 3) (sourceB769 + difference 3 1) sourceC769) = raw12802 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12802; decide +kernel
    rw [ha]
    exact (canonical12802 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA769 + difference 1 4) (sourceB769 + difference 4 1) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA769 + difference 1 4) (sourceB769 + difference 4 1) sourceC769) = raw12803 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12803; decide +kernel
    rw [ha]
    exact (canonical12803 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA769 + difference 1 5) (sourceB769 + difference 5 1) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA769 + difference 1 5) (sourceB769 + difference 5 1) sourceC769) = raw12804 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12804; decide +kernel
    rw [ha]
    exact (canonical12804 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA769 + difference 2 0) (sourceB769 + difference 0 2) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1070) := by
    have ha : (tripleCharges (sourceA769 + difference 2 0) (sourceB769 + difference 0 2) sourceC769) = raw12805 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12805; decide +kernel
    rw [ha]
    exact (canonical12805 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA769 + difference 2 1) (sourceB769 + difference 1 2) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2500) := by
    have ha : (tripleCharges (sourceA769 + difference 2 1) (sourceB769 + difference 1 2) sourceC769) = raw12806 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12806; decide +kernel
    rw [ha]
    exact (canonical12806 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA769 + difference 2 3) (sourceB769 + difference 3 2) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA769 + difference 2 3) (sourceB769 + difference 3 2) sourceC769) = raw12807 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12807; decide +kernel
    rw [ha]
    exact (canonical12807 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA769 + difference 2 4) (sourceB769 + difference 4 2) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA769 + difference 2 4) (sourceB769 + difference 4 2) sourceC769) = raw12808 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12808; decide +kernel
    rw [ha]
    exact (canonical12808 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA769 + difference 2 5) (sourceB769 + difference 5 2) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA769 + difference 2 5) (sourceB769 + difference 5 2) sourceC769) = raw12809 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12809; decide +kernel
    rw [ha]
    exact (canonical12809 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA769 + difference 3 0) (sourceB769 + difference 0 3) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA769 + difference 3 0) (sourceB769 + difference 0 3) sourceC769) = raw12810 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12810; decide +kernel
    rw [ha]
    exact (canonical12810 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA769 + difference 3 1) (sourceB769 + difference 1 3) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA769 + difference 3 1) (sourceB769 + difference 1 3) sourceC769) = raw12811 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12811; decide +kernel
    rw [ha]
    exact (canonical12811 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA769 + difference 3 2) (sourceB769 + difference 2 3) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2638) := by
    have ha : (tripleCharges (sourceA769 + difference 3 2) (sourceB769 + difference 2 3) sourceC769) = raw12812 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12812; decide +kernel
    rw [ha]
    exact (canonical12812 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA769 + difference 3 4) (sourceB769 + difference 4 3) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA769 + difference 3 4) (sourceB769 + difference 4 3) sourceC769) = raw12813 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12813; decide +kernel
    rw [ha]
    exact (canonical12813 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA769 + difference 3 5) (sourceB769 + difference 5 3) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA769 + difference 3 5) (sourceB769 + difference 5 3) sourceC769) = raw12814 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12814; decide +kernel
    rw [ha]
    exact (canonical12814 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA769 + difference 4 0) (sourceB769 + difference 0 4) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1054) := by
    have ha : (tripleCharges (sourceA769 + difference 4 0) (sourceB769 + difference 0 4) sourceC769) = raw12815 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12815; decide +kernel
    rw [ha]
    exact (canonical12815 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA769 + difference 4 1) (sourceB769 + difference 1 4) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2491) := by
    have ha : (tripleCharges (sourceA769 + difference 4 1) (sourceB769 + difference 1 4) sourceC769) = raw12816 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12816; decide +kernel
    rw [ha]
    exact (canonical12816 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA769 + difference 4 2) (sourceB769 + difference 2 4) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA769 + difference 4 2) (sourceB769 + difference 2 4) sourceC769) = raw12817 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12817; decide +kernel
    rw [ha]
    exact (canonical12817 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA769 + difference 4 3) (sourceB769 + difference 3 4) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA769 + difference 4 3) (sourceB769 + difference 3 4) sourceC769) = raw12818 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12818; decide +kernel
    rw [ha]
    exact (canonical12818 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA769 + difference 4 5) (sourceB769 + difference 5 4) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA769 + difference 4 5) (sourceB769 + difference 5 4) sourceC769) = raw12819 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12819; decide +kernel
    rw [ha]
    exact (canonical12819 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA769 + difference 5 0) (sourceB769 + difference 0 5) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1053) := by
    have ha : (tripleCharges (sourceA769 + difference 5 0) (sourceB769 + difference 0 5) sourceC769) = raw12820 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12820; decide +kernel
    rw [ha]
    exact (canonical12820 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA769 + difference 5 1) (sourceB769 + difference 1 5) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2490) := by
    have ha : (tripleCharges (sourceA769 + difference 5 1) (sourceB769 + difference 1 5) sourceC769) = raw12821 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12821; decide +kernel
    rw [ha]
    exact (canonical12821 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA769 + difference 5 2) (sourceB769 + difference 2 5) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2632) := by
    have ha : (tripleCharges (sourceA769 + difference 5 2) (sourceB769 + difference 2 5) sourceC769) = raw12822 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12822; decide +kernel
    rw [ha]
    exact (canonical12822 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA769 + difference 5 3) (sourceB769 + difference 3 5) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA769 + difference 5 3) (sourceB769 + difference 3 5) sourceC769) = raw12823 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12823; decide +kernel
    rw [ha]
    exact (canonical12823 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA769 + difference 5 4) (sourceB769 + difference 4 5) sourceC769) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA769 + difference 5 4) (sourceB769 + difference 4 5) sourceC769) = raw12824 := by
      apply Matrix.ext; unfold tripleCharges sourceA769 sourceB769 sourceC769 difference raw12824; decide +kernel
    rw [ha]
    exact (canonical12824 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA769 sourceB769 sourceC769
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm769, Integer.Sparse.eval]
  linarith only [hs]

def sourceA770 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB770 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC770 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceForm770 : Integer.Sparse Master := [(Sum.inr 1638, 1), (Sum.inr 1639, 1), (Sum.inr 1640, 1), (Sum.inr 1649, 1), (Sum.inr 1715, 1), (Sum.inr 2921, 1), (Sum.inr 2930, 1), (Sum.inr 2952, 1), (Sum.inr 3098, 1), (Sum.inr 3378, 1), (Sum.inr 3379, 1), (Sum.inr 3395, 1), (Sum.inr 3441, 1), (Sum.inr 3447, 1), (Sum.inr 3464, 1), (Sum.inr 3505, 1), (Sum.inr 3506, 1), (Sum.inr 3541, 1), (Sum.inr 3569, 1), (Sum.inr 3570, 1), (Sum.inr 3573, 1), (Sum.inr 3578, 1), (Sum.inr 3584, 1), (Sum.inr 3624, 1), (Sum.inr 3626, 1), (Sum.inr 3958, 1), (Sum.inr 3972, 1), (Sum.inr 3987, 1), (Sum.inr 3993, 1), (Sum.inr 4027, 1)]

theorem sourceEq770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm770 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA770 + difference 0 1) (sourceB770 + difference 1 0) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA770 + difference 0 1) (sourceB770 + difference 1 0) sourceC770) = raw12825 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12825; decide +kernel
    rw [ha]
    exact (canonical12825 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA770 + difference 0 2) (sourceB770 + difference 2 0) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA770 + difference 0 2) (sourceB770 + difference 2 0) sourceC770) = raw12826 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12826; decide +kernel
    rw [ha]
    exact (canonical12826 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA770 + difference 0 3) (sourceB770 + difference 3 0) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4027) := by
    have ha : (tripleCharges (sourceA770 + difference 0 3) (sourceB770 + difference 3 0) sourceC770) = raw12827 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12827; decide +kernel
    rw [ha]
    exact (canonical12827 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA770 + difference 0 4) (sourceB770 + difference 4 0) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA770 + difference 0 4) (sourceB770 + difference 4 0) sourceC770) = raw12828 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12828; decide +kernel
    rw [ha]
    exact (canonical12828 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA770 + difference 0 5) (sourceB770 + difference 5 0) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA770 + difference 0 5) (sourceB770 + difference 5 0) sourceC770) = raw12829 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12829; decide +kernel
    rw [ha]
    exact (canonical12829 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA770 + difference 1 0) (sourceB770 + difference 0 1) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1638) := by
    have ha : (tripleCharges (sourceA770 + difference 1 0) (sourceB770 + difference 0 1) sourceC770) = raw12830 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12830; decide +kernel
    rw [ha]
    exact (canonical12830 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA770 + difference 1 2) (sourceB770 + difference 2 1) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3569) := by
    have ha : (tripleCharges (sourceA770 + difference 1 2) (sourceB770 + difference 2 1) sourceC770) = raw12831 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12831; decide +kernel
    rw [ha]
    exact (canonical12831 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA770 + difference 1 3) (sourceB770 + difference 3 1) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3378) := by
    have ha : (tripleCharges (sourceA770 + difference 1 3) (sourceB770 + difference 3 1) sourceC770) = raw12832 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12832; decide +kernel
    rw [ha]
    exact (canonical12832 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA770 + difference 1 4) (sourceB770 + difference 4 1) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3505) := by
    have ha : (tripleCharges (sourceA770 + difference 1 4) (sourceB770 + difference 4 1) sourceC770) = raw12833 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12833; decide +kernel
    rw [ha]
    exact (canonical12833 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA770 + difference 1 5) (sourceB770 + difference 5 1) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA770 + difference 1 5) (sourceB770 + difference 5 1) sourceC770) = raw12834 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12834; decide +kernel
    rw [ha]
    exact (canonical12834 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA770 + difference 2 0) (sourceB770 + difference 0 2) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1639) := by
    have ha : (tripleCharges (sourceA770 + difference 2 0) (sourceB770 + difference 0 2) sourceC770) = raw12835 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12835; decide +kernel
    rw [ha]
    exact (canonical12835 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA770 + difference 2 1) (sourceB770 + difference 1 2) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2921) := by
    have ha : (tripleCharges (sourceA770 + difference 2 1) (sourceB770 + difference 1 2) sourceC770) = raw12836 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12836; decide +kernel
    rw [ha]
    exact (canonical12836 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA770 + difference 2 3) (sourceB770 + difference 3 2) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA770 + difference 2 3) (sourceB770 + difference 3 2) sourceC770) = raw12837 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12837; decide +kernel
    rw [ha]
    exact (canonical12837 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA770 + difference 2 4) (sourceB770 + difference 4 2) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA770 + difference 2 4) (sourceB770 + difference 4 2) sourceC770) = raw12838 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12838; decide +kernel
    rw [ha]
    exact (canonical12838 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA770 + difference 2 5) (sourceB770 + difference 5 2) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA770 + difference 2 5) (sourceB770 + difference 5 2) sourceC770) = raw12839 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12839; decide +kernel
    rw [ha]
    exact (canonical12839 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA770 + difference 3 0) (sourceB770 + difference 0 3) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA770 + difference 3 0) (sourceB770 + difference 0 3) sourceC770) = raw12840 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12840; decide +kernel
    rw [ha]
    exact (canonical12840 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA770 + difference 3 1) (sourceB770 + difference 1 3) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA770 + difference 3 1) (sourceB770 + difference 1 3) sourceC770) = raw12841 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12841; decide +kernel
    rw [ha]
    exact (canonical12841 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA770 + difference 3 2) (sourceB770 + difference 2 3) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA770 + difference 3 2) (sourceB770 + difference 2 3) sourceC770) = raw12842 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12842; decide +kernel
    rw [ha]
    exact (canonical12842 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA770 + difference 3 4) (sourceB770 + difference 4 3) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA770 + difference 3 4) (sourceB770 + difference 4 3) sourceC770) = raw12843 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12843; decide +kernel
    rw [ha]
    exact (canonical12843 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA770 + difference 3 5) (sourceB770 + difference 5 3) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA770 + difference 3 5) (sourceB770 + difference 5 3) sourceC770) = raw12844 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12844; decide +kernel
    rw [ha]
    exact (canonical12844 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA770 + difference 4 0) (sourceB770 + difference 0 4) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1649) := by
    have ha : (tripleCharges (sourceA770 + difference 4 0) (sourceB770 + difference 0 4) sourceC770) = raw12845 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12845; decide +kernel
    rw [ha]
    exact (canonical12845 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA770 + difference 4 1) (sourceB770 + difference 1 4) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3447) := by
    have ha : (tripleCharges (sourceA770 + difference 4 1) (sourceB770 + difference 1 4) sourceC770) = raw12846 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12846; decide +kernel
    rw [ha]
    exact (canonical12846 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA770 + difference 4 2) (sourceB770 + difference 2 4) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA770 + difference 4 2) (sourceB770 + difference 2 4) sourceC770) = raw12847 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12847; decide +kernel
    rw [ha]
    exact (canonical12847 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA770 + difference 4 3) (sourceB770 + difference 3 4) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA770 + difference 4 3) (sourceB770 + difference 3 4) sourceC770) = raw12848 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12848; decide +kernel
    rw [ha]
    exact (canonical12848 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA770 + difference 4 5) (sourceB770 + difference 5 4) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA770 + difference 4 5) (sourceB770 + difference 5 4) sourceC770) = raw12849 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12849; decide +kernel
    rw [ha]
    exact (canonical12849 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA770 + difference 5 0) (sourceB770 + difference 0 5) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1640) := by
    have ha : (tripleCharges (sourceA770 + difference 5 0) (sourceB770 + difference 0 5) sourceC770) = raw12850 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12850; decide +kernel
    rw [ha]
    exact (canonical12850 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA770 + difference 5 1) (sourceB770 + difference 1 5) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3441) := by
    have ha : (tripleCharges (sourceA770 + difference 5 1) (sourceB770 + difference 1 5) sourceC770) = raw12851 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12851; decide +kernel
    rw [ha]
    exact (canonical12851 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA770 + difference 5 2) (sourceB770 + difference 2 5) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA770 + difference 5 2) (sourceB770 + difference 2 5) sourceC770) = raw12852 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12852; decide +kernel
    rw [ha]
    exact (canonical12852 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA770 + difference 5 3) (sourceB770 + difference 3 5) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3379) := by
    have ha : (tripleCharges (sourceA770 + difference 5 3) (sourceB770 + difference 3 5) sourceC770) = raw12853 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12853; decide +kernel
    rw [ha]
    exact (canonical12853 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA770 + difference 5 4) (sourceB770 + difference 4 5) sourceC770) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3506) := by
    have ha : (tripleCharges (sourceA770 + difference 5 4) (sourceB770 + difference 4 5) sourceC770) = raw12854 := by
      apply Matrix.ext; unfold tripleCharges sourceA770 sourceB770 sourceC770 difference raw12854; decide +kernel
    rw [ha]
    exact (canonical12854 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA770 sourceB770 sourceC770
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm770, Integer.Sparse.eval]
  linarith only [hs]

def sourceA771 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB771 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC771 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceForm771 : Integer.Sparse Master := [(Sum.inr 3051, 1), (Sum.inr 3848, 1), (Sum.inr 3850, 1), (Sum.inr 3857, 1), (Sum.inr 3913, 1), (Sum.inr 3961, 1), (Sum.inr 4092, -1)]

theorem sourceEq771 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm771 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA771 + difference 0 0) (sourceB771 + difference 0 0) sourceC771) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA771 + difference 0 0) (sourceB771 + difference 0 0) sourceC771) = raw12855 := by
      apply Matrix.ext; unfold tripleCharges sourceA771 sourceB771 sourceC771 difference raw12855; decide +kernel
    rw [ha]
    exact (canonical12855 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA771 + difference 0 1) (sourceB771 + difference 1 0) sourceC771) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA771 + difference 0 1) (sourceB771 + difference 1 0) sourceC771) = raw12856 := by
      apply Matrix.ext; unfold tripleCharges sourceA771 sourceB771 sourceC771 difference raw12856; decide +kernel
    rw [ha]
    exact (canonical12856 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA771 + difference 0 2) (sourceB771 + difference 2 0) sourceC771) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA771 + difference 0 2) (sourceB771 + difference 2 0) sourceC771) = raw12857 := by
      apply Matrix.ext; unfold tripleCharges sourceA771 sourceB771 sourceC771 difference raw12857; decide +kernel
    rw [ha]
    exact (canonical12857 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA771 + difference 0 3) (sourceB771 + difference 3 0) sourceC771) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA771 + difference 0 3) (sourceB771 + difference 3 0) sourceC771) = raw12858 := by
      apply Matrix.ext; unfold tripleCharges sourceA771 sourceB771 sourceC771 difference raw12858; decide +kernel
    rw [ha]
    exact (canonical12858 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA771 + difference 0 4) (sourceB771 + difference 4 0) sourceC771) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA771 + difference 0 4) (sourceB771 + difference 4 0) sourceC771) = raw12859 := by
      apply Matrix.ext; unfold tripleCharges sourceA771 sourceB771 sourceC771 difference raw12859; decide +kernel
    rw [ha]
    exact (canonical12859 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA771 + difference 0 5) (sourceB771 + difference 5 0) sourceC771) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA771 + difference 0 5) (sourceB771 + difference 5 0) sourceC771) = raw12860 := by
      apply Matrix.ext; unfold tripleCharges sourceA771 sourceB771 sourceC771 difference raw12860; decide +kernel
    rw [ha]
    exact (canonical12860 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA771 + sourceB771) sourceC771) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA771 + sourceB771) sourceC771) = raw12861 := by
      apply Matrix.ext; unfold doubleCharges sourceA771 sourceB771 sourceC771 raw12861; decide +kernel
    rw [ha]
    exact (canonical12861 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA771 sourceB771 sourceC771
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm771, Integer.Sparse.eval]
  linarith only [hs]

def sourceA772 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB772 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC772 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceForm772 : Integer.Sparse Master := [(Sum.inr 1364, 1), (Sum.inr 1367, 1), (Sum.inr 1368, 1), (Sum.inr 1371, 1), (Sum.inr 1433, 1), (Sum.inr 3051, 1), (Sum.inr 4092, -1)]

theorem sourceEq772 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm772 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA772 + difference 0 0) (sourceB772 + difference 0 0) sourceC772) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA772 + difference 0 0) (sourceB772 + difference 0 0) sourceC772) = raw12855 := by
      apply Matrix.ext; unfold tripleCharges sourceA772 sourceB772 sourceC772 difference raw12855; decide +kernel
    rw [ha]
    exact (canonical12855 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA772 + difference 1 0) (sourceB772 + difference 0 1) sourceC772) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1364) := by
    have ha : (tripleCharges (sourceA772 + difference 1 0) (sourceB772 + difference 0 1) sourceC772) = raw12862 := by
      apply Matrix.ext; unfold tripleCharges sourceA772 sourceB772 sourceC772 difference raw12862; decide +kernel
    rw [ha]
    exact (canonical12862 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA772 + difference 2 0) (sourceB772 + difference 0 2) sourceC772) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1433) := by
    have ha : (tripleCharges (sourceA772 + difference 2 0) (sourceB772 + difference 0 2) sourceC772) = raw12863 := by
      apply Matrix.ext; unfold tripleCharges sourceA772 sourceB772 sourceC772 difference raw12863; decide +kernel
    rw [ha]
    exact (canonical12863 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA772 + difference 3 0) (sourceB772 + difference 0 3) sourceC772) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA772 + difference 3 0) (sourceB772 + difference 0 3) sourceC772) = raw12864 := by
      apply Matrix.ext; unfold tripleCharges sourceA772 sourceB772 sourceC772 difference raw12864; decide +kernel
    rw [ha]
    exact (canonical12864 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA772 + difference 4 0) (sourceB772 + difference 0 4) sourceC772) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1368) := by
    have ha : (tripleCharges (sourceA772 + difference 4 0) (sourceB772 + difference 0 4) sourceC772) = raw12865 := by
      apply Matrix.ext; unfold tripleCharges sourceA772 sourceB772 sourceC772 difference raw12865; decide +kernel
    rw [ha]
    exact (canonical12865 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA772 + difference 5 0) (sourceB772 + difference 0 5) sourceC772) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1371) := by
    have ha : (tripleCharges (sourceA772 + difference 5 0) (sourceB772 + difference 0 5) sourceC772) = raw12866 := by
      apply Matrix.ext; unfold tripleCharges sourceA772 sourceB772 sourceC772 difference raw12866; decide +kernel
    rw [ha]
    exact (canonical12866 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA772 + sourceB772) sourceC772) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA772 + sourceB772) sourceC772) = raw12861 := by
      apply Matrix.ext; unfold doubleCharges sourceA772 sourceB772 sourceC772 raw12861; decide +kernel
    rw [ha]
    exact (canonical12861 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA772 sourceB772 sourceC772
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm772, Integer.Sparse.eval]
  linarith only [hs]

def sourceA773 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB773 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC773 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceForm773 : Integer.Sparse Master := [(Sum.inr 1364, 1), (Sum.inr 2878, 1), (Sum.inr 3036, 1), (Sum.inr 3043, 1), (Sum.inr 3051, 2), (Sum.inr 4092, -1)]

theorem sourceEq773 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm773 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA773 + difference 1 0) (sourceB773 + difference 0 1) sourceC773) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1364) := by
    have ha : (tripleCharges (sourceA773 + difference 1 0) (sourceB773 + difference 0 1) sourceC773) = raw12862 := by
      apply Matrix.ext; unfold tripleCharges sourceA773 sourceB773 sourceC773 difference raw12862; decide +kernel
    rw [ha]
    exact (canonical12862 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA773 + difference 1 1) (sourceB773 + difference 1 1) sourceC773) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA773 + difference 1 1) (sourceB773 + difference 1 1) sourceC773) = raw12855 := by
      apply Matrix.ext; unfold tripleCharges sourceA773 sourceB773 sourceC773 difference raw12855; decide +kernel
    rw [ha]
    exact (canonical12855 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA773 + difference 1 2) (sourceB773 + difference 2 1) sourceC773) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2878) := by
    have ha : (tripleCharges (sourceA773 + difference 1 2) (sourceB773 + difference 2 1) sourceC773) = raw12867 := by
      apply Matrix.ext; unfold tripleCharges sourceA773 sourceB773 sourceC773 difference raw12867; decide +kernel
    rw [ha]
    exact (canonical12867 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA773 + difference 1 3) (sourceB773 + difference 3 1) sourceC773) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3043) := by
    have ha : (tripleCharges (sourceA773 + difference 1 3) (sourceB773 + difference 3 1) sourceC773) = raw12868 := by
      apply Matrix.ext; unfold tripleCharges sourceA773 sourceB773 sourceC773 difference raw12868; decide +kernel
    rw [ha]
    exact (canonical12868 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA773 + difference 1 4) (sourceB773 + difference 4 1) sourceC773) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3036) := by
    have ha : (tripleCharges (sourceA773 + difference 1 4) (sourceB773 + difference 4 1) sourceC773) = raw12869 := by
      apply Matrix.ext; unfold tripleCharges sourceA773 sourceB773 sourceC773 difference raw12869; decide +kernel
    rw [ha]
    exact (canonical12869 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA773 + difference 1 5) (sourceB773 + difference 5 1) sourceC773) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA773 + difference 1 5) (sourceB773 + difference 5 1) sourceC773) = raw12870 := by
      apply Matrix.ext; unfold tripleCharges sourceA773 sourceB773 sourceC773 difference raw12870; decide +kernel
    rw [ha]
    exact (canonical12870 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA773 + sourceB773) sourceC773) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA773 + sourceB773) sourceC773) = raw12861 := by
      apply Matrix.ext; unfold doubleCharges sourceA773 sourceB773 sourceC773 raw12861; decide +kernel
    rw [ha]
    exact (canonical12861 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA773 sourceB773 sourceC773
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm773, Integer.Sparse.eval]
  linarith only [hs]

def sourceA774 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB774 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC774 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceForm774 : Integer.Sparse Master := [(Sum.inr 2571, 1), (Sum.inr 2974, 1), (Sum.inr 2975, 1), (Sum.inr 2977, 1), (Sum.inr 3051, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

theorem sourceEq774 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm774 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA774 + difference 0 1) (sourceB774 + difference 1 0) sourceC774) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA774 + difference 0 1) (sourceB774 + difference 1 0) sourceC774) = raw12856 := by
      apply Matrix.ext; unfold tripleCharges sourceA774 sourceB774 sourceC774 difference raw12856; decide +kernel
    rw [ha]
    exact (canonical12856 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA774 + difference 1 1) (sourceB774 + difference 1 1) sourceC774) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA774 + difference 1 1) (sourceB774 + difference 1 1) sourceC774) = raw12855 := by
      apply Matrix.ext; unfold tripleCharges sourceA774 sourceB774 sourceC774 difference raw12855; decide +kernel
    rw [ha]
    exact (canonical12855 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA774 + difference 2 1) (sourceB774 + difference 1 2) sourceC774) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2571) := by
    have ha : (tripleCharges (sourceA774 + difference 2 1) (sourceB774 + difference 1 2) sourceC774) = raw12871 := by
      apply Matrix.ext; unfold tripleCharges sourceA774 sourceB774 sourceC774 difference raw12871; decide +kernel
    rw [ha]
    exact (canonical12871 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA774 + difference 3 1) (sourceB774 + difference 1 3) sourceC774) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA774 + difference 3 1) (sourceB774 + difference 1 3) sourceC774) = raw12872 := by
      apply Matrix.ext; unfold tripleCharges sourceA774 sourceB774 sourceC774 difference raw12872; decide +kernel
    rw [ha]
    exact (canonical12872 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA774 + difference 4 1) (sourceB774 + difference 1 4) sourceC774) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2975) := by
    have ha : (tripleCharges (sourceA774 + difference 4 1) (sourceB774 + difference 1 4) sourceC774) = raw12873 := by
      apply Matrix.ext; unfold tripleCharges sourceA774 sourceB774 sourceC774 difference raw12873; decide +kernel
    rw [ha]
    exact (canonical12873 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA774 + difference 5 1) (sourceB774 + difference 1 5) sourceC774) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2977) := by
    have ha : (tripleCharges (sourceA774 + difference 5 1) (sourceB774 + difference 1 5) sourceC774) = raw12874 := by
      apply Matrix.ext; unfold tripleCharges sourceA774 sourceB774 sourceC774 difference raw12874; decide +kernel
    rw [ha]
    exact (canonical12874 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA774 + sourceB774) sourceC774) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA774 + sourceB774) sourceC774) = raw12861 := by
      apply Matrix.ext; unfold doubleCharges sourceA774 sourceB774 sourceC774 raw12861; decide +kernel
    rw [ha]
    exact (canonical12861 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA774 sourceB774 sourceC774
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm774, Integer.Sparse.eval]
  linarith only [hs]

def sourceA775 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB775 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC775 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceForm775 : Integer.Sparse Master := [(Sum.inr 2878, 1), (Sum.inr 2881, 1), (Sum.inr 2882, 1), (Sum.inr 2885, 1), (Sum.inr 3051, 1), (Sum.inr 3961, 1), (Sum.inr 4092, -1)]

theorem sourceEq775 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm775 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA775 + difference 0 2) (sourceB775 + difference 2 0) sourceC775) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA775 + difference 0 2) (sourceB775 + difference 2 0) sourceC775) = raw12857 := by
      apply Matrix.ext; unfold tripleCharges sourceA775 sourceB775 sourceC775 difference raw12857; decide +kernel
    rw [ha]
    exact (canonical12857 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA775 + difference 1 2) (sourceB775 + difference 2 1) sourceC775) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2878) := by
    have ha : (tripleCharges (sourceA775 + difference 1 2) (sourceB775 + difference 2 1) sourceC775) = raw12867 := by
      apply Matrix.ext; unfold tripleCharges sourceA775 sourceB775 sourceC775 difference raw12867; decide +kernel
    rw [ha]
    exact (canonical12867 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA775 + difference 2 2) (sourceB775 + difference 2 2) sourceC775) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA775 + difference 2 2) (sourceB775 + difference 2 2) sourceC775) = raw12855 := by
      apply Matrix.ext; unfold tripleCharges sourceA775 sourceB775 sourceC775 difference raw12855; decide +kernel
    rw [ha]
    exact (canonical12855 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA775 + difference 3 2) (sourceB775 + difference 2 3) sourceC775) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA775 + difference 3 2) (sourceB775 + difference 2 3) sourceC775) = raw12875 := by
      apply Matrix.ext; unfold tripleCharges sourceA775 sourceB775 sourceC775 difference raw12875; decide +kernel
    rw [ha]
    exact (canonical12875 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA775 + difference 4 2) (sourceB775 + difference 2 4) sourceC775) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA775 + difference 4 2) (sourceB775 + difference 2 4) sourceC775) = raw12876 := by
      apply Matrix.ext; unfold tripleCharges sourceA775 sourceB775 sourceC775 difference raw12876; decide +kernel
    rw [ha]
    exact (canonical12876 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA775 + difference 5 2) (sourceB775 + difference 2 5) sourceC775) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2885) := by
    have ha : (tripleCharges (sourceA775 + difference 5 2) (sourceB775 + difference 2 5) sourceC775) = raw12877 := by
      apply Matrix.ext; unfold tripleCharges sourceA775 sourceB775 sourceC775 difference raw12877; decide +kernel
    rw [ha]
    exact (canonical12877 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA775 + sourceB775) sourceC775) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA775 + sourceB775) sourceC775) = raw12861 := by
      apply Matrix.ext; unfold doubleCharges sourceA775 sourceB775 sourceC775 raw12861; decide +kernel
    rw [ha]
    exact (canonical12861 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA775 sourceB775 sourceC775
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm775, Integer.Sparse.eval]
  linarith only [hs]

def sourceA776 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB776 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC776 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceForm776 : Integer.Sparse Master := [(Sum.inr 2575, 1), (Sum.inr 3043, 1), (Sum.inr 3044, 1), (Sum.inr 3045, 1), (Sum.inr 3051, 1), (Sum.inr 3850, 1), (Sum.inr 4092, -1)]

theorem sourceEq776 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm776 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA776 + difference 0 3) (sourceB776 + difference 3 0) sourceC776) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA776 + difference 0 3) (sourceB776 + difference 3 0) sourceC776) = raw12858 := by
      apply Matrix.ext; unfold tripleCharges sourceA776 sourceB776 sourceC776 difference raw12858; decide +kernel
    rw [ha]
    exact (canonical12858 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA776 + difference 1 3) (sourceB776 + difference 3 1) sourceC776) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3043) := by
    have ha : (tripleCharges (sourceA776 + difference 1 3) (sourceB776 + difference 3 1) sourceC776) = raw12868 := by
      apply Matrix.ext; unfold tripleCharges sourceA776 sourceB776 sourceC776 difference raw12868; decide +kernel
    rw [ha]
    exact (canonical12868 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA776 + difference 2 3) (sourceB776 + difference 3 2) sourceC776) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2575) := by
    have ha : (tripleCharges (sourceA776 + difference 2 3) (sourceB776 + difference 3 2) sourceC776) = raw12878 := by
      apply Matrix.ext; unfold tripleCharges sourceA776 sourceB776 sourceC776 difference raw12878; decide +kernel
    rw [ha]
    exact (canonical12878 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA776 + difference 3 3) (sourceB776 + difference 3 3) sourceC776) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA776 + difference 3 3) (sourceB776 + difference 3 3) sourceC776) = raw12855 := by
      apply Matrix.ext; unfold tripleCharges sourceA776 sourceB776 sourceC776 difference raw12855; decide +kernel
    rw [ha]
    exact (canonical12855 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA776 + difference 4 3) (sourceB776 + difference 3 4) sourceC776) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3044) := by
    have ha : (tripleCharges (sourceA776 + difference 4 3) (sourceB776 + difference 3 4) sourceC776) = raw12879 := by
      apply Matrix.ext; unfold tripleCharges sourceA776 sourceB776 sourceC776 difference raw12879; decide +kernel
    rw [ha]
    exact (canonical12879 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA776 + difference 5 3) (sourceB776 + difference 3 5) sourceC776) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3045) := by
    have ha : (tripleCharges (sourceA776 + difference 5 3) (sourceB776 + difference 3 5) sourceC776) = raw12880 := by
      apply Matrix.ext; unfold tripleCharges sourceA776 sourceB776 sourceC776 difference raw12880; decide +kernel
    rw [ha]
    exact (canonical12880 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA776 + sourceB776) sourceC776) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA776 + sourceB776) sourceC776) = raw12861 := by
      apply Matrix.ext; unfold doubleCharges sourceA776 sourceB776 sourceC776 raw12861; decide +kernel
    rw [ha]
    exact (canonical12861 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA776 sourceB776 sourceC776
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm776, Integer.Sparse.eval]
  linarith only [hs]

def sourceA777 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB777 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC777 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm777 : Integer.Sparse Master := [(Sum.inr 4806, 1), (Sum.inr 4808, 1), (Sum.inr 4809, 1), (Sum.inr 4842, 1), (Sum.inr 4852, 1), (Sum.inr 4856, 1), (Sum.inr 4869, 1), (Sum.inr 4879, 1), (Sum.inr 4889, 1), (Sum.inr 5143, 1), (Sum.inr 5151, 1), (Sum.inr 5158, 1), (Sum.inr 5226, 1), (Sum.inr 5236, 1), (Sum.inr 5237, 1), (Sum.inr 5262, 1), (Sum.inr 5263, 1), (Sum.inr 5265, 1), (Sum.inr 5271, 1), (Sum.inr 5279, 1), (Sum.inr 5281, 1), (Sum.inr 5285, 1), (Sum.inr 5286, 1), (Sum.inr 5289, 1), (Sum.inr 5290, 1), (Sum.inr 5292, 1), (Sum.inr 5298, 1), (Sum.inr 5299, 2), (Sum.inr 5301, 1)]

theorem sourceEq777 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm777 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA777 + difference 0 1) (sourceB777 + difference 1 0) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA777 + difference 0 1) (sourceB777 + difference 1 0) sourceC777) = raw11999 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw11999; decide +kernel
    rw [ha]
    exact (canonical11999 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA777 + difference 0 2) (sourceB777 + difference 2 0) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA777 + difference 0 2) (sourceB777 + difference 2 0) sourceC777) = raw12463 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12463; decide +kernel
    rw [ha]
    exact (canonical12463 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA777 + difference 0 3) (sourceB777 + difference 3 0) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA777 + difference 0 3) (sourceB777 + difference 3 0) sourceC777) = raw12881 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12881; decide +kernel
    rw [ha]
    exact (canonical12881 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA777 + difference 0 4) (sourceB777 + difference 4 0) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA777 + difference 0 4) (sourceB777 + difference 4 0) sourceC777) = raw12882 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12882; decide +kernel
    rw [ha]
    exact (canonical12882 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA777 + difference 0 5) (sourceB777 + difference 5 0) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA777 + difference 0 5) (sourceB777 + difference 5 0) sourceC777) = raw12883 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12883; decide +kernel
    rw [ha]
    exact (canonical12883 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA777 + difference 1 0) (sourceB777 + difference 0 1) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA777 + difference 1 0) (sourceB777 + difference 0 1) sourceC777) = raw12884 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12884; decide +kernel
    rw [ha]
    exact (canonical12884 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA777 + difference 1 2) (sourceB777 + difference 2 1) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA777 + difference 1 2) (sourceB777 + difference 2 1) sourceC777) = raw12467 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12467; decide +kernel
    rw [ha]
    exact (canonical12467 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA777 + difference 1 3) (sourceB777 + difference 3 1) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5143) := by
    have ha : (tripleCharges (sourceA777 + difference 1 3) (sourceB777 + difference 3 1) sourceC777) = raw12885 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12885; decide +kernel
    rw [ha]
    exact (canonical12885 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA777 + difference 1 4) (sourceB777 + difference 4 1) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5285) := by
    have ha : (tripleCharges (sourceA777 + difference 1 4) (sourceB777 + difference 4 1) sourceC777) = raw12886 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12886; decide +kernel
    rw [ha]
    exact (canonical12886 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA777 + difference 1 5) (sourceB777 + difference 5 1) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA777 + difference 1 5) (sourceB777 + difference 5 1) sourceC777) = raw12887 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12887; decide +kernel
    rw [ha]
    exact (canonical12887 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA777 + difference 2 0) (sourceB777 + difference 0 2) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA777 + difference 2 0) (sourceB777 + difference 0 2) sourceC777) = raw12888 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12888; decide +kernel
    rw [ha]
    exact (canonical12888 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA777 + difference 2 1) (sourceB777 + difference 1 2) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4806) := by
    have ha : (tripleCharges (sourceA777 + difference 2 1) (sourceB777 + difference 1 2) sourceC777) = raw12008 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12008; decide +kernel
    rw [ha]
    exact (canonical12008 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA777 + difference 2 3) (sourceB777 + difference 3 2) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4809) := by
    have ha : (tripleCharges (sourceA777 + difference 2 3) (sourceB777 + difference 3 2) sourceC777) = raw12889 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12889; decide +kernel
    rw [ha]
    exact (canonical12889 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA777 + difference 2 4) (sourceB777 + difference 4 2) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4842) := by
    have ha : (tripleCharges (sourceA777 + difference 2 4) (sourceB777 + difference 4 2) sourceC777) = raw12890 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12890; decide +kernel
    rw [ha]
    exact (canonical12890 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA777 + difference 2 5) (sourceB777 + difference 5 2) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA777 + difference 2 5) (sourceB777 + difference 5 2) sourceC777) = raw12891 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12891; decide +kernel
    rw [ha]
    exact (canonical12891 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA777 + difference 3 0) (sourceB777 + difference 0 3) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA777 + difference 3 0) (sourceB777 + difference 0 3) sourceC777) = raw12002 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12002; decide +kernel
    rw [ha]
    exact (canonical12002 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA777 + difference 3 1) (sourceB777 + difference 1 3) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA777 + difference 3 1) (sourceB777 + difference 1 3) sourceC777) = raw11674 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw11674; decide +kernel
    rw [ha]
    exact (canonical11674 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA777 + difference 3 2) (sourceB777 + difference 2 3) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA777 + difference 3 2) (sourceB777 + difference 2 3) sourceC777) = raw11669 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw11669; decide +kernel
    rw [ha]
    exact (canonical11669 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA777 + difference 3 4) (sourceB777 + difference 4 3) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA777 + difference 3 4) (sourceB777 + difference 4 3) sourceC777) = raw12004 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12004; decide +kernel
    rw [ha]
    exact (canonical12004 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA777 + difference 3 5) (sourceB777 + difference 5 3) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA777 + difference 3 5) (sourceB777 + difference 5 3) sourceC777) = raw12005 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12005; decide +kernel
    rw [ha]
    exact (canonical12005 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA777 + difference 4 0) (sourceB777 + difference 0 4) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA777 + difference 4 0) (sourceB777 + difference 0 4) sourceC777) = raw12892 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12892; decide +kernel
    rw [ha]
    exact (canonical12892 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA777 + difference 4 1) (sourceB777 + difference 1 4) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA777 + difference 4 1) (sourceB777 + difference 1 4) sourceC777) = raw12017 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12017; decide +kernel
    rw [ha]
    exact (canonical12017 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA777 + difference 4 2) (sourceB777 + difference 2 4) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA777 + difference 4 2) (sourceB777 + difference 2 4) sourceC777) = raw12473 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12473; decide +kernel
    rw [ha]
    exact (canonical12473 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA777 + difference 4 3) (sourceB777 + difference 3 4) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5279) := by
    have ha : (tripleCharges (sourceA777 + difference 4 3) (sourceB777 + difference 3 4) sourceC777) = raw12893 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12893; decide +kernel
    rw [ha]
    exact (canonical12893 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA777 + difference 4 5) (sourceB777 + difference 5 4) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA777 + difference 4 5) (sourceB777 + difference 5 4) sourceC777) = raw12894 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12894; decide +kernel
    rw [ha]
    exact (canonical12894 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA777 + difference 5 0) (sourceB777 + difference 0 5) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA777 + difference 5 0) (sourceB777 + difference 0 5) sourceC777) = raw12468 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12468; decide +kernel
    rw [ha]
    exact (canonical12468 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA777 + difference 5 1) (sourceB777 + difference 1 5) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5262) := by
    have ha : (tripleCharges (sourceA777 + difference 5 1) (sourceB777 + difference 1 5) sourceC777) = raw11672 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw11672; decide +kernel
    rw [ha]
    exact (canonical11672 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA777 + difference 5 2) (sourceB777 + difference 2 5) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA777 + difference 5 2) (sourceB777 + difference 2 5) sourceC777) = raw11667 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw11667; decide +kernel
    rw [ha]
    exact (canonical11667 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA777 + difference 5 3) (sourceB777 + difference 3 5) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5158) := by
    have ha : (tripleCharges (sourceA777 + difference 5 3) (sourceB777 + difference 3 5) sourceC777) = raw12469 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12469; decide +kernel
    rw [ha]
    exact (canonical12469 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA777 + difference 5 4) (sourceB777 + difference 4 5) sourceC777) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5298) := by
    have ha : (tripleCharges (sourceA777 + difference 5 4) (sourceB777 + difference 4 5) sourceC777) = raw12470 := by
      apply Matrix.ext; unfold tripleCharges sourceA777 sourceB777 sourceC777 difference raw12470; decide +kernel
    rw [ha]
    exact (canonical12470 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA777 sourceB777 sourceC777
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm777, Integer.Sparse.eval]
  linarith only [hs]

def sourceA778 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB778 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC778 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm778 : Integer.Sparse Master := [(Sum.inr 2118, 1), (Sum.inr 2119, 1), (Sum.inr 2123, 1), (Sum.inr 2132, 1), (Sum.inr 2220, 1), (Sum.inr 2250, 1), (Sum.inr 2274, 1), (Sum.inr 2275, 1), (Sum.inr 2277, 1), (Sum.inr 2565, 1), (Sum.inr 2575, 1), (Sum.inr 2585, 1), (Sum.inr 2727, 1), (Sum.inr 2728, 1), (Sum.inr 2730, 1), (Sum.inr 2748, 1), (Sum.inr 2750, 1), (Sum.inr 2756, 1), (Sum.inr 2757, 1), (Sum.inr 2763, 1), (Sum.inr 2764, 1), (Sum.inr 2766, 1), (Sum.inr 2772, 1), (Sum.inr 2773, 2), (Sum.inr 2775, 1), (Sum.inr 3091, 1), (Sum.inr 3109, 1), (Sum.inr 3115, 1), (Sum.inr 3116, 1)]

theorem sourceEq778 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm778 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA778 + difference 0 1) (sourceB778 + difference 1 0) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA778 + difference 0 1) (sourceB778 + difference 1 0) sourceC778) = raw12021 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12021; decide +kernel
    rw [ha]
    exact (canonical12021 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA778 + difference 0 2) (sourceB778 + difference 2 0) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA778 + difference 0 2) (sourceB778 + difference 2 0) sourceC778) = raw12480 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12480; decide +kernel
    rw [ha]
    exact (canonical12480 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA778 + difference 0 3) (sourceB778 + difference 3 0) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2575) := by
    have ha : (tripleCharges (sourceA778 + difference 0 3) (sourceB778 + difference 3 0) sourceC778) = raw12895 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12895; decide +kernel
    rw [ha]
    exact (canonical12895 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA778 + difference 0 4) (sourceB778 + difference 4 0) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3115) := by
    have ha : (tripleCharges (sourceA778 + difference 0 4) (sourceB778 + difference 4 0) sourceC778) = raw12896 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12896; decide +kernel
    rw [ha]
    exact (canonical12896 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA778 + difference 0 5) (sourceB778 + difference 5 0) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3116) := by
    have ha : (tripleCharges (sourceA778 + difference 0 5) (sourceB778 + difference 5 0) sourceC778) = raw12897 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12897; decide +kernel
    rw [ha]
    exact (canonical12897 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA778 + difference 1 0) (sourceB778 + difference 0 1) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA778 + difference 1 0) (sourceB778 + difference 0 1) sourceC778) = raw12898 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12898; decide +kernel
    rw [ha]
    exact (canonical12898 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA778 + difference 1 2) (sourceB778 + difference 2 1) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA778 + difference 1 2) (sourceB778 + difference 2 1) sourceC778) = raw12485 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12485; decide +kernel
    rw [ha]
    exact (canonical12485 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA778 + difference 1 3) (sourceB778 + difference 3 1) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2565) := by
    have ha : (tripleCharges (sourceA778 + difference 1 3) (sourceB778 + difference 3 1) sourceC778) = raw12899 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12899; decide +kernel
    rw [ha]
    exact (canonical12899 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA778 + difference 1 4) (sourceB778 + difference 4 1) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2756) := by
    have ha : (tripleCharges (sourceA778 + difference 1 4) (sourceB778 + difference 4 1) sourceC778) = raw12900 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12900; decide +kernel
    rw [ha]
    exact (canonical12900 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA778 + difference 1 5) (sourceB778 + difference 5 1) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2757) := by
    have ha : (tripleCharges (sourceA778 + difference 1 5) (sourceB778 + difference 5 1) sourceC778) = raw12901 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12901; decide +kernel
    rw [ha]
    exact (canonical12901 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA778 + difference 2 0) (sourceB778 + difference 0 2) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA778 + difference 2 0) (sourceB778 + difference 0 2) sourceC778) = raw12902 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12902; decide +kernel
    rw [ha]
    exact (canonical12902 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA778 + difference 2 1) (sourceB778 + difference 1 2) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2118) := by
    have ha : (tripleCharges (sourceA778 + difference 2 1) (sourceB778 + difference 1 2) sourceC778) = raw12030 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12030; decide +kernel
    rw [ha]
    exact (canonical12030 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA778 + difference 2 3) (sourceB778 + difference 3 2) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2119) := by
    have ha : (tripleCharges (sourceA778 + difference 2 3) (sourceB778 + difference 3 2) sourceC778) = raw12903 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12903; decide +kernel
    rw [ha]
    exact (canonical12903 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA778 + difference 2 4) (sourceB778 + difference 4 2) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2123) := by
    have ha : (tripleCharges (sourceA778 + difference 2 4) (sourceB778 + difference 4 2) sourceC778) = raw12904 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12904; decide +kernel
    rw [ha]
    exact (canonical12904 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA778 + difference 2 5) (sourceB778 + difference 5 2) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2132) := by
    have ha : (tripleCharges (sourceA778 + difference 2 5) (sourceB778 + difference 5 2) sourceC778) = raw12905 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12905; decide +kernel
    rw [ha]
    exact (canonical12905 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA778 + difference 3 0) (sourceB778 + difference 0 3) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA778 + difference 3 0) (sourceB778 + difference 0 3) sourceC778) = raw12024 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12024; decide +kernel
    rw [ha]
    exact (canonical12024 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA778 + difference 3 1) (sourceB778 + difference 1 3) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA778 + difference 3 1) (sourceB778 + difference 1 3) sourceC778) = raw11704 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw11704; decide +kernel
    rw [ha]
    exact (canonical11704 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA778 + difference 3 2) (sourceB778 + difference 2 3) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA778 + difference 3 2) (sourceB778 + difference 2 3) sourceC778) = raw11699 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw11699; decide +kernel
    rw [ha]
    exact (canonical11699 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA778 + difference 3 4) (sourceB778 + difference 4 3) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA778 + difference 3 4) (sourceB778 + difference 4 3) sourceC778) = raw12026 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12026; decide +kernel
    rw [ha]
    exact (canonical12026 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA778 + difference 3 5) (sourceB778 + difference 5 3) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2775) := by
    have ha : (tripleCharges (sourceA778 + difference 3 5) (sourceB778 + difference 5 3) sourceC778) = raw12027 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12027; decide +kernel
    rw [ha]
    exact (canonical12027 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA778 + difference 4 0) (sourceB778 + difference 0 4) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA778 + difference 4 0) (sourceB778 + difference 0 4) sourceC778) = raw12906 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12906; decide +kernel
    rw [ha]
    exact (canonical12906 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA778 + difference 4 1) (sourceB778 + difference 1 4) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA778 + difference 4 1) (sourceB778 + difference 1 4) sourceC778) = raw12039 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12039; decide +kernel
    rw [ha]
    exact (canonical12039 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA778 + difference 4 2) (sourceB778 + difference 2 4) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA778 + difference 4 2) (sourceB778 + difference 2 4) sourceC778) = raw12492 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12492; decide +kernel
    rw [ha]
    exact (canonical12492 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA778 + difference 4 3) (sourceB778 + difference 3 4) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2748) := by
    have ha : (tripleCharges (sourceA778 + difference 4 3) (sourceB778 + difference 3 4) sourceC778) = raw12907 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12907; decide +kernel
    rw [ha]
    exact (canonical12907 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA778 + difference 4 5) (sourceB778 + difference 5 4) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA778 + difference 4 5) (sourceB778 + difference 5 4) sourceC778) = raw12908 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12908; decide +kernel
    rw [ha]
    exact (canonical12908 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA778 + difference 5 0) (sourceB778 + difference 0 5) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA778 + difference 5 0) (sourceB778 + difference 0 5) sourceC778) = raw12486 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12486; decide +kernel
    rw [ha]
    exact (canonical12486 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA778 + difference 5 1) (sourceB778 + difference 1 5) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2727) := by
    have ha : (tripleCharges (sourceA778 + difference 5 1) (sourceB778 + difference 1 5) sourceC778) = raw11702 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw11702; decide +kernel
    rw [ha]
    exact (canonical11702 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA778 + difference 5 2) (sourceB778 + difference 2 5) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA778 + difference 5 2) (sourceB778 + difference 2 5) sourceC778) = raw11697 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw11697; decide +kernel
    rw [ha]
    exact (canonical11697 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA778 + difference 5 3) (sourceB778 + difference 3 5) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2585) := by
    have ha : (tripleCharges (sourceA778 + difference 5 3) (sourceB778 + difference 3 5) sourceC778) = raw12487 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12487; decide +kernel
    rw [ha]
    exact (canonical12487 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA778 + difference 5 4) (sourceB778 + difference 4 5) sourceC778) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2772) := by
    have ha : (tripleCharges (sourceA778 + difference 5 4) (sourceB778 + difference 4 5) sourceC778) = raw12488 := by
      apply Matrix.ext; unfold tripleCharges sourceA778 sourceB778 sourceC778 difference raw12488; decide +kernel
    rw [ha]
    exact (canonical12488 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA778 sourceB778 sourceC778
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm778, Integer.Sparse.eval]
  linarith only [hs]

def sourceA779 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB779 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC779 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm779 : Integer.Sparse Master := [(Sum.inr 2024, 1), (Sum.inr 2026, 1), (Sum.inr 2027, 1), (Sum.inr 2061, 1), (Sum.inr 2246, 1), (Sum.inr 2669, 1), (Sum.inr 2681, 1), (Sum.inr 2682, 1), (Sum.inr 2684, 1), (Sum.inr 2739, 1), (Sum.inr 3020, 1), (Sum.inr 3021, 1), (Sum.inr 3023, 1), (Sum.inr 3034, 1), (Sum.inr 3036, 1), (Sum.inr 3037, 1), (Sum.inr 3047, 1), (Sum.inr 3048, 1), (Sum.inr 3050, 1), (Sum.inr 3051, 2), (Sum.inr 3053, 1), (Sum.inr 3074, 1), (Sum.inr 3097, 1), (Sum.inr 3099, 1), (Sum.inr 3100, 1), (Sum.inr 3170, 1), (Sum.inr 3174, 1), (Sum.inr 3183, 1), (Sum.inr 3223, 1)]

theorem sourceEq779 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm779 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA779 + difference 0 1) (sourceB779 + difference 1 0) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA779 + difference 0 1) (sourceB779 + difference 1 0) sourceC779) = raw12043 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12043; decide +kernel
    rw [ha]
    exact (canonical12043 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA779 + difference 0 2) (sourceB779 + difference 2 0) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA779 + difference 0 2) (sourceB779 + difference 2 0) sourceC779) = raw12499 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12499; decide +kernel
    rw [ha]
    exact (canonical12499 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA779 + difference 0 3) (sourceB779 + difference 3 0) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA779 + difference 0 3) (sourceB779 + difference 3 0) sourceC779) = raw12909 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12909; decide +kernel
    rw [ha]
    exact (canonical12909 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA779 + difference 0 4) (sourceB779 + difference 4 0) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2682) := by
    have ha : (tripleCharges (sourceA779 + difference 0 4) (sourceB779 + difference 4 0) sourceC779) = raw12910 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12910; decide +kernel
    rw [ha]
    exact (canonical12910 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA779 + difference 0 5) (sourceB779 + difference 5 0) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA779 + difference 0 5) (sourceB779 + difference 5 0) sourceC779) = raw12911 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12911; decide +kernel
    rw [ha]
    exact (canonical12911 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA779 + difference 1 0) (sourceB779 + difference 0 1) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA779 + difference 1 0) (sourceB779 + difference 0 1) sourceC779) = raw12912 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12912; decide +kernel
    rw [ha]
    exact (canonical12912 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA779 + difference 1 2) (sourceB779 + difference 2 1) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA779 + difference 1 2) (sourceB779 + difference 2 1) sourceC779) = raw12503 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12503; decide +kernel
    rw [ha]
    exact (canonical12503 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA779 + difference 1 3) (sourceB779 + difference 3 1) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3020) := by
    have ha : (tripleCharges (sourceA779 + difference 1 3) (sourceB779 + difference 3 1) sourceC779) = raw12913 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12913; decide +kernel
    rw [ha]
    exact (canonical12913 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA779 + difference 1 4) (sourceB779 + difference 4 1) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3021) := by
    have ha : (tripleCharges (sourceA779 + difference 1 4) (sourceB779 + difference 4 1) sourceC779) = raw12914 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12914; decide +kernel
    rw [ha]
    exact (canonical12914 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA779 + difference 1 5) (sourceB779 + difference 5 1) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA779 + difference 1 5) (sourceB779 + difference 5 1) sourceC779) = raw12915 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12915; decide +kernel
    rw [ha]
    exact (canonical12915 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA779 + difference 2 0) (sourceB779 + difference 0 2) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA779 + difference 2 0) (sourceB779 + difference 0 2) sourceC779) = raw12916 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12916; decide +kernel
    rw [ha]
    exact (canonical12916 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA779 + difference 2 1) (sourceB779 + difference 1 2) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2024) := by
    have ha : (tripleCharges (sourceA779 + difference 2 1) (sourceB779 + difference 1 2) sourceC779) = raw12052 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12052; decide +kernel
    rw [ha]
    exact (canonical12052 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA779 + difference 2 3) (sourceB779 + difference 3 2) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2027) := by
    have ha : (tripleCharges (sourceA779 + difference 2 3) (sourceB779 + difference 3 2) sourceC779) = raw12917 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12917; decide +kernel
    rw [ha]
    exact (canonical12917 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA779 + difference 2 4) (sourceB779 + difference 4 2) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2061) := by
    have ha : (tripleCharges (sourceA779 + difference 2 4) (sourceB779 + difference 4 2) sourceC779) = raw12918 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12918; decide +kernel
    rw [ha]
    exact (canonical12918 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA779 + difference 2 5) (sourceB779 + difference 5 2) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA779 + difference 2 5) (sourceB779 + difference 5 2) sourceC779) = raw12919 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12919; decide +kernel
    rw [ha]
    exact (canonical12919 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA779 + difference 3 0) (sourceB779 + difference 0 3) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA779 + difference 3 0) (sourceB779 + difference 0 3) sourceC779) = raw12046 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12046; decide +kernel
    rw [ha]
    exact (canonical12046 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA779 + difference 3 1) (sourceB779 + difference 1 3) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA779 + difference 3 1) (sourceB779 + difference 1 3) sourceC779) = raw11734 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw11734; decide +kernel
    rw [ha]
    exact (canonical11734 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA779 + difference 3 2) (sourceB779 + difference 2 3) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA779 + difference 3 2) (sourceB779 + difference 2 3) sourceC779) = raw11729 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw11729; decide +kernel
    rw [ha]
    exact (canonical11729 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA779 + difference 3 4) (sourceB779 + difference 4 3) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA779 + difference 3 4) (sourceB779 + difference 4 3) sourceC779) = raw12048 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12048; decide +kernel
    rw [ha]
    exact (canonical12048 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA779 + difference 3 5) (sourceB779 + difference 5 3) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA779 + difference 3 5) (sourceB779 + difference 5 3) sourceC779) = raw12049 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12049; decide +kernel
    rw [ha]
    exact (canonical12049 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA779 + difference 4 0) (sourceB779 + difference 0 4) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3183) := by
    have ha : (tripleCharges (sourceA779 + difference 4 0) (sourceB779 + difference 0 4) sourceC779) = raw12920 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12920; decide +kernel
    rw [ha]
    exact (canonical12920 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA779 + difference 4 1) (sourceB779 + difference 1 4) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3036) := by
    have ha : (tripleCharges (sourceA779 + difference 4 1) (sourceB779 + difference 1 4) sourceC779) = raw12061 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12061; decide +kernel
    rw [ha]
    exact (canonical12061 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA779 + difference 4 2) (sourceB779 + difference 2 4) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA779 + difference 4 2) (sourceB779 + difference 2 4) sourceC779) = raw12509 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12509; decide +kernel
    rw [ha]
    exact (canonical12509 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA779 + difference 4 3) (sourceB779 + difference 3 4) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3050) := by
    have ha : (tripleCharges (sourceA779 + difference 4 3) (sourceB779 + difference 3 4) sourceC779) = raw12921 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12921; decide +kernel
    rw [ha]
    exact (canonical12921 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA779 + difference 4 5) (sourceB779 + difference 5 4) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA779 + difference 4 5) (sourceB779 + difference 5 4) sourceC779) = raw12922 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12922; decide +kernel
    rw [ha]
    exact (canonical12922 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA779 + difference 5 0) (sourceB779 + difference 0 5) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA779 + difference 5 0) (sourceB779 + difference 0 5) sourceC779) = raw12504 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12504; decide +kernel
    rw [ha]
    exact (canonical12504 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA779 + difference 5 1) (sourceB779 + difference 1 5) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3034) := by
    have ha : (tripleCharges (sourceA779 + difference 5 1) (sourceB779 + difference 1 5) sourceC779) = raw11732 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw11732; decide +kernel
    rw [ha]
    exact (canonical11732 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA779 + difference 5 2) (sourceB779 + difference 2 5) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA779 + difference 5 2) (sourceB779 + difference 2 5) sourceC779) = raw11727 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw11727; decide +kernel
    rw [ha]
    exact (canonical11727 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA779 + difference 5 3) (sourceB779 + difference 3 5) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3047) := by
    have ha : (tripleCharges (sourceA779 + difference 5 3) (sourceB779 + difference 3 5) sourceC779) = raw12505 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12505; decide +kernel
    rw [ha]
    exact (canonical12505 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA779 + difference 5 4) (sourceB779 + difference 4 5) sourceC779) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3048) := by
    have ha : (tripleCharges (sourceA779 + difference 5 4) (sourceB779 + difference 4 5) sourceC779) = raw12506 := by
      apply Matrix.ext; unfold tripleCharges sourceA779 sourceB779 sourceC779 difference raw12506; decide +kernel
    rw [ha]
    exact (canonical12506 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA779 sourceB779 sourceC779
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm779, Integer.Sparse.eval]
  linarith only [hs]

def sourceA780 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB780 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC780 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm780 : Integer.Sparse Master := [(Sum.inr 2930, 1), (Sum.inr 3376, 1), (Sum.inr 3380, 1), (Sum.inr 3394, 1), (Sum.inr 3534, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

theorem sourceEq780 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm780 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA780 + difference 0 0) (sourceB780 + difference 0 0) sourceC780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA780 + difference 0 0) (sourceB780 + difference 0 0) sourceC780) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA780 sourceB780 sourceC780 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA780 + difference 0 1) (sourceB780 + difference 1 0) sourceC780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA780 + difference 0 1) (sourceB780 + difference 1 0) sourceC780) = raw12065 := by
      apply Matrix.ext; unfold tripleCharges sourceA780 sourceB780 sourceC780 difference raw12065; decide +kernel
    rw [ha]
    exact (canonical12065 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA780 + difference 0 2) (sourceB780 + difference 2 0) sourceC780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA780 + difference 0 2) (sourceB780 + difference 2 0) sourceC780) = raw12515 := by
      apply Matrix.ext; unfold tripleCharges sourceA780 sourceB780 sourceC780 difference raw12515; decide +kernel
    rw [ha]
    exact (canonical12515 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA780 + difference 0 3) (sourceB780 + difference 3 0) sourceC780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA780 + difference 0 3) (sourceB780 + difference 3 0) sourceC780) = raw12923 := by
      apply Matrix.ext; unfold tripleCharges sourceA780 sourceB780 sourceC780 difference raw12923; decide +kernel
    rw [ha]
    exact (canonical12923 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA780 + difference 0 4) (sourceB780 + difference 4 0) sourceC780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3380) := by
    have ha : (tripleCharges (sourceA780 + difference 0 4) (sourceB780 + difference 4 0) sourceC780) = raw12924 := by
      apply Matrix.ext; unfold tripleCharges sourceA780 sourceB780 sourceC780 difference raw12924; decide +kernel
    rw [ha]
    exact (canonical12924 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA780 + difference 0 5) (sourceB780 + difference 5 0) sourceC780) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3394) := by
    have ha : (tripleCharges (sourceA780 + difference 0 5) (sourceB780 + difference 5 0) sourceC780) = raw12925 := by
      apply Matrix.ext; unfold tripleCharges sourceA780 sourceB780 sourceC780 difference raw12925; decide +kernel
    rw [ha]
    exact (canonical12925 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA780 + sourceB780) sourceC780) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA780 + sourceB780) sourceC780) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA780 sourceB780 sourceC780 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA780 sourceB780 sourceC780
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm780, Integer.Sparse.eval]
  linarith only [hs]

def sourceA781 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB781 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC781 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm781 : Integer.Sparse Master := [(Sum.inr 2089, 1), (Sum.inr 2926, 1), (Sum.inr 3551, 1), (Sum.inr 3567, 1), (Sum.inr 3571, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

theorem sourceEq781 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm781 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA781 + difference 1 0) (sourceB781 + difference 0 1) sourceC781) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA781 + difference 1 0) (sourceB781 + difference 0 1) sourceC781) = raw12926 := by
      apply Matrix.ext; unfold tripleCharges sourceA781 sourceB781 sourceC781 difference raw12926; decide +kernel
    rw [ha]
    exact (canonical12926 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA781 + difference 1 1) (sourceB781 + difference 1 1) sourceC781) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA781 + difference 1 1) (sourceB781 + difference 1 1) sourceC781) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA781 sourceB781 sourceC781 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA781 + difference 1 2) (sourceB781 + difference 2 1) sourceC781) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA781 + difference 1 2) (sourceB781 + difference 2 1) sourceC781) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA781 sourceB781 sourceC781 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA781 + difference 1 3) (sourceB781 + difference 3 1) sourceC781) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2926) := by
    have ha : (tripleCharges (sourceA781 + difference 1 3) (sourceB781 + difference 3 1) sourceC781) = raw12927 := by
      apply Matrix.ext; unfold tripleCharges sourceA781 sourceB781 sourceC781 difference raw12927; decide +kernel
    rw [ha]
    exact (canonical12927 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA781 + difference 1 4) (sourceB781 + difference 4 1) sourceC781) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3551) := by
    have ha : (tripleCharges (sourceA781 + difference 1 4) (sourceB781 + difference 4 1) sourceC781) = raw12928 := by
      apply Matrix.ext; unfold tripleCharges sourceA781 sourceB781 sourceC781 difference raw12928; decide +kernel
    rw [ha]
    exact (canonical12928 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA781 + difference 1 5) (sourceB781 + difference 5 1) sourceC781) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA781 + difference 1 5) (sourceB781 + difference 5 1) sourceC781) = raw12929 := by
      apply Matrix.ext; unfold tripleCharges sourceA781 sourceB781 sourceC781 difference raw12929; decide +kernel
    rw [ha]
    exact (canonical12929 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA781 + sourceB781) sourceC781) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA781 + sourceB781) sourceC781) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA781 sourceB781 sourceC781 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA781 sourceB781 sourceC781
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm781, Integer.Sparse.eval]
  linarith only [hs]

def sourceA782 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB782 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC782 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm782 : Integer.Sparse Master := [(Sum.inr 2092, 1), (Sum.inr 2929, 1), (Sum.inr 3149, 1), (Sum.inr 3152, 1), (Sum.inr 3158, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

theorem sourceEq782 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm782 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA782 + difference 2 0) (sourceB782 + difference 0 2) sourceC782) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA782 + difference 2 0) (sourceB782 + difference 0 2) sourceC782) = raw12930 := by
      apply Matrix.ext; unfold tripleCharges sourceA782 sourceB782 sourceC782 difference raw12930; decide +kernel
    rw [ha]
    exact (canonical12930 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA782 + difference 2 1) (sourceB782 + difference 1 2) sourceC782) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3149) := by
    have ha : (tripleCharges (sourceA782 + difference 2 1) (sourceB782 + difference 1 2) sourceC782) = raw12072 := by
      apply Matrix.ext; unfold tripleCharges sourceA782 sourceB782 sourceC782 difference raw12072; decide +kernel
    rw [ha]
    exact (canonical12072 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA782 + difference 2 2) (sourceB782 + difference 2 2) sourceC782) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA782 + difference 2 2) (sourceB782 + difference 2 2) sourceC782) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA782 sourceB782 sourceC782 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA782 + difference 2 3) (sourceB782 + difference 3 2) sourceC782) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2929) := by
    have ha : (tripleCharges (sourceA782 + difference 2 3) (sourceB782 + difference 3 2) sourceC782) = raw12931 := by
      apply Matrix.ext; unfold tripleCharges sourceA782 sourceB782 sourceC782 difference raw12931; decide +kernel
    rw [ha]
    exact (canonical12931 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA782 + difference 2 4) (sourceB782 + difference 4 2) sourceC782) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3152) := by
    have ha : (tripleCharges (sourceA782 + difference 2 4) (sourceB782 + difference 4 2) sourceC782) = raw12932 := by
      apply Matrix.ext; unfold tripleCharges sourceA782 sourceB782 sourceC782 difference raw12932; decide +kernel
    rw [ha]
    exact (canonical12932 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA782 + difference 2 5) (sourceB782 + difference 5 2) sourceC782) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA782 + difference 2 5) (sourceB782 + difference 5 2) sourceC782) = raw12933 := by
      apply Matrix.ext; unfold tripleCharges sourceA782 sourceB782 sourceC782 difference raw12933; decide +kernel
    rw [ha]
    exact (canonical12933 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA782 + sourceB782) sourceC782) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA782 + sourceB782) sourceC782) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA782 sourceB782 sourceC782 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA782 sourceB782 sourceC782
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm782, Integer.Sparse.eval]
  linarith only [hs]

def sourceA783 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB783 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC783 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm783 : Integer.Sparse Master := [(Sum.inr 2926, 1), (Sum.inr 2929, 1), (Sum.inr 2930, 1), (Sum.inr 2956, 1), (Sum.inr 3079, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

theorem sourceEq783 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm783 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA783 + difference 0 3) (sourceB783 + difference 3 0) sourceC783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA783 + difference 0 3) (sourceB783 + difference 3 0) sourceC783) = raw12923 := by
      apply Matrix.ext; unfold tripleCharges sourceA783 sourceB783 sourceC783 difference raw12923; decide +kernel
    rw [ha]
    exact (canonical12923 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA783 + difference 1 3) (sourceB783 + difference 3 1) sourceC783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2926) := by
    have ha : (tripleCharges (sourceA783 + difference 1 3) (sourceB783 + difference 3 1) sourceC783) = raw12927 := by
      apply Matrix.ext; unfold tripleCharges sourceA783 sourceB783 sourceC783 difference raw12927; decide +kernel
    rw [ha]
    exact (canonical12927 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA783 + difference 2 3) (sourceB783 + difference 3 2) sourceC783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2929) := by
    have ha : (tripleCharges (sourceA783 + difference 2 3) (sourceB783 + difference 3 2) sourceC783) = raw12931 := by
      apply Matrix.ext; unfold tripleCharges sourceA783 sourceB783 sourceC783 difference raw12931; decide +kernel
    rw [ha]
    exact (canonical12931 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA783 + difference 3 3) (sourceB783 + difference 3 3) sourceC783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA783 + difference 3 3) (sourceB783 + difference 3 3) sourceC783) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA783 sourceB783 sourceC783 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA783 + difference 4 3) (sourceB783 + difference 3 4) sourceC783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3079) := by
    have ha : (tripleCharges (sourceA783 + difference 4 3) (sourceB783 + difference 3 4) sourceC783) = raw12934 := by
      apply Matrix.ext; unfold tripleCharges sourceA783 sourceB783 sourceC783 difference raw12934; decide +kernel
    rw [ha]
    exact (canonical12934 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA783 + difference 5 3) (sourceB783 + difference 3 5) sourceC783) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2956) := by
    have ha : (tripleCharges (sourceA783 + difference 5 3) (sourceB783 + difference 3 5) sourceC783) = raw12522 := by
      apply Matrix.ext; unfold tripleCharges sourceA783 sourceB783 sourceC783 difference raw12522; decide +kernel
    rw [ha]
    exact (canonical12522 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA783 + sourceB783) sourceC783) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA783 + sourceB783) sourceC783) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA783 sourceB783 sourceC783 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA783 sourceB783 sourceC783
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm783, Integer.Sparse.eval]
  linarith only [hs]

def sourceA784 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB784 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC784 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm784 : Integer.Sparse Master := [(Sum.inr 2110, 1), (Sum.inr 3079, 1), (Sum.inr 3505, 1), (Sum.inr 3573, 2), (Sum.inr 3581, 1), (Sum.inr 4083, -1)]

theorem sourceEq784 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm784 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA784 + difference 4 0) (sourceB784 + difference 0 4) sourceC784) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA784 + difference 4 0) (sourceB784 + difference 0 4) sourceC784) = raw12935 := by
      apply Matrix.ext; unfold tripleCharges sourceA784 sourceB784 sourceC784 difference raw12935; decide +kernel
    rw [ha]
    exact (canonical12935 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA784 + difference 4 1) (sourceB784 + difference 1 4) sourceC784) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3505) := by
    have ha : (tripleCharges (sourceA784 + difference 4 1) (sourceB784 + difference 1 4) sourceC784) = raw12079 := by
      apply Matrix.ext; unfold tripleCharges sourceA784 sourceB784 sourceC784 difference raw12079; decide +kernel
    rw [ha]
    exact (canonical12079 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA784 + difference 4 2) (sourceB784 + difference 2 4) sourceC784) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA784 + difference 4 2) (sourceB784 + difference 2 4) sourceC784) = raw12528 := by
      apply Matrix.ext; unfold tripleCharges sourceA784 sourceB784 sourceC784 difference raw12528; decide +kernel
    rw [ha]
    exact (canonical12528 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA784 + difference 4 3) (sourceB784 + difference 3 4) sourceC784) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3079) := by
    have ha : (tripleCharges (sourceA784 + difference 4 3) (sourceB784 + difference 3 4) sourceC784) = raw12934 := by
      apply Matrix.ext; unfold tripleCharges sourceA784 sourceB784 sourceC784 difference raw12934; decide +kernel
    rw [ha]
    exact (canonical12934 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA784 + difference 4 4) (sourceB784 + difference 4 4) sourceC784) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA784 + difference 4 4) (sourceB784 + difference 4 4) sourceC784) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA784 sourceB784 sourceC784 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA784 + difference 4 5) (sourceB784 + difference 5 4) sourceC784) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA784 + difference 4 5) (sourceB784 + difference 5 4) sourceC784) = raw12936 := by
      apply Matrix.ext; unfold tripleCharges sourceA784 sourceB784 sourceC784 difference raw12936; decide +kernel
    rw [ha]
    exact (canonical12936 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA784 + sourceB784) sourceC784) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA784 + sourceB784) sourceC784) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA784 sourceB784 sourceC784 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA784 sourceB784 sourceC784
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm784, Integer.Sparse.eval]
  linarith only [hs]

def sourceA785 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB785 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC785 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm785 : Integer.Sparse Master := [(Sum.inr 3152, 1), (Sum.inr 3380, 1), (Sum.inr 3551, 1), (Sum.inr 3552, 1), (Sum.inr 3573, 2), (Sum.inr 4083, -1)]

theorem sourceEq785 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm785 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA785 + difference 0 4) (sourceB785 + difference 4 0) sourceC785) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3380) := by
    have ha : (tripleCharges (sourceA785 + difference 0 4) (sourceB785 + difference 4 0) sourceC785) = raw12924 := by
      apply Matrix.ext; unfold tripleCharges sourceA785 sourceB785 sourceC785 difference raw12924; decide +kernel
    rw [ha]
    exact (canonical12924 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA785 + difference 1 4) (sourceB785 + difference 4 1) sourceC785) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3551) := by
    have ha : (tripleCharges (sourceA785 + difference 1 4) (sourceB785 + difference 4 1) sourceC785) = raw12928 := by
      apply Matrix.ext; unfold tripleCharges sourceA785 sourceB785 sourceC785 difference raw12928; decide +kernel
    rw [ha]
    exact (canonical12928 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA785 + difference 2 4) (sourceB785 + difference 4 2) sourceC785) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3152) := by
    have ha : (tripleCharges (sourceA785 + difference 2 4) (sourceB785 + difference 4 2) sourceC785) = raw12932 := by
      apply Matrix.ext; unfold tripleCharges sourceA785 sourceB785 sourceC785 difference raw12932; decide +kernel
    rw [ha]
    exact (canonical12932 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA785 + difference 3 4) (sourceB785 + difference 4 3) sourceC785) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA785 + difference 3 4) (sourceB785 + difference 4 3) sourceC785) = raw12937 := by
      apply Matrix.ext; unfold tripleCharges sourceA785 sourceB785 sourceC785 difference raw12937; decide +kernel
    rw [ha]
    exact (canonical12937 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA785 + difference 4 4) (sourceB785 + difference 4 4) sourceC785) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA785 + difference 4 4) (sourceB785 + difference 4 4) sourceC785) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA785 sourceB785 sourceC785 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA785 + difference 5 4) (sourceB785 + difference 4 5) sourceC785) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3552) := by
    have ha : (tripleCharges (sourceA785 + difference 5 4) (sourceB785 + difference 4 5) sourceC785) = raw12523 := by
      apply Matrix.ext; unfold tripleCharges sourceA785 sourceB785 sourceC785 difference raw12523; decide +kernel
    rw [ha]
    exact (canonical12523 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA785 + sourceB785) sourceC785) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA785 + sourceB785) sourceC785) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA785 sourceB785 sourceC785 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA785 sourceB785 sourceC785
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm785, Integer.Sparse.eval]
  linarith only [hs]

def sourceA786 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB786 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceC786 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceForm786 : Integer.Sparse Master := [(Sum.inr 4569, 1), (Sum.inr 4570, 3), (Sum.inr 4618, 1), (Sum.inr 5155, 3), (Sum.inr 5166, 1), (Sum.inr 5212, 1), (Sum.inr 5213, 3), (Sum.inr 5301, 4), (Sum.inr 5302, 6), (Sum.inr 5306, 3), (Sum.inr 5437, 1), (Sum.inr 5453, 3)]

theorem sourceEq786 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm786 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA786 + difference 0 1) (sourceB786 + difference 1 0) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA786 + difference 0 1) (sourceB786 + difference 1 0) sourceC786) = raw12938 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12938; decide +kernel
    rw [ha]
    exact (canonical12938 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA786 + difference 0 2) (sourceB786 + difference 2 0) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA786 + difference 0 2) (sourceB786 + difference 2 0) sourceC786) = raw12939 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12939; decide +kernel
    rw [ha]
    exact (canonical12939 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA786 + difference 0 3) (sourceB786 + difference 3 0) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA786 + difference 0 3) (sourceB786 + difference 3 0) sourceC786) = raw12940 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12940; decide +kernel
    rw [ha]
    exact (canonical12940 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA786 + difference 0 4) (sourceB786 + difference 4 0) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA786 + difference 0 4) (sourceB786 + difference 4 0) sourceC786) = raw12941 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12941; decide +kernel
    rw [ha]
    exact (canonical12941 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA786 + difference 0 5) (sourceB786 + difference 5 0) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA786 + difference 0 5) (sourceB786 + difference 5 0) sourceC786) = raw12942 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12942; decide +kernel
    rw [ha]
    exact (canonical12942 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA786 + difference 1 0) (sourceB786 + difference 0 1) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4569) := by
    have ha : (tripleCharges (sourceA786 + difference 1 0) (sourceB786 + difference 0 1) sourceC786) = raw12943 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12943; decide +kernel
    rw [ha]
    exact (canonical12943 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA786 + difference 1 2) (sourceB786 + difference 2 1) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5212) := by
    have ha : (tripleCharges (sourceA786 + difference 1 2) (sourceB786 + difference 2 1) sourceC786) = raw12944 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12944; decide +kernel
    rw [ha]
    exact (canonical12944 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA786 + difference 1 3) (sourceB786 + difference 3 1) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA786 + difference 1 3) (sourceB786 + difference 3 1) sourceC786) = raw12945 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12945; decide +kernel
    rw [ha]
    exact (canonical12945 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA786 + difference 1 4) (sourceB786 + difference 4 1) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA786 + difference 1 4) (sourceB786 + difference 4 1) sourceC786) = raw12946 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12946; decide +kernel
    rw [ha]
    exact (canonical12946 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA786 + difference 1 5) (sourceB786 + difference 5 1) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA786 + difference 1 5) (sourceB786 + difference 5 1) sourceC786) = raw12947 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12947; decide +kernel
    rw [ha]
    exact (canonical12947 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA786 + difference 2 0) (sourceB786 + difference 0 2) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA786 + difference 2 0) (sourceB786 + difference 0 2) sourceC786) = raw12948 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12948; decide +kernel
    rw [ha]
    exact (canonical12948 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA786 + difference 2 1) (sourceB786 + difference 1 2) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5166) := by
    have ha : (tripleCharges (sourceA786 + difference 2 1) (sourceB786 + difference 1 2) sourceC786) = raw12949 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12949; decide +kernel
    rw [ha]
    exact (canonical12949 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA786 + difference 2 3) (sourceB786 + difference 3 2) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA786 + difference 2 3) (sourceB786 + difference 3 2) sourceC786) = raw12950 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12950; decide +kernel
    rw [ha]
    exact (canonical12950 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA786 + difference 2 4) (sourceB786 + difference 4 2) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA786 + difference 2 4) (sourceB786 + difference 4 2) sourceC786) = raw12951 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12951; decide +kernel
    rw [ha]
    exact (canonical12951 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA786 + difference 2 5) (sourceB786 + difference 5 2) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA786 + difference 2 5) (sourceB786 + difference 5 2) sourceC786) = raw12952 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12952; decide +kernel
    rw [ha]
    exact (canonical12952 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA786 + difference 3 0) (sourceB786 + difference 0 3) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4570) := by
    have ha : (tripleCharges (sourceA786 + difference 3 0) (sourceB786 + difference 0 3) sourceC786) = raw12953 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12953; decide +kernel
    rw [ha]
    exact (canonical12953 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA786 + difference 3 1) (sourceB786 + difference 1 3) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA786 + difference 3 1) (sourceB786 + difference 1 3) sourceC786) = raw12954 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12954; decide +kernel
    rw [ha]
    exact (canonical12954 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA786 + difference 3 2) (sourceB786 + difference 2 3) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5213) := by
    have ha : (tripleCharges (sourceA786 + difference 3 2) (sourceB786 + difference 2 3) sourceC786) = raw12955 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12955; decide +kernel
    rw [ha]
    exact (canonical12955 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA786 + difference 3 4) (sourceB786 + difference 4 3) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA786 + difference 3 4) (sourceB786 + difference 4 3) sourceC786) = raw12956 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12956; decide +kernel
    rw [ha]
    exact (canonical12956 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA786 + difference 3 5) (sourceB786 + difference 5 3) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA786 + difference 3 5) (sourceB786 + difference 5 3) sourceC786) = raw12957 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12957; decide +kernel
    rw [ha]
    exact (canonical12957 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA786 + difference 4 0) (sourceB786 + difference 0 4) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4570) := by
    have ha : (tripleCharges (sourceA786 + difference 4 0) (sourceB786 + difference 0 4) sourceC786) = raw12958 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12958; decide +kernel
    rw [ha]
    exact (canonical12958 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA786 + difference 4 1) (sourceB786 + difference 1 4) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA786 + difference 4 1) (sourceB786 + difference 1 4) sourceC786) = raw12959 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12959; decide +kernel
    rw [ha]
    exact (canonical12959 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA786 + difference 4 2) (sourceB786 + difference 2 4) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5213) := by
    have ha : (tripleCharges (sourceA786 + difference 4 2) (sourceB786 + difference 2 4) sourceC786) = raw12960 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12960; decide +kernel
    rw [ha]
    exact (canonical12960 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA786 + difference 4 3) (sourceB786 + difference 3 4) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA786 + difference 4 3) (sourceB786 + difference 3 4) sourceC786) = raw12961 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12961; decide +kernel
    rw [ha]
    exact (canonical12961 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA786 + difference 4 5) (sourceB786 + difference 5 4) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA786 + difference 4 5) (sourceB786 + difference 5 4) sourceC786) = raw12962 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12962; decide +kernel
    rw [ha]
    exact (canonical12962 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA786 + difference 5 0) (sourceB786 + difference 0 5) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4570) := by
    have ha : (tripleCharges (sourceA786 + difference 5 0) (sourceB786 + difference 0 5) sourceC786) = raw12963 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12963; decide +kernel
    rw [ha]
    exact (canonical12963 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA786 + difference 5 1) (sourceB786 + difference 1 5) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA786 + difference 5 1) (sourceB786 + difference 1 5) sourceC786) = raw12964 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12964; decide +kernel
    rw [ha]
    exact (canonical12964 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA786 + difference 5 2) (sourceB786 + difference 2 5) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5213) := by
    have ha : (tripleCharges (sourceA786 + difference 5 2) (sourceB786 + difference 2 5) sourceC786) = raw12965 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12965; decide +kernel
    rw [ha]
    exact (canonical12965 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA786 + difference 5 3) (sourceB786 + difference 3 5) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA786 + difference 5 3) (sourceB786 + difference 3 5) sourceC786) = raw12966 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12966; decide +kernel
    rw [ha]
    exact (canonical12966 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA786 + difference 5 4) (sourceB786 + difference 4 5) sourceC786) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA786 + difference 5 4) (sourceB786 + difference 4 5) sourceC786) = raw12967 := by
      apply Matrix.ext; unfold tripleCharges sourceA786 sourceB786 sourceC786 difference raw12967; decide +kernel
    rw [ha]
    exact (canonical12967 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA786 sourceB786 sourceC786
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm786, Integer.Sparse.eval]
  linarith only [hs]

def sourceA787 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB787 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceC787 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceForm787 : Integer.Sparse Master := [(Sum.inr 1187, 1), (Sum.inr 1188, 3), (Sum.inr 1293, 1), (Sum.inr 2839, 1), (Sum.inr 2840, 3), (Sum.inr 2908, 3), (Sum.inr 2953, 1), (Sum.inr 3053, 3), (Sum.inr 3054, 6), (Sum.inr 3120, 3), (Sum.inr 3619, 1), (Sum.inr 3899, 1), (Sum.inr 3912, 3)]

theorem sourceEq787 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm787 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA787 + difference 0 1) (sourceB787 + difference 1 0) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA787 + difference 0 1) (sourceB787 + difference 1 0) sourceC787) = raw12968 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12968; decide +kernel
    rw [ha]
    exact (canonical12968 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA787 + difference 0 2) (sourceB787 + difference 2 0) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3619) := by
    have ha : (tripleCharges (sourceA787 + difference 0 2) (sourceB787 + difference 2 0) sourceC787) = raw12969 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12969; decide +kernel
    rw [ha]
    exact (canonical12969 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA787 + difference 0 3) (sourceB787 + difference 3 0) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3912) := by
    have ha : (tripleCharges (sourceA787 + difference 0 3) (sourceB787 + difference 3 0) sourceC787) = raw12970 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12970; decide +kernel
    rw [ha]
    exact (canonical12970 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA787 + difference 0 4) (sourceB787 + difference 4 0) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3912) := by
    have ha : (tripleCharges (sourceA787 + difference 0 4) (sourceB787 + difference 4 0) sourceC787) = raw12971 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12971; decide +kernel
    rw [ha]
    exact (canonical12971 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA787 + difference 0 5) (sourceB787 + difference 5 0) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3912) := by
    have ha : (tripleCharges (sourceA787 + difference 0 5) (sourceB787 + difference 5 0) sourceC787) = raw12972 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12972; decide +kernel
    rw [ha]
    exact (canonical12972 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA787 + difference 1 0) (sourceB787 + difference 0 1) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1187) := by
    have ha : (tripleCharges (sourceA787 + difference 1 0) (sourceB787 + difference 0 1) sourceC787) = raw12973 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12973; decide +kernel
    rw [ha]
    exact (canonical12973 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA787 + difference 1 2) (sourceB787 + difference 2 1) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2839) := by
    have ha : (tripleCharges (sourceA787 + difference 1 2) (sourceB787 + difference 2 1) sourceC787) = raw12974 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12974; decide +kernel
    rw [ha]
    exact (canonical12974 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA787 + difference 1 3) (sourceB787 + difference 3 1) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA787 + difference 1 3) (sourceB787 + difference 3 1) sourceC787) = raw12975 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12975; decide +kernel
    rw [ha]
    exact (canonical12975 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA787 + difference 1 4) (sourceB787 + difference 4 1) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA787 + difference 1 4) (sourceB787 + difference 4 1) sourceC787) = raw12976 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12976; decide +kernel
    rw [ha]
    exact (canonical12976 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA787 + difference 1 5) (sourceB787 + difference 5 1) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA787 + difference 1 5) (sourceB787 + difference 5 1) sourceC787) = raw12977 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12977; decide +kernel
    rw [ha]
    exact (canonical12977 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA787 + difference 2 0) (sourceB787 + difference 0 2) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA787 + difference 2 0) (sourceB787 + difference 0 2) sourceC787) = raw12978 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12978; decide +kernel
    rw [ha]
    exact (canonical12978 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA787 + difference 2 1) (sourceB787 + difference 1 2) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2953) := by
    have ha : (tripleCharges (sourceA787 + difference 2 1) (sourceB787 + difference 1 2) sourceC787) = raw12979 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12979; decide +kernel
    rw [ha]
    exact (canonical12979 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA787 + difference 2 3) (sourceB787 + difference 3 2) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA787 + difference 2 3) (sourceB787 + difference 3 2) sourceC787) = raw12980 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12980; decide +kernel
    rw [ha]
    exact (canonical12980 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA787 + difference 2 4) (sourceB787 + difference 4 2) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA787 + difference 2 4) (sourceB787 + difference 4 2) sourceC787) = raw12981 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12981; decide +kernel
    rw [ha]
    exact (canonical12981 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA787 + difference 2 5) (sourceB787 + difference 5 2) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA787 + difference 2 5) (sourceB787 + difference 5 2) sourceC787) = raw12982 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12982; decide +kernel
    rw [ha]
    exact (canonical12982 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA787 + difference 3 0) (sourceB787 + difference 0 3) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA787 + difference 3 0) (sourceB787 + difference 0 3) sourceC787) = raw12983 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12983; decide +kernel
    rw [ha]
    exact (canonical12983 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA787 + difference 3 1) (sourceB787 + difference 1 3) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2908) := by
    have ha : (tripleCharges (sourceA787 + difference 3 1) (sourceB787 + difference 1 3) sourceC787) = raw12984 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12984; decide +kernel
    rw [ha]
    exact (canonical12984 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA787 + difference 3 2) (sourceB787 + difference 2 3) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2840) := by
    have ha : (tripleCharges (sourceA787 + difference 3 2) (sourceB787 + difference 2 3) sourceC787) = raw12985 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12985; decide +kernel
    rw [ha]
    exact (canonical12985 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA787 + difference 3 4) (sourceB787 + difference 4 3) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA787 + difference 3 4) (sourceB787 + difference 4 3) sourceC787) = raw12986 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12986; decide +kernel
    rw [ha]
    exact (canonical12986 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA787 + difference 3 5) (sourceB787 + difference 5 3) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA787 + difference 3 5) (sourceB787 + difference 5 3) sourceC787) = raw12987 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12987; decide +kernel
    rw [ha]
    exact (canonical12987 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA787 + difference 4 0) (sourceB787 + difference 0 4) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA787 + difference 4 0) (sourceB787 + difference 0 4) sourceC787) = raw12988 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12988; decide +kernel
    rw [ha]
    exact (canonical12988 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA787 + difference 4 1) (sourceB787 + difference 1 4) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2908) := by
    have ha : (tripleCharges (sourceA787 + difference 4 1) (sourceB787 + difference 1 4) sourceC787) = raw12989 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12989; decide +kernel
    rw [ha]
    exact (canonical12989 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA787 + difference 4 2) (sourceB787 + difference 2 4) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2840) := by
    have ha : (tripleCharges (sourceA787 + difference 4 2) (sourceB787 + difference 2 4) sourceC787) = raw12990 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12990; decide +kernel
    rw [ha]
    exact (canonical12990 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA787 + difference 4 3) (sourceB787 + difference 3 4) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA787 + difference 4 3) (sourceB787 + difference 3 4) sourceC787) = raw12991 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12991; decide +kernel
    rw [ha]
    exact (canonical12991 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA787 + difference 4 5) (sourceB787 + difference 5 4) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA787 + difference 4 5) (sourceB787 + difference 5 4) sourceC787) = raw12992 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12992; decide +kernel
    rw [ha]
    exact (canonical12992 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA787 + difference 5 0) (sourceB787 + difference 0 5) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA787 + difference 5 0) (sourceB787 + difference 0 5) sourceC787) = raw12993 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12993; decide +kernel
    rw [ha]
    exact (canonical12993 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA787 + difference 5 1) (sourceB787 + difference 1 5) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2908) := by
    have ha : (tripleCharges (sourceA787 + difference 5 1) (sourceB787 + difference 1 5) sourceC787) = raw12994 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12994; decide +kernel
    rw [ha]
    exact (canonical12994 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA787 + difference 5 2) (sourceB787 + difference 2 5) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2840) := by
    have ha : (tripleCharges (sourceA787 + difference 5 2) (sourceB787 + difference 2 5) sourceC787) = raw12995 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12995; decide +kernel
    rw [ha]
    exact (canonical12995 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA787 + difference 5 3) (sourceB787 + difference 3 5) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA787 + difference 5 3) (sourceB787 + difference 3 5) sourceC787) = raw12996 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12996; decide +kernel
    rw [ha]
    exact (canonical12996 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA787 + difference 5 4) (sourceB787 + difference 4 5) sourceC787) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA787 + difference 5 4) (sourceB787 + difference 4 5) sourceC787) = raw12997 := by
      apply Matrix.ext; unfold tripleCharges sourceA787 sourceB787 sourceC787 difference raw12997; decide +kernel
    rw [ha]
    exact (canonical12997 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA787 sourceB787 sourceC787
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm787, Integer.Sparse.eval]
  linarith only [hs]

def sourceA788 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB788 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC788 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceForm788 : Integer.Sparse Master := [(Sum.inr 4473, 1), (Sum.inr 4474, 3), (Sum.inr 4494, 1), (Sum.inr 5085, 3), (Sum.inr 5097, 1), (Sum.inr 5202, 1), (Sum.inr 5203, 3), (Sum.inr 5265, 3), (Sum.inr 5266, 6), (Sum.inr 5270, 3), (Sum.inr 5447, 1), (Sum.inr 5450, 3), (Sum.inr 5474, 1)]

theorem sourceEq788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm788 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA788 + difference 0 1) (sourceB788 + difference 1 0) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA788 + difference 0 1) (sourceB788 + difference 1 0) sourceC788) = raw12998 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw12998; decide +kernel
    rw [ha]
    exact (canonical12998 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA788 + difference 0 2) (sourceB788 + difference 2 0) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5474) := by
    have ha : (tripleCharges (sourceA788 + difference 0 2) (sourceB788 + difference 2 0) sourceC788) = raw12999 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw12999; decide +kernel
    rw [ha]
    exact (canonical12999 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA788 + difference 0 3) (sourceB788 + difference 3 0) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA788 + difference 0 3) (sourceB788 + difference 3 0) sourceC788) = raw13000 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13000; decide +kernel
    rw [ha]
    exact (canonical13000 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA788 + difference 0 4) (sourceB788 + difference 4 0) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA788 + difference 0 4) (sourceB788 + difference 4 0) sourceC788) = raw13001 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13001; decide +kernel
    rw [ha]
    exact (canonical13001 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA788 + difference 0 5) (sourceB788 + difference 5 0) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA788 + difference 0 5) (sourceB788 + difference 5 0) sourceC788) = raw13002 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13002; decide +kernel
    rw [ha]
    exact (canonical13002 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA788 + difference 1 0) (sourceB788 + difference 0 1) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4473) := by
    have ha : (tripleCharges (sourceA788 + difference 1 0) (sourceB788 + difference 0 1) sourceC788) = raw13003 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13003; decide +kernel
    rw [ha]
    exact (canonical13003 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA788 + difference 1 2) (sourceB788 + difference 2 1) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA788 + difference 1 2) (sourceB788 + difference 2 1) sourceC788) = raw13004 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13004; decide +kernel
    rw [ha]
    exact (canonical13004 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA788 + difference 1 3) (sourceB788 + difference 3 1) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA788 + difference 1 3) (sourceB788 + difference 3 1) sourceC788) = raw13005 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13005; decide +kernel
    rw [ha]
    exact (canonical13005 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA788 + difference 1 4) (sourceB788 + difference 4 1) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA788 + difference 1 4) (sourceB788 + difference 4 1) sourceC788) = raw13006 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13006; decide +kernel
    rw [ha]
    exact (canonical13006 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA788 + difference 1 5) (sourceB788 + difference 5 1) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA788 + difference 1 5) (sourceB788 + difference 5 1) sourceC788) = raw13007 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13007; decide +kernel
    rw [ha]
    exact (canonical13007 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA788 + difference 2 0) (sourceB788 + difference 0 2) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4494) := by
    have ha : (tripleCharges (sourceA788 + difference 2 0) (sourceB788 + difference 0 2) sourceC788) = raw13008 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13008; decide +kernel
    rw [ha]
    exact (canonical13008 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA788 + difference 2 1) (sourceB788 + difference 1 2) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5097) := by
    have ha : (tripleCharges (sourceA788 + difference 2 1) (sourceB788 + difference 1 2) sourceC788) = raw13009 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13009; decide +kernel
    rw [ha]
    exact (canonical13009 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA788 + difference 2 3) (sourceB788 + difference 3 2) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA788 + difference 2 3) (sourceB788 + difference 3 2) sourceC788) = raw13010 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13010; decide +kernel
    rw [ha]
    exact (canonical13010 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA788 + difference 2 4) (sourceB788 + difference 4 2) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA788 + difference 2 4) (sourceB788 + difference 4 2) sourceC788) = raw13011 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13011; decide +kernel
    rw [ha]
    exact (canonical13011 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA788 + difference 2 5) (sourceB788 + difference 5 2) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA788 + difference 2 5) (sourceB788 + difference 5 2) sourceC788) = raw13012 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13012; decide +kernel
    rw [ha]
    exact (canonical13012 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA788 + difference 3 0) (sourceB788 + difference 0 3) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA788 + difference 3 0) (sourceB788 + difference 0 3) sourceC788) = raw13013 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13013; decide +kernel
    rw [ha]
    exact (canonical13013 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA788 + difference 3 1) (sourceB788 + difference 1 3) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA788 + difference 3 1) (sourceB788 + difference 1 3) sourceC788) = raw13014 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13014; decide +kernel
    rw [ha]
    exact (canonical13014 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA788 + difference 3 2) (sourceB788 + difference 2 3) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA788 + difference 3 2) (sourceB788 + difference 2 3) sourceC788) = raw13015 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13015; decide +kernel
    rw [ha]
    exact (canonical13015 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA788 + difference 3 4) (sourceB788 + difference 4 3) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA788 + difference 3 4) (sourceB788 + difference 4 3) sourceC788) = raw13016 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13016; decide +kernel
    rw [ha]
    exact (canonical13016 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA788 + difference 3 5) (sourceB788 + difference 5 3) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA788 + difference 3 5) (sourceB788 + difference 5 3) sourceC788) = raw13017 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13017; decide +kernel
    rw [ha]
    exact (canonical13017 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA788 + difference 4 0) (sourceB788 + difference 0 4) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA788 + difference 4 0) (sourceB788 + difference 0 4) sourceC788) = raw13018 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13018; decide +kernel
    rw [ha]
    exact (canonical13018 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA788 + difference 4 1) (sourceB788 + difference 1 4) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA788 + difference 4 1) (sourceB788 + difference 1 4) sourceC788) = raw13019 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13019; decide +kernel
    rw [ha]
    exact (canonical13019 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA788 + difference 4 2) (sourceB788 + difference 2 4) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA788 + difference 4 2) (sourceB788 + difference 2 4) sourceC788) = raw13020 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13020; decide +kernel
    rw [ha]
    exact (canonical13020 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA788 + difference 4 3) (sourceB788 + difference 3 4) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA788 + difference 4 3) (sourceB788 + difference 3 4) sourceC788) = raw13021 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13021; decide +kernel
    rw [ha]
    exact (canonical13021 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA788 + difference 4 5) (sourceB788 + difference 5 4) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA788 + difference 4 5) (sourceB788 + difference 5 4) sourceC788) = raw13022 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13022; decide +kernel
    rw [ha]
    exact (canonical13022 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA788 + difference 5 0) (sourceB788 + difference 0 5) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA788 + difference 5 0) (sourceB788 + difference 0 5) sourceC788) = raw13023 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13023; decide +kernel
    rw [ha]
    exact (canonical13023 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA788 + difference 5 1) (sourceB788 + difference 1 5) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA788 + difference 5 1) (sourceB788 + difference 1 5) sourceC788) = raw13024 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13024; decide +kernel
    rw [ha]
    exact (canonical13024 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA788 + difference 5 2) (sourceB788 + difference 2 5) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA788 + difference 5 2) (sourceB788 + difference 2 5) sourceC788) = raw13025 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13025; decide +kernel
    rw [ha]
    exact (canonical13025 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA788 + difference 5 3) (sourceB788 + difference 3 5) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA788 + difference 5 3) (sourceB788 + difference 3 5) sourceC788) = raw13026 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13026; decide +kernel
    rw [ha]
    exact (canonical13026 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA788 + difference 5 4) (sourceB788 + difference 4 5) sourceC788) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA788 + difference 5 4) (sourceB788 + difference 4 5) sourceC788) = raw13027 := by
      apply Matrix.ext; unfold tripleCharges sourceA788 sourceB788 sourceC788 difference raw13027; decide +kernel
    rw [ha]
    exact (canonical13027 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA788 sourceB788 sourceC788
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm788, Integer.Sparse.eval]
  linarith only [hs]

def sourceA789 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB789 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC789 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceForm789 : Integer.Sparse Master := [(Sum.inr 1699, 1), (Sum.inr 1700, 1), (Sum.inr 1709, 3), (Sum.inr 3058, 1), (Sum.inr 3075, 3), (Sum.inr 3461, 3), (Sum.inr 3526, 3), (Sum.inr 3535, 6), (Sum.inr 3617, 1), (Sum.inr 3621, 3), (Sum.inr 3962, 1), (Sum.inr 4025, 1), (Sum.inr 4029, 3)]

theorem sourceEq789 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm789 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA789 + difference 0 1) (sourceB789 + difference 1 0) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4025) := by
    have ha : (tripleCharges (sourceA789 + difference 0 1) (sourceB789 + difference 1 0) sourceC789) = raw13028 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13028; decide +kernel
    rw [ha]
    exact (canonical13028 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA789 + difference 0 2) (sourceB789 + difference 2 0) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3962) := by
    have ha : (tripleCharges (sourceA789 + difference 0 2) (sourceB789 + difference 2 0) sourceC789) = raw13029 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13029; decide +kernel
    rw [ha]
    exact (canonical13029 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA789 + difference 0 3) (sourceB789 + difference 3 0) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA789 + difference 0 3) (sourceB789 + difference 3 0) sourceC789) = raw13030 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13030; decide +kernel
    rw [ha]
    exact (canonical13030 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA789 + difference 0 4) (sourceB789 + difference 4 0) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA789 + difference 0 4) (sourceB789 + difference 4 0) sourceC789) = raw13031 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13031; decide +kernel
    rw [ha]
    exact (canonical13031 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA789 + difference 0 5) (sourceB789 + difference 5 0) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA789 + difference 0 5) (sourceB789 + difference 5 0) sourceC789) = raw13032 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13032; decide +kernel
    rw [ha]
    exact (canonical13032 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA789 + difference 1 0) (sourceB789 + difference 0 1) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA789 + difference 1 0) (sourceB789 + difference 0 1) sourceC789) = raw13033 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13033; decide +kernel
    rw [ha]
    exact (canonical13033 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA789 + difference 1 2) (sourceB789 + difference 2 1) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3617) := by
    have ha : (tripleCharges (sourceA789 + difference 1 2) (sourceB789 + difference 2 1) sourceC789) = raw13034 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13034; decide +kernel
    rw [ha]
    exact (canonical13034 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA789 + difference 1 3) (sourceB789 + difference 3 1) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA789 + difference 1 3) (sourceB789 + difference 3 1) sourceC789) = raw13035 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13035; decide +kernel
    rw [ha]
    exact (canonical13035 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA789 + difference 1 4) (sourceB789 + difference 4 1) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA789 + difference 1 4) (sourceB789 + difference 4 1) sourceC789) = raw13036 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13036; decide +kernel
    rw [ha]
    exact (canonical13036 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA789 + difference 1 5) (sourceB789 + difference 5 1) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA789 + difference 1 5) (sourceB789 + difference 5 1) sourceC789) = raw13037 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13037; decide +kernel
    rw [ha]
    exact (canonical13037 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA789 + difference 2 0) (sourceB789 + difference 0 2) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA789 + difference 2 0) (sourceB789 + difference 0 2) sourceC789) = raw13038 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13038; decide +kernel
    rw [ha]
    exact (canonical13038 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA789 + difference 2 1) (sourceB789 + difference 1 2) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3058) := by
    have ha : (tripleCharges (sourceA789 + difference 2 1) (sourceB789 + difference 1 2) sourceC789) = raw13039 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13039; decide +kernel
    rw [ha]
    exact (canonical13039 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA789 + difference 2 3) (sourceB789 + difference 3 2) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA789 + difference 2 3) (sourceB789 + difference 3 2) sourceC789) = raw13040 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13040; decide +kernel
    rw [ha]
    exact (canonical13040 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA789 + difference 2 4) (sourceB789 + difference 4 2) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA789 + difference 2 4) (sourceB789 + difference 4 2) sourceC789) = raw13041 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13041; decide +kernel
    rw [ha]
    exact (canonical13041 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA789 + difference 2 5) (sourceB789 + difference 5 2) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA789 + difference 2 5) (sourceB789 + difference 5 2) sourceC789) = raw13042 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13042; decide +kernel
    rw [ha]
    exact (canonical13042 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA789 + difference 3 0) (sourceB789 + difference 0 3) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA789 + difference 3 0) (sourceB789 + difference 0 3) sourceC789) = raw13043 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13043; decide +kernel
    rw [ha]
    exact (canonical13043 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA789 + difference 3 1) (sourceB789 + difference 1 3) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA789 + difference 3 1) (sourceB789 + difference 1 3) sourceC789) = raw13044 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13044; decide +kernel
    rw [ha]
    exact (canonical13044 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA789 + difference 3 2) (sourceB789 + difference 2 3) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3621) := by
    have ha : (tripleCharges (sourceA789 + difference 3 2) (sourceB789 + difference 2 3) sourceC789) = raw13045 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13045; decide +kernel
    rw [ha]
    exact (canonical13045 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA789 + difference 3 4) (sourceB789 + difference 4 3) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA789 + difference 3 4) (sourceB789 + difference 4 3) sourceC789) = raw13046 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13046; decide +kernel
    rw [ha]
    exact (canonical13046 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA789 + difference 3 5) (sourceB789 + difference 5 3) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA789 + difference 3 5) (sourceB789 + difference 5 3) sourceC789) = raw13047 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13047; decide +kernel
    rw [ha]
    exact (canonical13047 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA789 + difference 4 0) (sourceB789 + difference 0 4) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA789 + difference 4 0) (sourceB789 + difference 0 4) sourceC789) = raw13048 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13048; decide +kernel
    rw [ha]
    exact (canonical13048 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA789 + difference 4 1) (sourceB789 + difference 1 4) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA789 + difference 4 1) (sourceB789 + difference 1 4) sourceC789) = raw13049 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13049; decide +kernel
    rw [ha]
    exact (canonical13049 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA789 + difference 4 2) (sourceB789 + difference 2 4) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3621) := by
    have ha : (tripleCharges (sourceA789 + difference 4 2) (sourceB789 + difference 2 4) sourceC789) = raw13050 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13050; decide +kernel
    rw [ha]
    exact (canonical13050 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA789 + difference 4 3) (sourceB789 + difference 3 4) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA789 + difference 4 3) (sourceB789 + difference 3 4) sourceC789) = raw13051 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13051; decide +kernel
    rw [ha]
    exact (canonical13051 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA789 + difference 4 5) (sourceB789 + difference 5 4) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA789 + difference 4 5) (sourceB789 + difference 5 4) sourceC789) = raw13052 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13052; decide +kernel
    rw [ha]
    exact (canonical13052 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA789 + difference 5 0) (sourceB789 + difference 0 5) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA789 + difference 5 0) (sourceB789 + difference 0 5) sourceC789) = raw13053 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13053; decide +kernel
    rw [ha]
    exact (canonical13053 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA789 + difference 5 1) (sourceB789 + difference 1 5) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA789 + difference 5 1) (sourceB789 + difference 1 5) sourceC789) = raw13054 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13054; decide +kernel
    rw [ha]
    exact (canonical13054 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA789 + difference 5 2) (sourceB789 + difference 2 5) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3621) := by
    have ha : (tripleCharges (sourceA789 + difference 5 2) (sourceB789 + difference 2 5) sourceC789) = raw13055 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13055; decide +kernel
    rw [ha]
    exact (canonical13055 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA789 + difference 5 3) (sourceB789 + difference 3 5) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA789 + difference 5 3) (sourceB789 + difference 3 5) sourceC789) = raw13056 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13056; decide +kernel
    rw [ha]
    exact (canonical13056 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA789 + difference 5 4) (sourceB789 + difference 4 5) sourceC789) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA789 + difference 5 4) (sourceB789 + difference 4 5) sourceC789) = raw13057 := by
      apply Matrix.ext; unfold tripleCharges sourceA789 sourceB789 sourceC789 difference raw13057; decide +kernel
    rw [ha]
    exact (canonical13057 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA789 sourceB789 sourceC789
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm789, Integer.Sparse.eval]
  linarith only [hs]

def sourceA790 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB790 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC790 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceForm790 : Integer.Sparse Master := [(Sum.inr 3053, 1), (Sum.inr 3909, 1), (Sum.inr 3910, 3), (Sum.inr 3962, 1), (Sum.inr 4091, -1)]

theorem sourceEq790 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm790 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA790 + difference 0 0) (sourceB790 + difference 0 0) sourceC790) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA790 + difference 0 0) (sourceB790 + difference 0 0) sourceC790) = raw13058 := by
      apply Matrix.ext; unfold tripleCharges sourceA790 sourceB790 sourceC790 difference raw13058; decide +kernel
    rw [ha]
    exact (canonical13058 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA790 + difference 0 1) (sourceB790 + difference 1 0) sourceC790) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA790 + difference 0 1) (sourceB790 + difference 1 0) sourceC790) = raw13059 := by
      apply Matrix.ext; unfold tripleCharges sourceA790 sourceB790 sourceC790 difference raw13059; decide +kernel
    rw [ha]
    exact (canonical13059 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA790 + difference 0 2) (sourceB790 + difference 2 0) sourceC790) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3962) := by
    have ha : (tripleCharges (sourceA790 + difference 0 2) (sourceB790 + difference 2 0) sourceC790) = raw13060 := by
      apply Matrix.ext; unfold tripleCharges sourceA790 sourceB790 sourceC790 difference raw13060; decide +kernel
    rw [ha]
    exact (canonical13060 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA790 + difference 0 3) (sourceB790 + difference 3 0) sourceC790) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA790 + difference 0 3) (sourceB790 + difference 3 0) sourceC790) = raw13061 := by
      apply Matrix.ext; unfold tripleCharges sourceA790 sourceB790 sourceC790 difference raw13061; decide +kernel
    rw [ha]
    exact (canonical13061 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA790 + difference 0 4) (sourceB790 + difference 4 0) sourceC790) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA790 + difference 0 4) (sourceB790 + difference 4 0) sourceC790) = raw13062 := by
      apply Matrix.ext; unfold tripleCharges sourceA790 sourceB790 sourceC790 difference raw13062; decide +kernel
    rw [ha]
    exact (canonical13062 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA790 + difference 0 5) (sourceB790 + difference 5 0) sourceC790) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA790 + difference 0 5) (sourceB790 + difference 5 0) sourceC790) = raw13063 := by
      apply Matrix.ext; unfold tripleCharges sourceA790 sourceB790 sourceC790 difference raw13063; decide +kernel
    rw [ha]
    exact (canonical13063 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA790 + sourceB790) sourceC790) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA790 + sourceB790) sourceC790) = raw13064 := by
      apply Matrix.ext; unfold doubleCharges sourceA790 sourceB790 sourceC790 raw13064; decide +kernel
    rw [ha]
    exact (canonical13064 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA790 sourceB790 sourceC790
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm790, Integer.Sparse.eval]
  linarith only [hs]

def sourceA791 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB791 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC791 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceForm791 : Integer.Sparse Master := [(Sum.inr 2746, 1), (Sum.inr 2976, 3), (Sum.inr 3053, 1), (Sum.inr 3909, 1), (Sum.inr 4091, -1)]

theorem sourceEq791 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm791 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA791 + difference 0 1) (sourceB791 + difference 1 0) sourceC791) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA791 + difference 0 1) (sourceB791 + difference 1 0) sourceC791) = raw13059 := by
      apply Matrix.ext; unfold tripleCharges sourceA791 sourceB791 sourceC791 difference raw13059; decide +kernel
    rw [ha]
    exact (canonical13059 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA791 + difference 1 1) (sourceB791 + difference 1 1) sourceC791) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA791 + difference 1 1) (sourceB791 + difference 1 1) sourceC791) = raw13058 := by
      apply Matrix.ext; unfold tripleCharges sourceA791 sourceB791 sourceC791 difference raw13058; decide +kernel
    rw [ha]
    exact (canonical13058 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA791 + difference 2 1) (sourceB791 + difference 1 2) sourceC791) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2746) := by
    have ha : (tripleCharges (sourceA791 + difference 2 1) (sourceB791 + difference 1 2) sourceC791) = raw13065 := by
      apply Matrix.ext; unfold tripleCharges sourceA791 sourceB791 sourceC791 difference raw13065; decide +kernel
    rw [ha]
    exact (canonical13065 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA791 + difference 3 1) (sourceB791 + difference 1 3) sourceC791) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA791 + difference 3 1) (sourceB791 + difference 1 3) sourceC791) = raw13066 := by
      apply Matrix.ext; unfold tripleCharges sourceA791 sourceB791 sourceC791 difference raw13066; decide +kernel
    rw [ha]
    exact (canonical13066 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA791 + difference 4 1) (sourceB791 + difference 1 4) sourceC791) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA791 + difference 4 1) (sourceB791 + difference 1 4) sourceC791) = raw13067 := by
      apply Matrix.ext; unfold tripleCharges sourceA791 sourceB791 sourceC791 difference raw13067; decide +kernel
    rw [ha]
    exact (canonical13067 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA791 + difference 5 1) (sourceB791 + difference 1 5) sourceC791) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA791 + difference 5 1) (sourceB791 + difference 1 5) sourceC791) = raw13068 := by
      apply Matrix.ext; unfold tripleCharges sourceA791 sourceB791 sourceC791 difference raw13068; decide +kernel
    rw [ha]
    exact (canonical13068 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA791 + sourceB791) sourceC791) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA791 + sourceB791) sourceC791) = raw13064 := by
      apply Matrix.ext; unfold doubleCharges sourceA791 sourceB791 sourceC791 raw13064; decide +kernel
    rw [ha]
    exact (canonical13064 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA791 sourceB791 sourceC791
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm791, Integer.Sparse.eval]
  linarith only [hs]

def sourceA792 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB792 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC792 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm792 : Integer.Sparse Master := [(Sum.inr 4878, 1), (Sum.inr 4879, 3), (Sum.inr 4885, 1), (Sum.inr 4886, 1), (Sum.inr 4889, 3), (Sum.inr 5227, 1), (Sum.inr 5237, 3), (Sum.inr 5265, 3), (Sum.inr 5273, 1), (Sum.inr 5283, 1), (Sum.inr 5286, 3), (Sum.inr 5292, 3), (Sum.inr 5299, 6)]

theorem sourceEq792 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm792 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA792 + difference 0 1) (sourceB792 + difference 1 0) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5227) := by
    have ha : (tripleCharges (sourceA792 + difference 0 1) (sourceB792 + difference 1 0) sourceC792) = raw12001 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12001; decide +kernel
    rw [ha]
    exact (canonical12001 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA792 + difference 0 2) (sourceB792 + difference 2 0) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA792 + difference 0 2) (sourceB792 + difference 2 0) sourceC792) = raw12652 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12652; decide +kernel
    rw [ha]
    exact (canonical12652 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA792 + difference 0 3) (sourceB792 + difference 3 0) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA792 + difference 0 3) (sourceB792 + difference 3 0) sourceC792) = raw12883 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12883; decide +kernel
    rw [ha]
    exact (canonical12883 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA792 + difference 0 4) (sourceB792 + difference 4 0) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA792 + difference 0 4) (sourceB792 + difference 4 0) sourceC792) = raw13069 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13069; decide +kernel
    rw [ha]
    exact (canonical13069 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA792 + difference 0 5) (sourceB792 + difference 5 0) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA792 + difference 0 5) (sourceB792 + difference 5 0) sourceC792) = raw13070 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13070; decide +kernel
    rw [ha]
    exact (canonical13070 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA792 + difference 1 0) (sourceB792 + difference 0 1) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA792 + difference 1 0) (sourceB792 + difference 0 1) sourceC792) = raw13071 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13071; decide +kernel
    rw [ha]
    exact (canonical13071 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA792 + difference 1 2) (sourceB792 + difference 2 1) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA792 + difference 1 2) (sourceB792 + difference 2 1) sourceC792) = raw12655 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12655; decide +kernel
    rw [ha]
    exact (canonical12655 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA792 + difference 1 3) (sourceB792 + difference 3 1) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA792 + difference 1 3) (sourceB792 + difference 3 1) sourceC792) = raw12887 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12887; decide +kernel
    rw [ha]
    exact (canonical12887 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA792 + difference 1 4) (sourceB792 + difference 4 1) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA792 + difference 1 4) (sourceB792 + difference 4 1) sourceC792) = raw13072 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13072; decide +kernel
    rw [ha]
    exact (canonical13072 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA792 + difference 1 5) (sourceB792 + difference 5 1) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA792 + difference 1 5) (sourceB792 + difference 5 1) sourceC792) = raw13073 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13073; decide +kernel
    rw [ha]
    exact (canonical13073 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA792 + difference 2 0) (sourceB792 + difference 0 2) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4886) := by
    have ha : (tripleCharges (sourceA792 + difference 2 0) (sourceB792 + difference 0 2) sourceC792) = raw13074 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13074; decide +kernel
    rw [ha]
    exact (canonical13074 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA792 + difference 2 1) (sourceB792 + difference 1 2) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4878) := by
    have ha : (tripleCharges (sourceA792 + difference 2 1) (sourceB792 + difference 1 2) sourceC792) = raw12010 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12010; decide +kernel
    rw [ha]
    exact (canonical12010 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA792 + difference 2 3) (sourceB792 + difference 3 2) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA792 + difference 2 3) (sourceB792 + difference 3 2) sourceC792) = raw12891 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12891; decide +kernel
    rw [ha]
    exact (canonical12891 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA792 + difference 2 4) (sourceB792 + difference 4 2) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA792 + difference 2 4) (sourceB792 + difference 4 2) sourceC792) = raw13075 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13075; decide +kernel
    rw [ha]
    exact (canonical13075 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA792 + difference 2 5) (sourceB792 + difference 5 2) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA792 + difference 2 5) (sourceB792 + difference 5 2) sourceC792) = raw13076 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13076; decide +kernel
    rw [ha]
    exact (canonical13076 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA792 + difference 3 0) (sourceB792 + difference 0 3) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA792 + difference 3 0) (sourceB792 + difference 0 3) sourceC792) = raw13077 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13077; decide +kernel
    rw [ha]
    exact (canonical13077 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA792 + difference 3 1) (sourceB792 + difference 1 3) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA792 + difference 3 1) (sourceB792 + difference 1 3) sourceC792) = raw12014 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12014; decide +kernel
    rw [ha]
    exact (canonical12014 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA792 + difference 3 2) (sourceB792 + difference 2 3) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA792 + difference 3 2) (sourceB792 + difference 2 3) sourceC792) = raw12658 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12658; decide +kernel
    rw [ha]
    exact (canonical12658 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA792 + difference 3 4) (sourceB792 + difference 4 3) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA792 + difference 3 4) (sourceB792 + difference 4 3) sourceC792) = raw13078 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13078; decide +kernel
    rw [ha]
    exact (canonical13078 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA792 + difference 3 5) (sourceB792 + difference 5 3) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA792 + difference 3 5) (sourceB792 + difference 5 3) sourceC792) = raw13079 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13079; decide +kernel
    rw [ha]
    exact (canonical13079 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA792 + difference 4 0) (sourceB792 + difference 0 4) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA792 + difference 4 0) (sourceB792 + difference 0 4) sourceC792) = raw13080 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13080; decide +kernel
    rw [ha]
    exact (canonical13080 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA792 + difference 4 1) (sourceB792 + difference 1 4) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA792 + difference 4 1) (sourceB792 + difference 1 4) sourceC792) = raw12018 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12018; decide +kernel
    rw [ha]
    exact (canonical12018 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA792 + difference 4 2) (sourceB792 + difference 2 4) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA792 + difference 4 2) (sourceB792 + difference 2 4) sourceC792) = raw12660 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12660; decide +kernel
    rw [ha]
    exact (canonical12660 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA792 + difference 4 3) (sourceB792 + difference 3 4) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA792 + difference 4 3) (sourceB792 + difference 3 4) sourceC792) = raw12894 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12894; decide +kernel
    rw [ha]
    exact (canonical12894 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA792 + difference 4 5) (sourceB792 + difference 5 4) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA792 + difference 4 5) (sourceB792 + difference 5 4) sourceC792) = raw13081 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw13081; decide +kernel
    rw [ha]
    exact (canonical13081 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA792 + difference 5 0) (sourceB792 + difference 0 5) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA792 + difference 5 0) (sourceB792 + difference 0 5) sourceC792) = raw12002 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12002; decide +kernel
    rw [ha]
    exact (canonical12002 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA792 + difference 5 1) (sourceB792 + difference 1 5) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA792 + difference 5 1) (sourceB792 + difference 1 5) sourceC792) = raw11674 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw11674; decide +kernel
    rw [ha]
    exact (canonical11674 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA792 + difference 5 2) (sourceB792 + difference 2 5) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA792 + difference 5 2) (sourceB792 + difference 2 5) sourceC792) = raw11669 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw11669; decide +kernel
    rw [ha]
    exact (canonical11669 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA792 + difference 5 3) (sourceB792 + difference 3 5) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA792 + difference 5 3) (sourceB792 + difference 3 5) sourceC792) = raw12003 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12003; decide +kernel
    rw [ha]
    exact (canonical12003 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA792 + difference 5 4) (sourceB792 + difference 4 5) sourceC792) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA792 + difference 5 4) (sourceB792 + difference 4 5) sourceC792) = raw12004 := by
      apply Matrix.ext; unfold tripleCharges sourceA792 sourceB792 sourceC792 difference raw12004; decide +kernel
    rw [ha]
    exact (canonical12004 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA792 sourceB792 sourceC792
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm792, Integer.Sparse.eval]
  linarith only [hs]

def sourceA793 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB793 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC793 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm793 : Integer.Sparse Master := [(Sum.inr 2234, 1), (Sum.inr 2235, 1), (Sum.inr 2246, 3), (Sum.inr 2671, 1), (Sum.inr 2684, 3), (Sum.inr 2741, 1), (Sum.inr 3023, 3), (Sum.inr 3037, 3), (Sum.inr 3051, 6), (Sum.inr 3076, 1), (Sum.inr 3100, 3), (Sum.inr 3221, 1), (Sum.inr 3223, 3)]

theorem sourceEq793 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm793 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA793 + difference 0 1) (sourceB793 + difference 1 0) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA793 + difference 0 1) (sourceB793 + difference 1 0) sourceC793) = raw12045 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12045; decide +kernel
    rw [ha]
    exact (canonical12045 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA793 + difference 0 2) (sourceB793 + difference 2 0) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA793 + difference 0 2) (sourceB793 + difference 2 0) sourceC793) = raw13082 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13082; decide +kernel
    rw [ha]
    exact (canonical13082 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA793 + difference 0 3) (sourceB793 + difference 3 0) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA793 + difference 0 3) (sourceB793 + difference 3 0) sourceC793) = raw12911 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12911; decide +kernel
    rw [ha]
    exact (canonical12911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA793 + difference 0 4) (sourceB793 + difference 4 0) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA793 + difference 0 4) (sourceB793 + difference 4 0) sourceC793) = raw13083 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13083; decide +kernel
    rw [ha]
    exact (canonical13083 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA793 + difference 0 5) (sourceB793 + difference 5 0) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA793 + difference 0 5) (sourceB793 + difference 5 0) sourceC793) = raw13084 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13084; decide +kernel
    rw [ha]
    exact (canonical13084 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA793 + difference 1 0) (sourceB793 + difference 0 1) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA793 + difference 1 0) (sourceB793 + difference 0 1) sourceC793) = raw13085 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13085; decide +kernel
    rw [ha]
    exact (canonical13085 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA793 + difference 1 2) (sourceB793 + difference 2 1) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3076) := by
    have ha : (tripleCharges (sourceA793 + difference 1 2) (sourceB793 + difference 2 1) sourceC793) = raw13086 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13086; decide +kernel
    rw [ha]
    exact (canonical13086 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA793 + difference 1 3) (sourceB793 + difference 3 1) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA793 + difference 1 3) (sourceB793 + difference 3 1) sourceC793) = raw12915 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12915; decide +kernel
    rw [ha]
    exact (canonical12915 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA793 + difference 1 4) (sourceB793 + difference 4 1) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA793 + difference 1 4) (sourceB793 + difference 4 1) sourceC793) = raw13087 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13087; decide +kernel
    rw [ha]
    exact (canonical13087 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA793 + difference 1 5) (sourceB793 + difference 5 1) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA793 + difference 1 5) (sourceB793 + difference 5 1) sourceC793) = raw13088 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13088; decide +kernel
    rw [ha]
    exact (canonical13088 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA793 + difference 2 0) (sourceB793 + difference 0 2) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA793 + difference 2 0) (sourceB793 + difference 0 2) sourceC793) = raw13089 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13089; decide +kernel
    rw [ha]
    exact (canonical13089 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA793 + difference 2 1) (sourceB793 + difference 1 2) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA793 + difference 2 1) (sourceB793 + difference 1 2) sourceC793) = raw12054 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12054; decide +kernel
    rw [ha]
    exact (canonical12054 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA793 + difference 2 3) (sourceB793 + difference 3 2) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA793 + difference 2 3) (sourceB793 + difference 3 2) sourceC793) = raw12919 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12919; decide +kernel
    rw [ha]
    exact (canonical12919 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA793 + difference 2 4) (sourceB793 + difference 4 2) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA793 + difference 2 4) (sourceB793 + difference 4 2) sourceC793) = raw13090 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13090; decide +kernel
    rw [ha]
    exact (canonical13090 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA793 + difference 2 5) (sourceB793 + difference 5 2) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA793 + difference 2 5) (sourceB793 + difference 5 2) sourceC793) = raw13091 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13091; decide +kernel
    rw [ha]
    exact (canonical13091 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA793 + difference 3 0) (sourceB793 + difference 0 3) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA793 + difference 3 0) (sourceB793 + difference 0 3) sourceC793) = raw13092 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13092; decide +kernel
    rw [ha]
    exact (canonical13092 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA793 + difference 3 1) (sourceB793 + difference 1 3) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA793 + difference 3 1) (sourceB793 + difference 1 3) sourceC793) = raw12058 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12058; decide +kernel
    rw [ha]
    exact (canonical12058 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA793 + difference 3 2) (sourceB793 + difference 2 3) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA793 + difference 3 2) (sourceB793 + difference 2 3) sourceC793) = raw13093 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13093; decide +kernel
    rw [ha]
    exact (canonical13093 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA793 + difference 3 4) (sourceB793 + difference 4 3) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA793 + difference 3 4) (sourceB793 + difference 4 3) sourceC793) = raw13094 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13094; decide +kernel
    rw [ha]
    exact (canonical13094 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA793 + difference 3 5) (sourceB793 + difference 5 3) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA793 + difference 3 5) (sourceB793 + difference 5 3) sourceC793) = raw13095 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13095; decide +kernel
    rw [ha]
    exact (canonical13095 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA793 + difference 4 0) (sourceB793 + difference 0 4) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA793 + difference 4 0) (sourceB793 + difference 0 4) sourceC793) = raw13096 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13096; decide +kernel
    rw [ha]
    exact (canonical13096 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA793 + difference 4 1) (sourceB793 + difference 1 4) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA793 + difference 4 1) (sourceB793 + difference 1 4) sourceC793) = raw12062 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12062; decide +kernel
    rw [ha]
    exact (canonical12062 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA793 + difference 4 2) (sourceB793 + difference 2 4) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA793 + difference 4 2) (sourceB793 + difference 2 4) sourceC793) = raw13097 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13097; decide +kernel
    rw [ha]
    exact (canonical13097 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA793 + difference 4 3) (sourceB793 + difference 3 4) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA793 + difference 4 3) (sourceB793 + difference 3 4) sourceC793) = raw12922 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12922; decide +kernel
    rw [ha]
    exact (canonical12922 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA793 + difference 4 5) (sourceB793 + difference 5 4) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA793 + difference 4 5) (sourceB793 + difference 5 4) sourceC793) = raw13098 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw13098; decide +kernel
    rw [ha]
    exact (canonical13098 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA793 + difference 5 0) (sourceB793 + difference 0 5) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA793 + difference 5 0) (sourceB793 + difference 0 5) sourceC793) = raw12046 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12046; decide +kernel
    rw [ha]
    exact (canonical12046 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA793 + difference 5 1) (sourceB793 + difference 1 5) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA793 + difference 5 1) (sourceB793 + difference 1 5) sourceC793) = raw11734 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw11734; decide +kernel
    rw [ha]
    exact (canonical11734 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA793 + difference 5 2) (sourceB793 + difference 2 5) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA793 + difference 5 2) (sourceB793 + difference 2 5) sourceC793) = raw11729 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw11729; decide +kernel
    rw [ha]
    exact (canonical11729 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA793 + difference 5 3) (sourceB793 + difference 3 5) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA793 + difference 5 3) (sourceB793 + difference 3 5) sourceC793) = raw12047 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12047; decide +kernel
    rw [ha]
    exact (canonical12047 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA793 + difference 5 4) (sourceB793 + difference 4 5) sourceC793) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA793 + difference 5 4) (sourceB793 + difference 4 5) sourceC793) = raw12048 := by
      apply Matrix.ext; unfold tripleCharges sourceA793 sourceB793 sourceC793 difference raw12048; decide +kernel
    rw [ha]
    exact (canonical12048 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA793 sourceB793 sourceC793
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm793, Integer.Sparse.eval]
  linarith only [hs]

def sourceA794 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB794 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC794 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceForm794 : Integer.Sparse Master := [(Sum.inr 4579, 1), (Sum.inr 4580, 1), (Sum.inr 4582, 1), (Sum.inr 4599, 2), (Sum.inr 5057, 2), (Sum.inr 5097, 1), (Sum.inr 5190, 2), (Sum.inr 5191, 2), (Sum.inr 5197, 2), (Sum.inr 5250, 1), (Sum.inr 5251, 1), (Sum.inr 5257, 2), (Sum.inr 5270, 1), (Sum.inr 5277, 1), (Sum.inr 5281, 2), (Sum.inr 5282, 1), (Sum.inr 5290, 2), (Sum.inr 5433, 1), (Sum.inr 5445, 2), (Sum.inr 5447, 1), (Sum.inr 5450, 1)]

theorem sourceEq794 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm794 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA794 + difference 0 1) (sourceB794 + difference 1 0) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA794 + difference 0 1) (sourceB794 + difference 1 0) sourceC794) = raw13099 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13099; decide +kernel
    rw [ha]
    exact (canonical13099 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA794 + difference 0 2) (sourceB794 + difference 2 0) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA794 + difference 0 2) (sourceB794 + difference 2 0) sourceC794) = raw13100 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13100; decide +kernel
    rw [ha]
    exact (canonical13100 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA794 + difference 0 3) (sourceB794 + difference 3 0) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA794 + difference 0 3) (sourceB794 + difference 3 0) sourceC794) = raw13101 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13101; decide +kernel
    rw [ha]
    exact (canonical13101 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA794 + difference 0 4) (sourceB794 + difference 4 0) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA794 + difference 0 4) (sourceB794 + difference 4 0) sourceC794) = raw13102 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13102; decide +kernel
    rw [ha]
    exact (canonical13102 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA794 + difference 0 5) (sourceB794 + difference 5 0) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA794 + difference 0 5) (sourceB794 + difference 5 0) sourceC794) = raw13103 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13103; decide +kernel
    rw [ha]
    exact (canonical13103 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA794 + difference 1 0) (sourceB794 + difference 0 1) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA794 + difference 1 0) (sourceB794 + difference 0 1) sourceC794) = raw13104 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13104; decide +kernel
    rw [ha]
    exact (canonical13104 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA794 + difference 1 2) (sourceB794 + difference 2 1) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA794 + difference 1 2) (sourceB794 + difference 2 1) sourceC794) = raw13105 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13105; decide +kernel
    rw [ha]
    exact (canonical13105 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA794 + difference 1 3) (sourceB794 + difference 3 1) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA794 + difference 1 3) (sourceB794 + difference 3 1) sourceC794) = raw13106 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13106; decide +kernel
    rw [ha]
    exact (canonical13106 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA794 + difference 1 4) (sourceB794 + difference 4 1) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA794 + difference 1 4) (sourceB794 + difference 4 1) sourceC794) = raw13107 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13107; decide +kernel
    rw [ha]
    exact (canonical13107 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA794 + difference 1 5) (sourceB794 + difference 5 1) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA794 + difference 1 5) (sourceB794 + difference 5 1) sourceC794) = raw13108 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13108; decide +kernel
    rw [ha]
    exact (canonical13108 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA794 + difference 2 0) (sourceB794 + difference 0 2) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA794 + difference 2 0) (sourceB794 + difference 0 2) sourceC794) = raw13109 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13109; decide +kernel
    rw [ha]
    exact (canonical13109 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA794 + difference 2 1) (sourceB794 + difference 1 2) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA794 + difference 2 1) (sourceB794 + difference 1 2) sourceC794) = raw13110 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13110; decide +kernel
    rw [ha]
    exact (canonical13110 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA794 + difference 2 3) (sourceB794 + difference 3 2) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA794 + difference 2 3) (sourceB794 + difference 3 2) sourceC794) = raw13111 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13111; decide +kernel
    rw [ha]
    exact (canonical13111 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA794 + difference 2 4) (sourceB794 + difference 4 2) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA794 + difference 2 4) (sourceB794 + difference 4 2) sourceC794) = raw13112 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13112; decide +kernel
    rw [ha]
    exact (canonical13112 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA794 + difference 2 5) (sourceB794 + difference 5 2) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA794 + difference 2 5) (sourceB794 + difference 5 2) sourceC794) = raw13113 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13113; decide +kernel
    rw [ha]
    exact (canonical13113 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA794 + difference 3 0) (sourceB794 + difference 0 3) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4579) := by
    have ha : (tripleCharges (sourceA794 + difference 3 0) (sourceB794 + difference 0 3) sourceC794) = raw13114 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13114; decide +kernel
    rw [ha]
    exact (canonical13114 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA794 + difference 3 1) (sourceB794 + difference 1 3) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5057) := by
    have ha : (tripleCharges (sourceA794 + difference 3 1) (sourceB794 + difference 1 3) sourceC794) = raw13115 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13115; decide +kernel
    rw [ha]
    exact (canonical13115 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA794 + difference 3 2) (sourceB794 + difference 2 3) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5057) := by
    have ha : (tripleCharges (sourceA794 + difference 3 2) (sourceB794 + difference 2 3) sourceC794) = raw13116 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13116; decide +kernel
    rw [ha]
    exact (canonical13116 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA794 + difference 3 4) (sourceB794 + difference 4 3) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA794 + difference 3 4) (sourceB794 + difference 4 3) sourceC794) = raw13117 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13117; decide +kernel
    rw [ha]
    exact (canonical13117 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA794 + difference 3 5) (sourceB794 + difference 5 3) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5097) := by
    have ha : (tripleCharges (sourceA794 + difference 3 5) (sourceB794 + difference 5 3) sourceC794) = raw13118 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13118; decide +kernel
    rw [ha]
    exact (canonical13118 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA794 + difference 4 0) (sourceB794 + difference 0 4) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4580) := by
    have ha : (tripleCharges (sourceA794 + difference 4 0) (sourceB794 + difference 0 4) sourceC794) = raw13119 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13119; decide +kernel
    rw [ha]
    exact (canonical13119 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA794 + difference 4 1) (sourceB794 + difference 1 4) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5191) := by
    have ha : (tripleCharges (sourceA794 + difference 4 1) (sourceB794 + difference 1 4) sourceC794) = raw13120 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13120; decide +kernel
    rw [ha]
    exact (canonical13120 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA794 + difference 4 2) (sourceB794 + difference 2 4) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5191) := by
    have ha : (tripleCharges (sourceA794 + difference 4 2) (sourceB794 + difference 2 4) sourceC794) = raw13121 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13121; decide +kernel
    rw [ha]
    exact (canonical13121 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA794 + difference 4 3) (sourceB794 + difference 3 4) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA794 + difference 4 3) (sourceB794 + difference 3 4) sourceC794) = raw13122 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13122; decide +kernel
    rw [ha]
    exact (canonical13122 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA794 + difference 4 5) (sourceB794 + difference 5 4) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5277) := by
    have ha : (tripleCharges (sourceA794 + difference 4 5) (sourceB794 + difference 5 4) sourceC794) = raw13123 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13123; decide +kernel
    rw [ha]
    exact (canonical13123 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA794 + difference 5 0) (sourceB794 + difference 0 5) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4582) := by
    have ha : (tripleCharges (sourceA794 + difference 5 0) (sourceB794 + difference 0 5) sourceC794) = raw13124 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13124; decide +kernel
    rw [ha]
    exact (canonical13124 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA794 + difference 5 1) (sourceB794 + difference 1 5) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5190) := by
    have ha : (tripleCharges (sourceA794 + difference 5 1) (sourceB794 + difference 1 5) sourceC794) = raw13125 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13125; decide +kernel
    rw [ha]
    exact (canonical13125 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA794 + difference 5 2) (sourceB794 + difference 2 5) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5190) := by
    have ha : (tripleCharges (sourceA794 + difference 5 2) (sourceB794 + difference 2 5) sourceC794) = raw13126 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13126; decide +kernel
    rw [ha]
    exact (canonical13126 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA794 + difference 5 3) (sourceB794 + difference 3 5) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA794 + difference 5 3) (sourceB794 + difference 3 5) sourceC794) = raw13127 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13127; decide +kernel
    rw [ha]
    exact (canonical13127 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA794 + difference 5 4) (sourceB794 + difference 4 5) sourceC794) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA794 + difference 5 4) (sourceB794 + difference 4 5) sourceC794) = raw13128 := by
      apply Matrix.ext; unfold tripleCharges sourceA794 sourceB794 sourceC794 difference raw13128; decide +kernel
    rw [ha]
    exact (canonical13128 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA794 sourceB794 sourceC794
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm794, Integer.Sparse.eval]
  linarith only [hs]

def sourceA795 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB795 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC795 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceForm795 : Integer.Sparse Master := [(Sum.inr 1197, 1), (Sum.inr 1198, 1), (Sum.inr 1201, 1), (Sum.inr 1233, 2), (Sum.inr 2851, 2), (Sum.inr 2852, 2), (Sum.inr 2854, 2), (Sum.inr 2878, 2), (Sum.inr 3058, 1), (Sum.inr 3059, 1), (Sum.inr 3064, 1), (Sum.inr 3065, 1), (Sum.inr 3074, 2), (Sum.inr 3075, 1), (Sum.inr 3078, 1), (Sum.inr 3087, 2), (Sum.inr 3099, 2), (Sum.inr 4024, 2), (Sum.inr 4025, 1), (Sum.inr 4029, 1), (Sum.inr 4033, 1)]

theorem sourceEq795 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm795 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA795 + difference 0 1) (sourceB795 + difference 1 0) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA795 + difference 0 1) (sourceB795 + difference 1 0) sourceC795) = raw13129 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13129; decide +kernel
    rw [ha]
    exact (canonical13129 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA795 + difference 0 2) (sourceB795 + difference 2 0) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA795 + difference 0 2) (sourceB795 + difference 2 0) sourceC795) = raw13130 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13130; decide +kernel
    rw [ha]
    exact (canonical13130 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA795 + difference 0 3) (sourceB795 + difference 3 0) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA795 + difference 0 3) (sourceB795 + difference 3 0) sourceC795) = raw13131 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13131; decide +kernel
    rw [ha]
    exact (canonical13131 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA795 + difference 0 4) (sourceB795 + difference 4 0) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA795 + difference 0 4) (sourceB795 + difference 4 0) sourceC795) = raw13132 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13132; decide +kernel
    rw [ha]
    exact (canonical13132 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA795 + difference 0 5) (sourceB795 + difference 5 0) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4025) := by
    have ha : (tripleCharges (sourceA795 + difference 0 5) (sourceB795 + difference 5 0) sourceC795) = raw13133 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13133; decide +kernel
    rw [ha]
    exact (canonical13133 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA795 + difference 1 0) (sourceB795 + difference 0 1) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA795 + difference 1 0) (sourceB795 + difference 0 1) sourceC795) = raw13134 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13134; decide +kernel
    rw [ha]
    exact (canonical13134 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA795 + difference 1 2) (sourceB795 + difference 2 1) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2878) := by
    have ha : (tripleCharges (sourceA795 + difference 1 2) (sourceB795 + difference 2 1) sourceC795) = raw13135 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13135; decide +kernel
    rw [ha]
    exact (canonical13135 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA795 + difference 1 3) (sourceB795 + difference 3 1) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA795 + difference 1 3) (sourceB795 + difference 3 1) sourceC795) = raw13136 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13136; decide +kernel
    rw [ha]
    exact (canonical13136 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA795 + difference 1 4) (sourceB795 + difference 4 1) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA795 + difference 1 4) (sourceB795 + difference 4 1) sourceC795) = raw13137 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13137; decide +kernel
    rw [ha]
    exact (canonical13137 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA795 + difference 1 5) (sourceB795 + difference 5 1) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA795 + difference 1 5) (sourceB795 + difference 5 1) sourceC795) = raw13138 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13138; decide +kernel
    rw [ha]
    exact (canonical13138 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA795 + difference 2 0) (sourceB795 + difference 0 2) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA795 + difference 2 0) (sourceB795 + difference 0 2) sourceC795) = raw13139 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13139; decide +kernel
    rw [ha]
    exact (canonical13139 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA795 + difference 2 1) (sourceB795 + difference 1 2) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2878) := by
    have ha : (tripleCharges (sourceA795 + difference 2 1) (sourceB795 + difference 1 2) sourceC795) = raw13140 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13140; decide +kernel
    rw [ha]
    exact (canonical13140 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA795 + difference 2 3) (sourceB795 + difference 3 2) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA795 + difference 2 3) (sourceB795 + difference 3 2) sourceC795) = raw13141 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13141; decide +kernel
    rw [ha]
    exact (canonical13141 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA795 + difference 2 4) (sourceB795 + difference 4 2) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA795 + difference 2 4) (sourceB795 + difference 4 2) sourceC795) = raw13142 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13142; decide +kernel
    rw [ha]
    exact (canonical13142 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA795 + difference 2 5) (sourceB795 + difference 5 2) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA795 + difference 2 5) (sourceB795 + difference 5 2) sourceC795) = raw13143 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13143; decide +kernel
    rw [ha]
    exact (canonical13143 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA795 + difference 3 0) (sourceB795 + difference 0 3) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1197) := by
    have ha : (tripleCharges (sourceA795 + difference 3 0) (sourceB795 + difference 0 3) sourceC795) = raw13144 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13144; decide +kernel
    rw [ha]
    exact (canonical13144 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA795 + difference 3 1) (sourceB795 + difference 1 3) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2851) := by
    have ha : (tripleCharges (sourceA795 + difference 3 1) (sourceB795 + difference 1 3) sourceC795) = raw13145 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13145; decide +kernel
    rw [ha]
    exact (canonical13145 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA795 + difference 3 2) (sourceB795 + difference 2 3) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2851) := by
    have ha : (tripleCharges (sourceA795 + difference 3 2) (sourceB795 + difference 2 3) sourceC795) = raw13146 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13146; decide +kernel
    rw [ha]
    exact (canonical13146 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA795 + difference 3 4) (sourceB795 + difference 4 3) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA795 + difference 3 4) (sourceB795 + difference 4 3) sourceC795) = raw13147 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13147; decide +kernel
    rw [ha]
    exact (canonical13147 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA795 + difference 3 5) (sourceB795 + difference 5 3) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3058) := by
    have ha : (tripleCharges (sourceA795 + difference 3 5) (sourceB795 + difference 5 3) sourceC795) = raw13148 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13148; decide +kernel
    rw [ha]
    exact (canonical13148 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA795 + difference 4 0) (sourceB795 + difference 0 4) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1198) := by
    have ha : (tripleCharges (sourceA795 + difference 4 0) (sourceB795 + difference 0 4) sourceC795) = raw13149 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13149; decide +kernel
    rw [ha]
    exact (canonical13149 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA795 + difference 4 1) (sourceB795 + difference 1 4) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2852) := by
    have ha : (tripleCharges (sourceA795 + difference 4 1) (sourceB795 + difference 1 4) sourceC795) = raw13150 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13150; decide +kernel
    rw [ha]
    exact (canonical13150 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA795 + difference 4 2) (sourceB795 + difference 2 4) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2852) := by
    have ha : (tripleCharges (sourceA795 + difference 4 2) (sourceB795 + difference 2 4) sourceC795) = raw13151 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13151; decide +kernel
    rw [ha]
    exact (canonical13151 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA795 + difference 4 3) (sourceB795 + difference 3 4) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA795 + difference 4 3) (sourceB795 + difference 3 4) sourceC795) = raw13152 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13152; decide +kernel
    rw [ha]
    exact (canonical13152 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA795 + difference 4 5) (sourceB795 + difference 5 4) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3059) := by
    have ha : (tripleCharges (sourceA795 + difference 4 5) (sourceB795 + difference 5 4) sourceC795) = raw13153 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13153; decide +kernel
    rw [ha]
    exact (canonical13153 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA795 + difference 5 0) (sourceB795 + difference 0 5) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1201) := by
    have ha : (tripleCharges (sourceA795 + difference 5 0) (sourceB795 + difference 0 5) sourceC795) = raw13154 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13154; decide +kernel
    rw [ha]
    exact (canonical13154 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA795 + difference 5 1) (sourceB795 + difference 1 5) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2854) := by
    have ha : (tripleCharges (sourceA795 + difference 5 1) (sourceB795 + difference 1 5) sourceC795) = raw13155 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13155; decide +kernel
    rw [ha]
    exact (canonical13155 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA795 + difference 5 2) (sourceB795 + difference 2 5) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2854) := by
    have ha : (tripleCharges (sourceA795 + difference 5 2) (sourceB795 + difference 2 5) sourceC795) = raw13156 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13156; decide +kernel
    rw [ha]
    exact (canonical13156 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA795 + difference 5 3) (sourceB795 + difference 3 5) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA795 + difference 5 3) (sourceB795 + difference 3 5) sourceC795) = raw13157 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13157; decide +kernel
    rw [ha]
    exact (canonical13157 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA795 + difference 5 4) (sourceB795 + difference 4 5) sourceC795) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA795 + difference 5 4) (sourceB795 + difference 4 5) sourceC795) = raw13158 := by
      apply Matrix.ext; unfold tripleCharges sourceA795 sourceB795 sourceC795 difference raw13158; decide +kernel
    rw [ha]
    exact (canonical13158 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA795 sourceB795 sourceC795
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm795, Integer.Sparse.eval]
  linarith only [hs]

def sourceA796 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB796 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC796 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceForm796 : Integer.Sparse Master := [(Sum.inr 2457, 1), (Sum.inr 2460, 2), (Sum.inr 2507, 1), (Sum.inr 2738, 1), (Sum.inr 3278, 1), (Sum.inr 3282, 1), (Sum.inr 3289, 2), (Sum.inr 3531, 1), (Sum.inr 3532, 2), (Sum.inr 3539, 1), (Sum.inr 3568, 2), (Sum.inr 3569, 2), (Sum.inr 3571, 2), (Sum.inr 3574, 2), (Sum.inr 3576, 1), (Sum.inr 3580, 1), (Sum.inr 3581, 2), (Sum.inr 3851, 1), (Sum.inr 3880, 2), (Sum.inr 3882, 1), (Sum.inr 3887, 1)]

theorem sourceEq796 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm796 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA796 + difference 0 1) (sourceB796 + difference 1 0) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA796 + difference 0 1) (sourceB796 + difference 1 0) sourceC796) = raw13159 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13159; decide +kernel
    rw [ha]
    exact (canonical13159 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA796 + difference 0 2) (sourceB796 + difference 2 0) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA796 + difference 0 2) (sourceB796 + difference 2 0) sourceC796) = raw13160 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13160; decide +kernel
    rw [ha]
    exact (canonical13160 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA796 + difference 0 3) (sourceB796 + difference 3 0) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA796 + difference 0 3) (sourceB796 + difference 3 0) sourceC796) = raw13161 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13161; decide +kernel
    rw [ha]
    exact (canonical13161 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA796 + difference 0 4) (sourceB796 + difference 4 0) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA796 + difference 0 4) (sourceB796 + difference 4 0) sourceC796) = raw13162 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13162; decide +kernel
    rw [ha]
    exact (canonical13162 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA796 + difference 0 5) (sourceB796 + difference 5 0) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3882) := by
    have ha : (tripleCharges (sourceA796 + difference 0 5) (sourceB796 + difference 5 0) sourceC796) = raw13163 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13163; decide +kernel
    rw [ha]
    exact (canonical13163 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA796 + difference 1 0) (sourceB796 + difference 0 1) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA796 + difference 1 0) (sourceB796 + difference 0 1) sourceC796) = raw13164 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13164; decide +kernel
    rw [ha]
    exact (canonical13164 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA796 + difference 1 2) (sourceB796 + difference 2 1) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3569) := by
    have ha : (tripleCharges (sourceA796 + difference 1 2) (sourceB796 + difference 2 1) sourceC796) = raw13165 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13165; decide +kernel
    rw [ha]
    exact (canonical13165 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA796 + difference 1 3) (sourceB796 + difference 3 1) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA796 + difference 1 3) (sourceB796 + difference 3 1) sourceC796) = raw13166 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13166; decide +kernel
    rw [ha]
    exact (canonical13166 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA796 + difference 1 4) (sourceB796 + difference 4 1) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA796 + difference 1 4) (sourceB796 + difference 4 1) sourceC796) = raw13167 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13167; decide +kernel
    rw [ha]
    exact (canonical13167 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA796 + difference 1 5) (sourceB796 + difference 5 1) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA796 + difference 1 5) (sourceB796 + difference 5 1) sourceC796) = raw13168 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13168; decide +kernel
    rw [ha]
    exact (canonical13168 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA796 + difference 2 0) (sourceB796 + difference 0 2) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA796 + difference 2 0) (sourceB796 + difference 0 2) sourceC796) = raw13169 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13169; decide +kernel
    rw [ha]
    exact (canonical13169 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA796 + difference 2 1) (sourceB796 + difference 1 2) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3569) := by
    have ha : (tripleCharges (sourceA796 + difference 2 1) (sourceB796 + difference 1 2) sourceC796) = raw13170 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13170; decide +kernel
    rw [ha]
    exact (canonical13170 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA796 + difference 2 3) (sourceB796 + difference 3 2) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA796 + difference 2 3) (sourceB796 + difference 3 2) sourceC796) = raw13171 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13171; decide +kernel
    rw [ha]
    exact (canonical13171 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA796 + difference 2 4) (sourceB796 + difference 4 2) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA796 + difference 2 4) (sourceB796 + difference 4 2) sourceC796) = raw13172 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13172; decide +kernel
    rw [ha]
    exact (canonical13172 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA796 + difference 2 5) (sourceB796 + difference 5 2) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA796 + difference 2 5) (sourceB796 + difference 5 2) sourceC796) = raw13173 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13173; decide +kernel
    rw [ha]
    exact (canonical13173 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA796 + difference 3 0) (sourceB796 + difference 0 3) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2457) := by
    have ha : (tripleCharges (sourceA796 + difference 3 0) (sourceB796 + difference 0 3) sourceC796) = raw13174 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13174; decide +kernel
    rw [ha]
    exact (canonical13174 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA796 + difference 3 1) (sourceB796 + difference 1 3) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2460) := by
    have ha : (tripleCharges (sourceA796 + difference 3 1) (sourceB796 + difference 1 3) sourceC796) = raw13175 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13175; decide +kernel
    rw [ha]
    exact (canonical13175 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA796 + difference 3 2) (sourceB796 + difference 2 3) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2460) := by
    have ha : (tripleCharges (sourceA796 + difference 3 2) (sourceB796 + difference 2 3) sourceC796) = raw13176 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13176; decide +kernel
    rw [ha]
    exact (canonical13176 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA796 + difference 3 4) (sourceB796 + difference 4 3) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA796 + difference 3 4) (sourceB796 + difference 4 3) sourceC796) = raw13177 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13177; decide +kernel
    rw [ha]
    exact (canonical13177 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA796 + difference 3 5) (sourceB796 + difference 5 3) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2507) := by
    have ha : (tripleCharges (sourceA796 + difference 3 5) (sourceB796 + difference 5 3) sourceC796) = raw13178 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13178; decide +kernel
    rw [ha]
    exact (canonical13178 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA796 + difference 4 0) (sourceB796 + difference 0 4) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3278) := by
    have ha : (tripleCharges (sourceA796 + difference 4 0) (sourceB796 + difference 0 4) sourceC796) = raw13179 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13179; decide +kernel
    rw [ha]
    exact (canonical13179 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA796 + difference 4 1) (sourceB796 + difference 1 4) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3574) := by
    have ha : (tripleCharges (sourceA796 + difference 4 1) (sourceB796 + difference 1 4) sourceC796) = raw13180 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13180; decide +kernel
    rw [ha]
    exact (canonical13180 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA796 + difference 4 2) (sourceB796 + difference 2 4) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3574) := by
    have ha : (tripleCharges (sourceA796 + difference 4 2) (sourceB796 + difference 2 4) sourceC796) = raw13181 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13181; decide +kernel
    rw [ha]
    exact (canonical13181 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA796 + difference 4 3) (sourceB796 + difference 3 4) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA796 + difference 4 3) (sourceB796 + difference 3 4) sourceC796) = raw13182 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13182; decide +kernel
    rw [ha]
    exact (canonical13182 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA796 + difference 4 5) (sourceB796 + difference 5 4) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3576) := by
    have ha : (tripleCharges (sourceA796 + difference 4 5) (sourceB796 + difference 5 4) sourceC796) = raw13183 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13183; decide +kernel
    rw [ha]
    exact (canonical13183 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA796 + difference 5 0) (sourceB796 + difference 0 5) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3282) := by
    have ha : (tripleCharges (sourceA796 + difference 5 0) (sourceB796 + difference 0 5) sourceC796) = raw13184 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13184; decide +kernel
    rw [ha]
    exact (canonical13184 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA796 + difference 5 1) (sourceB796 + difference 1 5) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3568) := by
    have ha : (tripleCharges (sourceA796 + difference 5 1) (sourceB796 + difference 1 5) sourceC796) = raw13185 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13185; decide +kernel
    rw [ha]
    exact (canonical13185 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA796 + difference 5 2) (sourceB796 + difference 2 5) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3568) := by
    have ha : (tripleCharges (sourceA796 + difference 5 2) (sourceB796 + difference 2 5) sourceC796) = raw13186 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13186; decide +kernel
    rw [ha]
    exact (canonical13186 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA796 + difference 5 3) (sourceB796 + difference 3 5) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA796 + difference 5 3) (sourceB796 + difference 3 5) sourceC796) = raw13187 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13187; decide +kernel
    rw [ha]
    exact (canonical13187 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA796 + difference 5 4) (sourceB796 + difference 4 5) sourceC796) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA796 + difference 5 4) (sourceB796 + difference 4 5) sourceC796) = raw13188 := by
      apply Matrix.ext; unfold tripleCharges sourceA796 sourceB796 sourceC796 difference raw13188; decide +kernel
    rw [ha]
    exact (canonical13188 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA796 sourceB796 sourceC796
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm796, Integer.Sparse.eval]
  linarith only [hs]

def sourceA797 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB797 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC797 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceForm797 : Integer.Sparse Master := [(Sum.inr 2750, 1), (Sum.inr 3880, 2), (Sum.inr 3901, 1), (Sum.inr 3909, 1), (Sum.inr 3910, 1), (Sum.inr 4091, -1)]

theorem sourceEq797 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm797 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA797 + difference 0 0) (sourceB797 + difference 0 0) sourceC797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA797 + difference 0 0) (sourceB797 + difference 0 0) sourceC797) = raw13189 := by
      apply Matrix.ext; unfold tripleCharges sourceA797 sourceB797 sourceC797 difference raw13189; decide +kernel
    rw [ha]
    exact (canonical13189 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA797 + difference 0 1) (sourceB797 + difference 1 0) sourceC797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA797 + difference 0 1) (sourceB797 + difference 1 0) sourceC797) = raw13190 := by
      apply Matrix.ext; unfold tripleCharges sourceA797 sourceB797 sourceC797 difference raw13190; decide +kernel
    rw [ha]
    exact (canonical13190 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA797 + difference 0 2) (sourceB797 + difference 2 0) sourceC797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA797 + difference 0 2) (sourceB797 + difference 2 0) sourceC797) = raw13191 := by
      apply Matrix.ext; unfold tripleCharges sourceA797 sourceB797 sourceC797 difference raw13191; decide +kernel
    rw [ha]
    exact (canonical13191 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA797 + difference 0 3) (sourceB797 + difference 3 0) sourceC797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3901) := by
    have ha : (tripleCharges (sourceA797 + difference 0 3) (sourceB797 + difference 3 0) sourceC797) = raw13192 := by
      apply Matrix.ext; unfold tripleCharges sourceA797 sourceB797 sourceC797 difference raw13192; decide +kernel
    rw [ha]
    exact (canonical13192 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA797 + difference 0 4) (sourceB797 + difference 4 0) sourceC797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA797 + difference 0 4) (sourceB797 + difference 4 0) sourceC797) = raw13193 := by
      apply Matrix.ext; unfold tripleCharges sourceA797 sourceB797 sourceC797 difference raw13193; decide +kernel
    rw [ha]
    exact (canonical13193 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA797 + difference 0 5) (sourceB797 + difference 5 0) sourceC797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA797 + difference 0 5) (sourceB797 + difference 5 0) sourceC797) = raw13194 := by
      apply Matrix.ext; unfold tripleCharges sourceA797 sourceB797 sourceC797 difference raw13194; decide +kernel
    rw [ha]
    exact (canonical13194 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA797 + sourceB797) sourceC797) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA797 + sourceB797) sourceC797) = raw13195 := by
      apply Matrix.ext; unfold doubleCharges sourceA797 sourceB797 sourceC797 raw13195; decide +kernel
    rw [ha]
    exact (canonical13195 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA797 sourceB797 sourceC797
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm797, Integer.Sparse.eval]
  linarith only [hs]

def sourceA798 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB798 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC798 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceForm798 : Integer.Sparse Master := [(Sum.inr 1247, 1), (Sum.inr 1248, 1), (Sum.inr 1250, 1), (Sum.inr 1260, 2), (Sum.inr 2750, 1), (Sum.inr 4091, -1)]

theorem sourceEq798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm798 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA798 + difference 0 0) (sourceB798 + difference 0 0) sourceC798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA798 + difference 0 0) (sourceB798 + difference 0 0) sourceC798) = raw13189 := by
      apply Matrix.ext; unfold tripleCharges sourceA798 sourceB798 sourceC798 difference raw13189; decide +kernel
    rw [ha]
    exact (canonical13189 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA798 + difference 1 0) (sourceB798 + difference 0 1) sourceC798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA798 + difference 1 0) (sourceB798 + difference 0 1) sourceC798) = raw13196 := by
      apply Matrix.ext; unfold tripleCharges sourceA798 sourceB798 sourceC798 difference raw13196; decide +kernel
    rw [ha]
    exact (canonical13196 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA798 + difference 2 0) (sourceB798 + difference 0 2) sourceC798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA798 + difference 2 0) (sourceB798 + difference 0 2) sourceC798) = raw13197 := by
      apply Matrix.ext; unfold tripleCharges sourceA798 sourceB798 sourceC798 difference raw13197; decide +kernel
    rw [ha]
    exact (canonical13197 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA798 + difference 3 0) (sourceB798 + difference 0 3) sourceC798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1250) := by
    have ha : (tripleCharges (sourceA798 + difference 3 0) (sourceB798 + difference 0 3) sourceC798) = raw13198 := by
      apply Matrix.ext; unfold tripleCharges sourceA798 sourceB798 sourceC798 difference raw13198; decide +kernel
    rw [ha]
    exact (canonical13198 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA798 + difference 4 0) (sourceB798 + difference 0 4) sourceC798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1248) := by
    have ha : (tripleCharges (sourceA798 + difference 4 0) (sourceB798 + difference 0 4) sourceC798) = raw13199 := by
      apply Matrix.ext; unfold tripleCharges sourceA798 sourceB798 sourceC798 difference raw13199; decide +kernel
    rw [ha]
    exact (canonical13199 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA798 + difference 5 0) (sourceB798 + difference 0 5) sourceC798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1247) := by
    have ha : (tripleCharges (sourceA798 + difference 5 0) (sourceB798 + difference 0 5) sourceC798) = raw13200 := by
      apply Matrix.ext; unfold tripleCharges sourceA798 sourceB798 sourceC798 difference raw13200; decide +kernel
    rw [ha]
    exact (canonical13200 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA798 + sourceB798) sourceC798) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA798 + sourceB798) sourceC798) = raw13195 := by
      apply Matrix.ext; unfold doubleCharges sourceA798 sourceB798 sourceC798 raw13195; decide +kernel
    rw [ha]
    exact (canonical13195 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA798 sourceB798 sourceC798
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm798, Integer.Sparse.eval]
  linarith only [hs]

def sourceA799 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB799 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC799 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceForm799 : Integer.Sparse Master := [(Sum.inr 1260, 1), (Sum.inr 2631, 1), (Sum.inr 2721, 1), (Sum.inr 2750, 2), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

theorem sourceEq799 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm799 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA799 + difference 1 0) (sourceB799 + difference 0 1) sourceC799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA799 + difference 1 0) (sourceB799 + difference 0 1) sourceC799) = raw13196 := by
      apply Matrix.ext; unfold tripleCharges sourceA799 sourceB799 sourceC799 difference raw13196; decide +kernel
    rw [ha]
    exact (canonical13196 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA799 + difference 1 1) (sourceB799 + difference 1 1) sourceC799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA799 + difference 1 1) (sourceB799 + difference 1 1) sourceC799) = raw13189 := by
      apply Matrix.ext; unfold tripleCharges sourceA799 sourceB799 sourceC799 difference raw13189; decide +kernel
    rw [ha]
    exact (canonical13189 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA799 + difference 1 2) (sourceB799 + difference 2 1) sourceC799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2631) := by
    have ha : (tripleCharges (sourceA799 + difference 1 2) (sourceB799 + difference 2 1) sourceC799) = raw13201 := by
      apply Matrix.ext; unfold tripleCharges sourceA799 sourceB799 sourceC799 difference raw13201; decide +kernel
    rw [ha]
    exact (canonical13201 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA799 + difference 1 3) (sourceB799 + difference 3 1) sourceC799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA799 + difference 1 3) (sourceB799 + difference 3 1) sourceC799) = raw13202 := by
      apply Matrix.ext; unfold tripleCharges sourceA799 sourceB799 sourceC799 difference raw13202; decide +kernel
    rw [ha]
    exact (canonical13202 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA799 + difference 1 4) (sourceB799 + difference 4 1) sourceC799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA799 + difference 1 4) (sourceB799 + difference 4 1) sourceC799) = raw13203 := by
      apply Matrix.ext; unfold tripleCharges sourceA799 sourceB799 sourceC799 difference raw13203; decide +kernel
    rw [ha]
    exact (canonical13203 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA799 + difference 1 5) (sourceB799 + difference 5 1) sourceC799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA799 + difference 1 5) (sourceB799 + difference 5 1) sourceC799) = raw13204 := by
      apply Matrix.ext; unfold tripleCharges sourceA799 sourceB799 sourceC799 difference raw13204; decide +kernel
    rw [ha]
    exact (canonical13204 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA799 + sourceB799) sourceC799) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA799 + sourceB799) sourceC799) = raw13195 := by
      apply Matrix.ext; unfold doubleCharges sourceA799 sourceB799 sourceC799 raw13195; decide +kernel
    rw [ha]
    exact (canonical13195 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA799 sourceB799 sourceC799
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm799, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
