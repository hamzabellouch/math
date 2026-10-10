import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA576 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB576 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC576 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm576 : Integer.Sparse Master := [(Sum.inr 2724, 2), (Sum.inr 2743, 1), (Sum.inr 2744, 1), (Sum.inr 2788, 1), (Sum.inr 2964, 2), (Sum.inr 2966, 1), (Sum.inr 2967, 1), (Sum.inr 3040, 2), (Sum.inr 3055, 1), (Sum.inr 3056, 1), (Sum.inr 3066, 2), (Sum.inr 3078, 2), (Sum.inr 3079, 2), (Sum.inr 3089, 2), (Sum.inr 3102, 1), (Sum.inr 3103, 2), (Sum.inr 3124, 1), (Sum.inr 3125, 1), (Sum.inr 3185, 2), (Sum.inr 3187, 1), (Sum.inr 3230, 1)]

theorem sourceEq576 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm576 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA576 + difference 0 1) (sourceB576 + difference 1 0) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA576 + difference 0 1) (sourceB576 + difference 1 0) sourceC576) = raw9700 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9700; decide +kernel
    rw [ha]
    exact (canonical9700 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA576 + difference 0 2) (sourceB576 + difference 2 0) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA576 + difference 0 2) (sourceB576 + difference 2 0) sourceC576) = raw9701 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9701; decide +kernel
    rw [ha]
    exact (canonical9701 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA576 + difference 0 3) (sourceB576 + difference 3 0) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA576 + difference 0 3) (sourceB576 + difference 3 0) sourceC576) = raw9702 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9702; decide +kernel
    rw [ha]
    exact (canonical9702 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA576 + difference 0 4) (sourceB576 + difference 4 0) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA576 + difference 0 4) (sourceB576 + difference 4 0) sourceC576) = raw9703 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9703; decide +kernel
    rw [ha]
    exact (canonical9703 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA576 + difference 0 5) (sourceB576 + difference 5 0) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA576 + difference 0 5) (sourceB576 + difference 5 0) sourceC576) = raw9704 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9704; decide +kernel
    rw [ha]
    exact (canonical9704 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA576 + difference 1 0) (sourceB576 + difference 0 1) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3187) := by
    have ha : (tripleCharges (sourceA576 + difference 1 0) (sourceB576 + difference 0 1) sourceC576) = raw9705 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9705; decide +kernel
    rw [ha]
    exact (canonical9705 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA576 + difference 1 2) (sourceB576 + difference 2 1) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3040) := by
    have ha : (tripleCharges (sourceA576 + difference 1 2) (sourceB576 + difference 2 1) sourceC576) = raw9706 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9706; decide +kernel
    rw [ha]
    exact (canonical9706 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA576 + difference 1 3) (sourceB576 + difference 3 1) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3040) := by
    have ha : (tripleCharges (sourceA576 + difference 1 3) (sourceB576 + difference 3 1) sourceC576) = raw9707 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9707; decide +kernel
    rw [ha]
    exact (canonical9707 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA576 + difference 1 4) (sourceB576 + difference 4 1) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3056) := by
    have ha : (tripleCharges (sourceA576 + difference 1 4) (sourceB576 + difference 4 1) sourceC576) = raw9708 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9708; decide +kernel
    rw [ha]
    exact (canonical9708 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA576 + difference 1 5) (sourceB576 + difference 5 1) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA576 + difference 1 5) (sourceB576 + difference 5 1) sourceC576) = raw9709 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9709; decide +kernel
    rw [ha]
    exact (canonical9709 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA576 + difference 2 0) (sourceB576 + difference 0 2) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3185) := by
    have ha : (tripleCharges (sourceA576 + difference 2 0) (sourceB576 + difference 0 2) sourceC576) = raw9710 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9710; decide +kernel
    rw [ha]
    exact (canonical9710 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA576 + difference 2 1) (sourceB576 + difference 1 2) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA576 + difference 2 1) (sourceB576 + difference 1 2) sourceC576) = raw9072 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9072; decide +kernel
    rw [ha]
    exact (canonical9072 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA576 + difference 2 3) (sourceB576 + difference 3 2) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3066) := by
    have ha : (tripleCharges (sourceA576 + difference 2 3) (sourceB576 + difference 3 2) sourceC576) = raw9711 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9711; decide +kernel
    rw [ha]
    exact (canonical9711 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA576 + difference 2 4) (sourceB576 + difference 4 2) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3079) := by
    have ha : (tripleCharges (sourceA576 + difference 2 4) (sourceB576 + difference 4 2) sourceC576) = raw9712 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9712; decide +kernel
    rw [ha]
    exact (canonical9712 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA576 + difference 2 5) (sourceB576 + difference 5 2) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA576 + difference 2 5) (sourceB576 + difference 5 2) sourceC576) = raw9065 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9065; decide +kernel
    rw [ha]
    exact (canonical9065 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA576 + difference 3 0) (sourceB576 + difference 0 3) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3185) := by
    have ha : (tripleCharges (sourceA576 + difference 3 0) (sourceB576 + difference 0 3) sourceC576) = raw9713 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9713; decide +kernel
    rw [ha]
    exact (canonical9713 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA576 + difference 3 1) (sourceB576 + difference 1 3) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA576 + difference 3 1) (sourceB576 + difference 1 3) sourceC576) = raw7956 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw7956; decide +kernel
    rw [ha]
    exact (canonical7956 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA576 + difference 3 2) (sourceB576 + difference 2 3) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3066) := by
    have ha : (tripleCharges (sourceA576 + difference 3 2) (sourceB576 + difference 2 3) sourceC576) = raw9714 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9714; decide +kernel
    rw [ha]
    exact (canonical9714 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA576 + difference 3 4) (sourceB576 + difference 4 3) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3079) := by
    have ha : (tripleCharges (sourceA576 + difference 3 4) (sourceB576 + difference 4 3) sourceC576) = raw9715 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9715; decide +kernel
    rw [ha]
    exact (canonical9715 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA576 + difference 3 5) (sourceB576 + difference 5 3) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA576 + difference 3 5) (sourceB576 + difference 5 3) sourceC576) = raw7950 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw7950; decide +kernel
    rw [ha]
    exact (canonical7950 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA576 + difference 4 0) (sourceB576 + difference 0 4) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA576 + difference 4 0) (sourceB576 + difference 0 4) sourceC576) = raw9716 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9716; decide +kernel
    rw [ha]
    exact (canonical9716 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA576 + difference 4 1) (sourceB576 + difference 1 4) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA576 + difference 4 1) (sourceB576 + difference 1 4) sourceC576) = raw7955 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw7955; decide +kernel
    rw [ha]
    exact (canonical7955 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA576 + difference 4 2) (sourceB576 + difference 2 4) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA576 + difference 4 2) (sourceB576 + difference 2 4) sourceC576) = raw9717 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9717; decide +kernel
    rw [ha]
    exact (canonical9717 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA576 + difference 4 3) (sourceB576 + difference 3 4) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA576 + difference 4 3) (sourceB576 + difference 3 4) sourceC576) = raw9718 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9718; decide +kernel
    rw [ha]
    exact (canonical9718 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA576 + difference 4 5) (sourceB576 + difference 5 4) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA576 + difference 4 5) (sourceB576 + difference 5 4) sourceC576) = raw7949 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw7949; decide +kernel
    rw [ha]
    exact (canonical7949 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA576 + difference 5 0) (sourceB576 + difference 0 5) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2966) := by
    have ha : (tripleCharges (sourceA576 + difference 5 0) (sourceB576 + difference 0 5) sourceC576) = raw9719 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9719; decide +kernel
    rw [ha]
    exact (canonical9719 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA576 + difference 5 1) (sourceB576 + difference 1 5) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3125) := by
    have ha : (tripleCharges (sourceA576 + difference 5 1) (sourceB576 + difference 1 5) sourceC576) = raw9720 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9720; decide +kernel
    rw [ha]
    exact (canonical9720 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA576 + difference 5 2) (sourceB576 + difference 2 5) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA576 + difference 5 2) (sourceB576 + difference 2 5) sourceC576) = raw9721 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9721; decide +kernel
    rw [ha]
    exact (canonical9721 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA576 + difference 5 3) (sourceB576 + difference 3 5) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA576 + difference 5 3) (sourceB576 + difference 3 5) sourceC576) = raw9722 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9722; decide +kernel
    rw [ha]
    exact (canonical9722 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA576 + difference 5 4) (sourceB576 + difference 4 5) sourceC576) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA576 + difference 5 4) (sourceB576 + difference 4 5) sourceC576) = raw9723 := by
      apply Matrix.ext; unfold tripleCharges sourceA576 sourceB576 sourceC576 difference raw9723; decide +kernel
    rw [ha]
    exact (canonical9723 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA576 sourceB576 sourceC576
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm576, Integer.Sparse.eval]
  linarith only [hs]

def sourceA577 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB577 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC577 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm577 : Integer.Sparse Master := [(Sum.inr 2106, 2), (Sum.inr 2109, 1), (Sum.inr 2115, 1), (Sum.inr 2264, 1), (Sum.inr 3582, 1), (Sum.inr 4084, -1)]

theorem sourceEq577 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm577 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA577 + difference 0 0) (sourceB577 + difference 0 0) sourceC577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA577 + difference 0 0) (sourceB577 + difference 0 0) sourceC577) = raw9724 := by
      apply Matrix.ext; unfold tripleCharges sourceA577 sourceB577 sourceC577 difference raw9724; decide +kernel
    rw [ha]
    exact (canonical9724 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA577 + difference 1 0) (sourceB577 + difference 0 1) sourceC577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA577 + difference 1 0) (sourceB577 + difference 0 1) sourceC577) = raw9725 := by
      apply Matrix.ext; unfold tripleCharges sourceA577 sourceB577 sourceC577 difference raw9725; decide +kernel
    rw [ha]
    exact (canonical9725 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA577 + difference 2 0) (sourceB577 + difference 0 2) sourceC577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA577 + difference 2 0) (sourceB577 + difference 0 2) sourceC577) = raw9726 := by
      apply Matrix.ext; unfold tripleCharges sourceA577 sourceB577 sourceC577 difference raw9726; decide +kernel
    rw [ha]
    exact (canonical9726 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA577 + difference 3 0) (sourceB577 + difference 0 3) sourceC577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA577 + difference 3 0) (sourceB577 + difference 0 3) sourceC577) = raw9727 := by
      apply Matrix.ext; unfold tripleCharges sourceA577 sourceB577 sourceC577 difference raw9727; decide +kernel
    rw [ha]
    exact (canonical9727 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA577 + difference 4 0) (sourceB577 + difference 0 4) sourceC577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA577 + difference 4 0) (sourceB577 + difference 0 4) sourceC577) = raw9728 := by
      apply Matrix.ext; unfold tripleCharges sourceA577 sourceB577 sourceC577 difference raw9728; decide +kernel
    rw [ha]
    exact (canonical9728 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA577 + difference 5 0) (sourceB577 + difference 0 5) sourceC577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA577 + difference 5 0) (sourceB577 + difference 0 5) sourceC577) = raw9729 := by
      apply Matrix.ext; unfold tripleCharges sourceA577 sourceB577 sourceC577 difference raw9729; decide +kernel
    rw [ha]
    exact (canonical9729 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA577 + sourceB577) sourceC577) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA577 + sourceB577) sourceC577) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA577 sourceB577 sourceC577 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA577 sourceB577 sourceC577
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm577, Integer.Sparse.eval]
  linarith only [hs]

def sourceA578 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB578 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC578 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceForm578 : Integer.Sparse Master := [(Sum.inr 4590, 1), (Sum.inr 4591, 1), (Sum.inr 4593, 1), (Sum.inr 4603, 1), (Sum.inr 4606, 1), (Sum.inr 5073, 1), (Sum.inr 5078, 1), (Sum.inr 5081, 1), (Sum.inr 5104, 1), (Sum.inr 5128, 1), (Sum.inr 5130, 1), (Sum.inr 5137, 1), (Sum.inr 5139, 1), (Sum.inr 5145, 1), (Sum.inr 5185, 1), (Sum.inr 5189, 1), (Sum.inr 5199, 1), (Sum.inr 5250, 1), (Sum.inr 5252, 1), (Sum.inr 5257, 1), (Sum.inr 5259, 2), (Sum.inr 5273, 1), (Sum.inr 5282, 1), (Sum.inr 5290, 1), (Sum.inr 5410, 1), (Sum.inr 5424, 1), (Sum.inr 5438, 1), (Sum.inr 5439, 1), (Sum.inr 5440, 1)]

theorem sourceEq578 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm578 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA578 + difference 0 1) (sourceB578 + difference 1 0) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA578 + difference 0 1) (sourceB578 + difference 1 0) sourceC578) = raw9730 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9730; decide +kernel
    rw [ha]
    exact (canonical9730 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA578 + difference 0 2) (sourceB578 + difference 2 0) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA578 + difference 0 2) (sourceB578 + difference 2 0) sourceC578) = raw9731 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9731; decide +kernel
    rw [ha]
    exact (canonical9731 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA578 + difference 0 3) (sourceB578 + difference 3 0) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA578 + difference 0 3) (sourceB578 + difference 3 0) sourceC578) = raw9732 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9732; decide +kernel
    rw [ha]
    exact (canonical9732 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA578 + difference 0 4) (sourceB578 + difference 4 0) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA578 + difference 0 4) (sourceB578 + difference 4 0) sourceC578) = raw9733 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9733; decide +kernel
    rw [ha]
    exact (canonical9733 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA578 + difference 0 5) (sourceB578 + difference 5 0) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA578 + difference 0 5) (sourceB578 + difference 5 0) sourceC578) = raw9734 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9734; decide +kernel
    rw [ha]
    exact (canonical9734 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA578 + difference 1 0) (sourceB578 + difference 0 1) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA578 + difference 1 0) (sourceB578 + difference 0 1) sourceC578) = raw9735 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9735; decide +kernel
    rw [ha]
    exact (canonical9735 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA578 + difference 1 2) (sourceB578 + difference 2 1) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA578 + difference 1 2) (sourceB578 + difference 2 1) sourceC578) = raw9736 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9736; decide +kernel
    rw [ha]
    exact (canonical9736 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA578 + difference 1 3) (sourceB578 + difference 3 1) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA578 + difference 1 3) (sourceB578 + difference 3 1) sourceC578) = raw9737 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9737; decide +kernel
    rw [ha]
    exact (canonical9737 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA578 + difference 1 4) (sourceB578 + difference 4 1) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA578 + difference 1 4) (sourceB578 + difference 4 1) sourceC578) = raw9738 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9738; decide +kernel
    rw [ha]
    exact (canonical9738 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA578 + difference 1 5) (sourceB578 + difference 5 1) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA578 + difference 1 5) (sourceB578 + difference 5 1) sourceC578) = raw9739 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9739; decide +kernel
    rw [ha]
    exact (canonical9739 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA578 + difference 2 0) (sourceB578 + difference 0 2) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA578 + difference 2 0) (sourceB578 + difference 0 2) sourceC578) = raw9740 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9740; decide +kernel
    rw [ha]
    exact (canonical9740 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA578 + difference 2 1) (sourceB578 + difference 1 2) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA578 + difference 2 1) (sourceB578 + difference 1 2) sourceC578) = raw9741 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9741; decide +kernel
    rw [ha]
    exact (canonical9741 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA578 + difference 2 3) (sourceB578 + difference 3 2) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA578 + difference 2 3) (sourceB578 + difference 3 2) sourceC578) = raw9742 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9742; decide +kernel
    rw [ha]
    exact (canonical9742 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA578 + difference 2 4) (sourceB578 + difference 4 2) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA578 + difference 2 4) (sourceB578 + difference 4 2) sourceC578) = raw9743 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9743; decide +kernel
    rw [ha]
    exact (canonical9743 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA578 + difference 2 5) (sourceB578 + difference 5 2) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA578 + difference 2 5) (sourceB578 + difference 5 2) sourceC578) = raw9744 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9744; decide +kernel
    rw [ha]
    exact (canonical9744 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA578 + difference 3 0) (sourceB578 + difference 0 3) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA578 + difference 3 0) (sourceB578 + difference 0 3) sourceC578) = raw9745 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9745; decide +kernel
    rw [ha]
    exact (canonical9745 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA578 + difference 3 1) (sourceB578 + difference 1 3) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA578 + difference 3 1) (sourceB578 + difference 1 3) sourceC578) = raw9746 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9746; decide +kernel
    rw [ha]
    exact (canonical9746 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA578 + difference 3 2) (sourceB578 + difference 2 3) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA578 + difference 3 2) (sourceB578 + difference 2 3) sourceC578) = raw9747 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9747; decide +kernel
    rw [ha]
    exact (canonical9747 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA578 + difference 3 4) (sourceB578 + difference 4 3) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA578 + difference 3 4) (sourceB578 + difference 4 3) sourceC578) = raw9748 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9748; decide +kernel
    rw [ha]
    exact (canonical9748 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA578 + difference 3 5) (sourceB578 + difference 5 3) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA578 + difference 3 5) (sourceB578 + difference 5 3) sourceC578) = raw9749 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9749; decide +kernel
    rw [ha]
    exact (canonical9749 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA578 + difference 4 0) (sourceB578 + difference 0 4) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA578 + difference 4 0) (sourceB578 + difference 0 4) sourceC578) = raw9750 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9750; decide +kernel
    rw [ha]
    exact (canonical9750 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA578 + difference 4 1) (sourceB578 + difference 1 4) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA578 + difference 4 1) (sourceB578 + difference 1 4) sourceC578) = raw9751 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9751; decide +kernel
    rw [ha]
    exact (canonical9751 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA578 + difference 4 2) (sourceB578 + difference 2 4) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA578 + difference 4 2) (sourceB578 + difference 2 4) sourceC578) = raw9752 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9752; decide +kernel
    rw [ha]
    exact (canonical9752 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA578 + difference 4 3) (sourceB578 + difference 3 4) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA578 + difference 4 3) (sourceB578 + difference 3 4) sourceC578) = raw9753 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9753; decide +kernel
    rw [ha]
    exact (canonical9753 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA578 + difference 4 5) (sourceB578 + difference 5 4) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA578 + difference 4 5) (sourceB578 + difference 5 4) sourceC578) = raw9754 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9754; decide +kernel
    rw [ha]
    exact (canonical9754 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA578 + difference 5 0) (sourceB578 + difference 0 5) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA578 + difference 5 0) (sourceB578 + difference 0 5) sourceC578) = raw9755 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9755; decide +kernel
    rw [ha]
    exact (canonical9755 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA578 + difference 5 1) (sourceB578 + difference 1 5) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA578 + difference 5 1) (sourceB578 + difference 1 5) sourceC578) = raw9756 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9756; decide +kernel
    rw [ha]
    exact (canonical9756 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA578 + difference 5 2) (sourceB578 + difference 2 5) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA578 + difference 5 2) (sourceB578 + difference 2 5) sourceC578) = raw9757 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9757; decide +kernel
    rw [ha]
    exact (canonical9757 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA578 + difference 5 3) (sourceB578 + difference 3 5) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA578 + difference 5 3) (sourceB578 + difference 3 5) sourceC578) = raw9758 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9758; decide +kernel
    rw [ha]
    exact (canonical9758 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA578 + difference 5 4) (sourceB578 + difference 4 5) sourceC578) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA578 + difference 5 4) (sourceB578 + difference 4 5) sourceC578) = raw9759 := by
      apply Matrix.ext; unfold tripleCharges sourceA578 sourceB578 sourceC578 difference raw9759; decide +kernel
    rw [ha]
    exact (canonical9759 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA578 sourceB578 sourceC578
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm578, Integer.Sparse.eval]
  linarith only [hs]

def sourceA579 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB579 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC579 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceForm579 : Integer.Sparse Master := [(Sum.inr 1213, 1), (Sum.inr 1215, 1), (Sum.inr 1220, 1), (Sum.inr 1237, 1), (Sum.inr 1266, 1), (Sum.inr 2543, 1), (Sum.inr 2558, 1), (Sum.inr 2572, 1), (Sum.inr 2712, 1), (Sum.inr 2862, 1), (Sum.inr 2868, 1), (Sum.inr 2882, 1), (Sum.inr 2917, 1), (Sum.inr 2925, 1), (Sum.inr 2936, 1), (Sum.inr 2987, 1), (Sum.inr 2991, 1), (Sum.inr 3000, 1), (Sum.inr 3065, 1), (Sum.inr 3078, 1), (Sum.inr 3087, 1), (Sum.inr 3088, 2), (Sum.inr 3099, 1), (Sum.inr 3111, 1), (Sum.inr 3990, 1), (Sum.inr 3993, 1), (Sum.inr 3996, 1), (Sum.inr 4012, 1), (Sum.inr 4036, 1)]

theorem sourceEq579 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm579 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA579 + difference 0 1) (sourceB579 + difference 1 0) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA579 + difference 0 1) (sourceB579 + difference 1 0) sourceC579) = raw9760 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9760; decide +kernel
    rw [ha]
    exact (canonical9760 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA579 + difference 0 2) (sourceB579 + difference 2 0) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA579 + difference 0 2) (sourceB579 + difference 2 0) sourceC579) = raw9761 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9761; decide +kernel
    rw [ha]
    exact (canonical9761 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA579 + difference 0 3) (sourceB579 + difference 3 0) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3996) := by
    have ha : (tripleCharges (sourceA579 + difference 0 3) (sourceB579 + difference 3 0) sourceC579) = raw9762 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9762; decide +kernel
    rw [ha]
    exact (canonical9762 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA579 + difference 0 4) (sourceB579 + difference 4 0) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA579 + difference 0 4) (sourceB579 + difference 4 0) sourceC579) = raw9763 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9763; decide +kernel
    rw [ha]
    exact (canonical9763 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA579 + difference 0 5) (sourceB579 + difference 5 0) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4036) := by
    have ha : (tripleCharges (sourceA579 + difference 0 5) (sourceB579 + difference 5 0) sourceC579) = raw9764 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9764; decide +kernel
    rw [ha]
    exact (canonical9764 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA579 + difference 1 0) (sourceB579 + difference 0 1) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1266) := by
    have ha : (tripleCharges (sourceA579 + difference 1 0) (sourceB579 + difference 0 1) sourceC579) = raw9765 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9765; decide +kernel
    rw [ha]
    exact (canonical9765 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA579 + difference 1 2) (sourceB579 + difference 2 1) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2936) := by
    have ha : (tripleCharges (sourceA579 + difference 1 2) (sourceB579 + difference 2 1) sourceC579) = raw9766 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9766; decide +kernel
    rw [ha]
    exact (canonical9766 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA579 + difference 1 3) (sourceB579 + difference 3 1) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3000) := by
    have ha : (tripleCharges (sourceA579 + difference 1 3) (sourceB579 + difference 3 1) sourceC579) = raw9767 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9767; decide +kernel
    rw [ha]
    exact (canonical9767 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA579 + difference 1 4) (sourceB579 + difference 4 1) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA579 + difference 1 4) (sourceB579 + difference 4 1) sourceC579) = raw9768 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9768; decide +kernel
    rw [ha]
    exact (canonical9768 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA579 + difference 1 5) (sourceB579 + difference 5 1) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3111) := by
    have ha : (tripleCharges (sourceA579 + difference 1 5) (sourceB579 + difference 5 1) sourceC579) = raw9769 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9769; decide +kernel
    rw [ha]
    exact (canonical9769 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA579 + difference 2 0) (sourceB579 + difference 0 2) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA579 + difference 2 0) (sourceB579 + difference 0 2) sourceC579) = raw9770 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9770; decide +kernel
    rw [ha]
    exact (canonical9770 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA579 + difference 2 1) (sourceB579 + difference 1 2) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA579 + difference 2 1) (sourceB579 + difference 1 2) sourceC579) = raw9771 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9771; decide +kernel
    rw [ha]
    exact (canonical9771 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA579 + difference 2 3) (sourceB579 + difference 3 2) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2987) := by
    have ha : (tripleCharges (sourceA579 + difference 2 3) (sourceB579 + difference 3 2) sourceC579) = raw9772 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9772; decide +kernel
    rw [ha]
    exact (canonical9772 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA579 + difference 2 4) (sourceB579 + difference 4 2) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA579 + difference 2 4) (sourceB579 + difference 4 2) sourceC579) = raw9773 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9773; decide +kernel
    rw [ha]
    exact (canonical9773 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA579 + difference 2 5) (sourceB579 + difference 5 2) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA579 + difference 2 5) (sourceB579 + difference 5 2) sourceC579) = raw9774 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9774; decide +kernel
    rw [ha]
    exact (canonical9774 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA579 + difference 3 0) (sourceB579 + difference 0 3) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA579 + difference 3 0) (sourceB579 + difference 0 3) sourceC579) = raw9775 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9775; decide +kernel
    rw [ha]
    exact (canonical9775 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA579 + difference 3 1) (sourceB579 + difference 1 3) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA579 + difference 3 1) (sourceB579 + difference 1 3) sourceC579) = raw9776 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9776; decide +kernel
    rw [ha]
    exact (canonical9776 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA579 + difference 3 2) (sourceB579 + difference 2 3) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA579 + difference 3 2) (sourceB579 + difference 2 3) sourceC579) = raw9777 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9777; decide +kernel
    rw [ha]
    exact (canonical9777 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA579 + difference 3 4) (sourceB579 + difference 4 3) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA579 + difference 3 4) (sourceB579 + difference 4 3) sourceC579) = raw9778 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9778; decide +kernel
    rw [ha]
    exact (canonical9778 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA579 + difference 3 5) (sourceB579 + difference 5 3) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA579 + difference 3 5) (sourceB579 + difference 5 3) sourceC579) = raw9779 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9779; decide +kernel
    rw [ha]
    exact (canonical9779 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA579 + difference 4 0) (sourceB579 + difference 0 4) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA579 + difference 4 0) (sourceB579 + difference 0 4) sourceC579) = raw9780 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9780; decide +kernel
    rw [ha]
    exact (canonical9780 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA579 + difference 4 1) (sourceB579 + difference 1 4) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2868) := by
    have ha : (tripleCharges (sourceA579 + difference 4 1) (sourceB579 + difference 1 4) sourceC579) = raw9781 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9781; decide +kernel
    rw [ha]
    exact (canonical9781 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA579 + difference 4 2) (sourceB579 + difference 2 4) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2917) := by
    have ha : (tripleCharges (sourceA579 + difference 4 2) (sourceB579 + difference 2 4) sourceC579) = raw9782 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9782; decide +kernel
    rw [ha]
    exact (canonical9782 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA579 + difference 4 3) (sourceB579 + difference 3 4) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2991) := by
    have ha : (tripleCharges (sourceA579 + difference 4 3) (sourceB579 + difference 3 4) sourceC579) = raw9783 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9783; decide +kernel
    rw [ha]
    exact (canonical9783 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA579 + difference 4 5) (sourceB579 + difference 5 4) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA579 + difference 4 5) (sourceB579 + difference 5 4) sourceC579) = raw9784 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9784; decide +kernel
    rw [ha]
    exact (canonical9784 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA579 + difference 5 0) (sourceB579 + difference 0 5) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA579 + difference 5 0) (sourceB579 + difference 0 5) sourceC579) = raw9785 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9785; decide +kernel
    rw [ha]
    exact (canonical9785 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA579 + difference 5 1) (sourceB579 + difference 1 5) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA579 + difference 5 1) (sourceB579 + difference 1 5) sourceC579) = raw9786 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9786; decide +kernel
    rw [ha]
    exact (canonical9786 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA579 + difference 5 2) (sourceB579 + difference 2 5) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA579 + difference 5 2) (sourceB579 + difference 2 5) sourceC579) = raw9787 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9787; decide +kernel
    rw [ha]
    exact (canonical9787 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA579 + difference 5 3) (sourceB579 + difference 3 5) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2572) := by
    have ha : (tripleCharges (sourceA579 + difference 5 3) (sourceB579 + difference 3 5) sourceC579) = raw9788 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9788; decide +kernel
    rw [ha]
    exact (canonical9788 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA579 + difference 5 4) (sourceB579 + difference 4 5) sourceC579) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA579 + difference 5 4) (sourceB579 + difference 4 5) sourceC579) = raw9789 := by
      apply Matrix.ext; unfold tripleCharges sourceA579 sourceB579 sourceC579 difference raw9789; decide +kernel
    rw [ha]
    exact (canonical9789 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA579 sourceB579 sourceC579
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm579, Integer.Sparse.eval]
  linarith only [hs]

def sourceA580 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB580 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC580 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceForm580 : Integer.Sparse Master := [(Sum.inr 3290, 1), (Sum.inr 3291, 1), (Sum.inr 3294, 1), (Sum.inr 3297, 1), (Sum.inr 3299, 1), (Sum.inr 3467, 1), (Sum.inr 3481, 1), (Sum.inr 3482, 1), (Sum.inr 3483, 1), (Sum.inr 3519, 1), (Sum.inr 3520, 1), (Sum.inr 3521, 1), (Sum.inr 3523, 1), (Sum.inr 3529, 1), (Sum.inr 3531, 1), (Sum.inr 3532, 1), (Sum.inr 3542, 1), (Sum.inr 3543, 1), (Sum.inr 3544, 2), (Sum.inr 3546, 1), (Sum.inr 3562, 1), (Sum.inr 3578, 1), (Sum.inr 3580, 1), (Sum.inr 3581, 1), (Sum.inr 3816, 1), (Sum.inr 3843, 1), (Sum.inr 3857, 1), (Sum.inr 3858, 1), (Sum.inr 3859, 1)]

theorem sourceEq580 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm580 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA580 + difference 0 1) (sourceB580 + difference 1 0) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA580 + difference 0 1) (sourceB580 + difference 1 0) sourceC580) = raw9790 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9790; decide +kernel
    rw [ha]
    exact (canonical9790 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA580 + difference 0 2) (sourceB580 + difference 2 0) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA580 + difference 0 2) (sourceB580 + difference 2 0) sourceC580) = raw9791 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9791; decide +kernel
    rw [ha]
    exact (canonical9791 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA580 + difference 0 3) (sourceB580 + difference 3 0) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA580 + difference 0 3) (sourceB580 + difference 3 0) sourceC580) = raw9792 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9792; decide +kernel
    rw [ha]
    exact (canonical9792 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA580 + difference 0 4) (sourceB580 + difference 4 0) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA580 + difference 0 4) (sourceB580 + difference 4 0) sourceC580) = raw9793 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9793; decide +kernel
    rw [ha]
    exact (canonical9793 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA580 + difference 0 5) (sourceB580 + difference 5 0) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3859) := by
    have ha : (tripleCharges (sourceA580 + difference 0 5) (sourceB580 + difference 5 0) sourceC580) = raw9794 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9794; decide +kernel
    rw [ha]
    exact (canonical9794 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA580 + difference 1 0) (sourceB580 + difference 0 1) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA580 + difference 1 0) (sourceB580 + difference 0 1) sourceC580) = raw9795 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9795; decide +kernel
    rw [ha]
    exact (canonical9795 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA580 + difference 1 2) (sourceB580 + difference 2 1) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3521) := by
    have ha : (tripleCharges (sourceA580 + difference 1 2) (sourceB580 + difference 2 1) sourceC580) = raw9796 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9796; decide +kernel
    rw [ha]
    exact (canonical9796 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA580 + difference 1 3) (sourceB580 + difference 3 1) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3483) := by
    have ha : (tripleCharges (sourceA580 + difference 1 3) (sourceB580 + difference 3 1) sourceC580) = raw9797 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9797; decide +kernel
    rw [ha]
    exact (canonical9797 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA580 + difference 1 4) (sourceB580 + difference 4 1) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA580 + difference 1 4) (sourceB580 + difference 4 1) sourceC580) = raw9798 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9798; decide +kernel
    rw [ha]
    exact (canonical9798 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA580 + difference 1 5) (sourceB580 + difference 5 1) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA580 + difference 1 5) (sourceB580 + difference 5 1) sourceC580) = raw9799 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9799; decide +kernel
    rw [ha]
    exact (canonical9799 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA580 + difference 2 0) (sourceB580 + difference 0 2) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA580 + difference 2 0) (sourceB580 + difference 0 2) sourceC580) = raw9800 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9800; decide +kernel
    rw [ha]
    exact (canonical9800 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA580 + difference 2 1) (sourceB580 + difference 1 2) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA580 + difference 2 1) (sourceB580 + difference 1 2) sourceC580) = raw9801 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9801; decide +kernel
    rw [ha]
    exact (canonical9801 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA580 + difference 2 3) (sourceB580 + difference 3 2) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA580 + difference 2 3) (sourceB580 + difference 3 2) sourceC580) = raw9802 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9802; decide +kernel
    rw [ha]
    exact (canonical9802 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA580 + difference 2 4) (sourceB580 + difference 4 2) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA580 + difference 2 4) (sourceB580 + difference 4 2) sourceC580) = raw9803 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9803; decide +kernel
    rw [ha]
    exact (canonical9803 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA580 + difference 2 5) (sourceB580 + difference 5 2) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA580 + difference 2 5) (sourceB580 + difference 5 2) sourceC580) = raw9804 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9804; decide +kernel
    rw [ha]
    exact (canonical9804 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA580 + difference 3 0) (sourceB580 + difference 0 3) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA580 + difference 3 0) (sourceB580 + difference 0 3) sourceC580) = raw9805 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9805; decide +kernel
    rw [ha]
    exact (canonical9805 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA580 + difference 3 1) (sourceB580 + difference 1 3) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA580 + difference 3 1) (sourceB580 + difference 1 3) sourceC580) = raw9806 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9806; decide +kernel
    rw [ha]
    exact (canonical9806 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA580 + difference 3 2) (sourceB580 + difference 2 3) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA580 + difference 3 2) (sourceB580 + difference 2 3) sourceC580) = raw9807 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9807; decide +kernel
    rw [ha]
    exact (canonical9807 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA580 + difference 3 4) (sourceB580 + difference 4 3) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA580 + difference 3 4) (sourceB580 + difference 4 3) sourceC580) = raw9808 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9808; decide +kernel
    rw [ha]
    exact (canonical9808 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA580 + difference 3 5) (sourceB580 + difference 5 3) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA580 + difference 3 5) (sourceB580 + difference 5 3) sourceC580) = raw9809 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9809; decide +kernel
    rw [ha]
    exact (canonical9809 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA580 + difference 4 0) (sourceB580 + difference 0 4) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3297) := by
    have ha : (tripleCharges (sourceA580 + difference 4 0) (sourceB580 + difference 0 4) sourceC580) = raw9810 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9810; decide +kernel
    rw [ha]
    exact (canonical9810 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA580 + difference 4 1) (sourceB580 + difference 1 4) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA580 + difference 4 1) (sourceB580 + difference 1 4) sourceC580) = raw9811 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9811; decide +kernel
    rw [ha]
    exact (canonical9811 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA580 + difference 4 2) (sourceB580 + difference 2 4) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA580 + difference 4 2) (sourceB580 + difference 2 4) sourceC580) = raw9812 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9812; decide +kernel
    rw [ha]
    exact (canonical9812 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA580 + difference 4 3) (sourceB580 + difference 3 4) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA580 + difference 4 3) (sourceB580 + difference 3 4) sourceC580) = raw9813 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9813; decide +kernel
    rw [ha]
    exact (canonical9813 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA580 + difference 4 5) (sourceB580 + difference 5 4) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA580 + difference 4 5) (sourceB580 + difference 5 4) sourceC580) = raw9814 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9814; decide +kernel
    rw [ha]
    exact (canonical9814 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA580 + difference 5 0) (sourceB580 + difference 0 5) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA580 + difference 5 0) (sourceB580 + difference 0 5) sourceC580) = raw9815 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9815; decide +kernel
    rw [ha]
    exact (canonical9815 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA580 + difference 5 1) (sourceB580 + difference 1 5) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA580 + difference 5 1) (sourceB580 + difference 1 5) sourceC580) = raw9816 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9816; decide +kernel
    rw [ha]
    exact (canonical9816 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA580 + difference 5 2) (sourceB580 + difference 2 5) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA580 + difference 5 2) (sourceB580 + difference 2 5) sourceC580) = raw9817 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9817; decide +kernel
    rw [ha]
    exact (canonical9817 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA580 + difference 5 3) (sourceB580 + difference 3 5) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA580 + difference 5 3) (sourceB580 + difference 3 5) sourceC580) = raw9818 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9818; decide +kernel
    rw [ha]
    exact (canonical9818 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA580 + difference 5 4) (sourceB580 + difference 4 5) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA580 + difference 5 4) (sourceB580 + difference 4 5) sourceC580) = raw9819 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9819; decide +kernel
    rw [ha]
    exact (canonical9819 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA580 sourceB580 sourceC580
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm580, Integer.Sparse.eval]
  linarith only [hs]

def sourceA581 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB581 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC581 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceForm581 : Integer.Sparse Master := [(Sum.inr 2723, 1), (Sum.inr 3808, 1), (Sum.inr 3838, 1), (Sum.inr 3876, 1), (Sum.inr 3902, 1), (Sum.inr 3904, 1), (Sum.inr 4091, -1)]

theorem sourceEq581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm581 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA581 + difference 0 0) (sourceB581 + difference 0 0) sourceC581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA581 + difference 0 0) (sourceB581 + difference 0 0) sourceC581) = raw9820 := by
      apply Matrix.ext; unfold tripleCharges sourceA581 sourceB581 sourceC581 difference raw9820; decide +kernel
    rw [ha]
    exact (canonical9820 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA581 + difference 0 1) (sourceB581 + difference 1 0) sourceC581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA581 + difference 0 1) (sourceB581 + difference 1 0) sourceC581) = raw9821 := by
      apply Matrix.ext; unfold tripleCharges sourceA581 sourceB581 sourceC581 difference raw9821; decide +kernel
    rw [ha]
    exact (canonical9821 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA581 + difference 0 2) (sourceB581 + difference 2 0) sourceC581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA581 + difference 0 2) (sourceB581 + difference 2 0) sourceC581) = raw9822 := by
      apply Matrix.ext; unfold tripleCharges sourceA581 sourceB581 sourceC581 difference raw9822; decide +kernel
    rw [ha]
    exact (canonical9822 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA581 + difference 0 3) (sourceB581 + difference 3 0) sourceC581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA581 + difference 0 3) (sourceB581 + difference 3 0) sourceC581) = raw9823 := by
      apply Matrix.ext; unfold tripleCharges sourceA581 sourceB581 sourceC581 difference raw9823; decide +kernel
    rw [ha]
    exact (canonical9823 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA581 + difference 0 4) (sourceB581 + difference 4 0) sourceC581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA581 + difference 0 4) (sourceB581 + difference 4 0) sourceC581) = raw9824 := by
      apply Matrix.ext; unfold tripleCharges sourceA581 sourceB581 sourceC581 difference raw9824; decide +kernel
    rw [ha]
    exact (canonical9824 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA581 + difference 0 5) (sourceB581 + difference 5 0) sourceC581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3904) := by
    have ha : (tripleCharges (sourceA581 + difference 0 5) (sourceB581 + difference 5 0) sourceC581) = raw9825 := by
      apply Matrix.ext; unfold tripleCharges sourceA581 sourceB581 sourceC581 difference raw9825; decide +kernel
    rw [ha]
    exact (canonical9825 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA581 + sourceB581) sourceC581) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA581 + sourceB581) sourceC581) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA581 sourceB581 sourceC581 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA581 sourceB581 sourceC581
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm581, Integer.Sparse.eval]
  linarith only [hs]

def sourceA582 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB582 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC582 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceForm582 : Integer.Sparse Master := [(Sum.inr 1213, 1), (Sum.inr 1217, 1), (Sum.inr 1220, 1), (Sum.inr 1240, 1), (Sum.inr 1262, 1), (Sum.inr 2723, 1), (Sum.inr 4091, -1)]

theorem sourceEq582 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm582 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA582 + difference 0 0) (sourceB582 + difference 0 0) sourceC582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA582 + difference 0 0) (sourceB582 + difference 0 0) sourceC582) = raw9820 := by
      apply Matrix.ext; unfold tripleCharges sourceA582 sourceB582 sourceC582 difference raw9820; decide +kernel
    rw [ha]
    exact (canonical9820 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA582 + difference 1 0) (sourceB582 + difference 0 1) sourceC582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA582 + difference 1 0) (sourceB582 + difference 0 1) sourceC582) = raw9827 := by
      apply Matrix.ext; unfold tripleCharges sourceA582 sourceB582 sourceC582 difference raw9827; decide +kernel
    rw [ha]
    exact (canonical9827 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA582 + difference 2 0) (sourceB582 + difference 0 2) sourceC582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA582 + difference 2 0) (sourceB582 + difference 0 2) sourceC582) = raw9828 := by
      apply Matrix.ext; unfold tripleCharges sourceA582 sourceB582 sourceC582 difference raw9828; decide +kernel
    rw [ha]
    exact (canonical9828 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA582 + difference 3 0) (sourceB582 + difference 0 3) sourceC582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA582 + difference 3 0) (sourceB582 + difference 0 3) sourceC582) = raw9829 := by
      apply Matrix.ext; unfold tripleCharges sourceA582 sourceB582 sourceC582 difference raw9829; decide +kernel
    rw [ha]
    exact (canonical9829 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA582 + difference 4 0) (sourceB582 + difference 0 4) sourceC582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA582 + difference 4 0) (sourceB582 + difference 0 4) sourceC582) = raw9830 := by
      apply Matrix.ext; unfold tripleCharges sourceA582 sourceB582 sourceC582 difference raw9830; decide +kernel
    rw [ha]
    exact (canonical9830 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA582 + difference 5 0) (sourceB582 + difference 0 5) sourceC582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA582 + difference 5 0) (sourceB582 + difference 0 5) sourceC582) = raw9831 := by
      apply Matrix.ext; unfold tripleCharges sourceA582 sourceB582 sourceC582 difference raw9831; decide +kernel
    rw [ha]
    exact (canonical9831 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA582 + sourceB582) sourceC582) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA582 + sourceB582) sourceC582) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA582 sourceB582 sourceC582 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA582 sourceB582 sourceC582
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm582, Integer.Sparse.eval]
  linarith only [hs]

def sourceA583 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB583 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC583 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceForm583 : Integer.Sparse Master := [(Sum.inr 1240, 1), (Sum.inr 2514, 1), (Sum.inr 2556, 1), (Sum.inr 2723, 2), (Sum.inr 2741, 1), (Sum.inr 4091, -1)]

theorem sourceEq583 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm583 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA583 + difference 1 0) (sourceB583 + difference 0 1) sourceC583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA583 + difference 1 0) (sourceB583 + difference 0 1) sourceC583) = raw9827 := by
      apply Matrix.ext; unfold tripleCharges sourceA583 sourceB583 sourceC583 difference raw9827; decide +kernel
    rw [ha]
    exact (canonical9827 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA583 + difference 1 1) (sourceB583 + difference 1 1) sourceC583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA583 + difference 1 1) (sourceB583 + difference 1 1) sourceC583) = raw9820 := by
      apply Matrix.ext; unfold tripleCharges sourceA583 sourceB583 sourceC583 difference raw9820; decide +kernel
    rw [ha]
    exact (canonical9820 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA583 + difference 1 2) (sourceB583 + difference 2 1) sourceC583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA583 + difference 1 2) (sourceB583 + difference 2 1) sourceC583) = raw9832 := by
      apply Matrix.ext; unfold tripleCharges sourceA583 sourceB583 sourceC583 difference raw9832; decide +kernel
    rw [ha]
    exact (canonical9832 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA583 + difference 1 3) (sourceB583 + difference 3 1) sourceC583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2514) := by
    have ha : (tripleCharges (sourceA583 + difference 1 3) (sourceB583 + difference 3 1) sourceC583) = raw9833 := by
      apply Matrix.ext; unfold tripleCharges sourceA583 sourceB583 sourceC583 difference raw9833; decide +kernel
    rw [ha]
    exact (canonical9833 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA583 + difference 1 4) (sourceB583 + difference 4 1) sourceC583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA583 + difference 1 4) (sourceB583 + difference 4 1) sourceC583) = raw9834 := by
      apply Matrix.ext; unfold tripleCharges sourceA583 sourceB583 sourceC583 difference raw9834; decide +kernel
    rw [ha]
    exact (canonical9834 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA583 + difference 1 5) (sourceB583 + difference 5 1) sourceC583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA583 + difference 1 5) (sourceB583 + difference 5 1) sourceC583) = raw9835 := by
      apply Matrix.ext; unfold tripleCharges sourceA583 sourceB583 sourceC583 difference raw9835; decide +kernel
    rw [ha]
    exact (canonical9835 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA583 + sourceB583) sourceC583) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA583 + sourceB583) sourceC583) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA583 sourceB583 sourceC583 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA583 sourceB583 sourceC583
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm583, Integer.Sparse.eval]
  linarith only [hs]

def sourceA584 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB584 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC584 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceForm584 : Integer.Sparse Master := [(Sum.inr 2615, 1), (Sum.inr 2618, 1), (Sum.inr 2621, 1), (Sum.inr 2633, 1), (Sum.inr 2723, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

theorem sourceEq584 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm584 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA584 + difference 0 1) (sourceB584 + difference 1 0) sourceC584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA584 + difference 0 1) (sourceB584 + difference 1 0) sourceC584) = raw9821 := by
      apply Matrix.ext; unfold tripleCharges sourceA584 sourceB584 sourceC584 difference raw9821; decide +kernel
    rw [ha]
    exact (canonical9821 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA584 + difference 1 1) (sourceB584 + difference 1 1) sourceC584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA584 + difference 1 1) (sourceB584 + difference 1 1) sourceC584) = raw9820 := by
      apply Matrix.ext; unfold tripleCharges sourceA584 sourceB584 sourceC584 difference raw9820; decide +kernel
    rw [ha]
    exact (canonical9820 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA584 + difference 2 1) (sourceB584 + difference 1 2) sourceC584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA584 + difference 2 1) (sourceB584 + difference 1 2) sourceC584) = raw9836 := by
      apply Matrix.ext; unfold tripleCharges sourceA584 sourceB584 sourceC584 difference raw9836; decide +kernel
    rw [ha]
    exact (canonical9836 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA584 + difference 3 1) (sourceB584 + difference 1 3) sourceC584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA584 + difference 3 1) (sourceB584 + difference 1 3) sourceC584) = raw9837 := by
      apply Matrix.ext; unfold tripleCharges sourceA584 sourceB584 sourceC584 difference raw9837; decide +kernel
    rw [ha]
    exact (canonical9837 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA584 + difference 4 1) (sourceB584 + difference 1 4) sourceC584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2621) := by
    have ha : (tripleCharges (sourceA584 + difference 4 1) (sourceB584 + difference 1 4) sourceC584) = raw9838 := by
      apply Matrix.ext; unfold tripleCharges sourceA584 sourceB584 sourceC584 difference raw9838; decide +kernel
    rw [ha]
    exact (canonical9838 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA584 + difference 5 1) (sourceB584 + difference 1 5) sourceC584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA584 + difference 5 1) (sourceB584 + difference 1 5) sourceC584) = raw9839 := by
      apply Matrix.ext; unfold tripleCharges sourceA584 sourceB584 sourceC584 difference raw9839; decide +kernel
    rw [ha]
    exact (canonical9839 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA584 + sourceB584) sourceC584) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA584 + sourceB584) sourceC584) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA584 sourceB584 sourceC584 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA584 sourceB584 sourceC584
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm584, Integer.Sparse.eval]
  linarith only [hs]

def sourceA585 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB585 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC585 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceForm585 : Integer.Sparse Master := [(Sum.inr 2543, 1), (Sum.inr 2546, 1), (Sum.inr 2556, 1), (Sum.inr 2567, 1), (Sum.inr 2723, 1), (Sum.inr 3838, 1), (Sum.inr 4091, -1)]

theorem sourceEq585 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm585 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA585 + difference 0 2) (sourceB585 + difference 2 0) sourceC585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA585 + difference 0 2) (sourceB585 + difference 2 0) sourceC585) = raw9822 := by
      apply Matrix.ext; unfold tripleCharges sourceA585 sourceB585 sourceC585 difference raw9822; decide +kernel
    rw [ha]
    exact (canonical9822 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA585 + difference 1 2) (sourceB585 + difference 2 1) sourceC585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA585 + difference 1 2) (sourceB585 + difference 2 1) sourceC585) = raw9832 := by
      apply Matrix.ext; unfold tripleCharges sourceA585 sourceB585 sourceC585 difference raw9832; decide +kernel
    rw [ha]
    exact (canonical9832 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA585 + difference 2 2) (sourceB585 + difference 2 2) sourceC585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA585 + difference 2 2) (sourceB585 + difference 2 2) sourceC585) = raw9820 := by
      apply Matrix.ext; unfold tripleCharges sourceA585 sourceB585 sourceC585 difference raw9820; decide +kernel
    rw [ha]
    exact (canonical9820 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA585 + difference 3 2) (sourceB585 + difference 2 3) sourceC585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA585 + difference 3 2) (sourceB585 + difference 2 3) sourceC585) = raw9840 := by
      apply Matrix.ext; unfold tripleCharges sourceA585 sourceB585 sourceC585 difference raw9840; decide +kernel
    rw [ha]
    exact (canonical9840 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA585 + difference 4 2) (sourceB585 + difference 2 4) sourceC585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2546) := by
    have ha : (tripleCharges (sourceA585 + difference 4 2) (sourceB585 + difference 2 4) sourceC585) = raw9841 := by
      apply Matrix.ext; unfold tripleCharges sourceA585 sourceB585 sourceC585 difference raw9841; decide +kernel
    rw [ha]
    exact (canonical9841 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA585 + difference 5 2) (sourceB585 + difference 2 5) sourceC585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA585 + difference 5 2) (sourceB585 + difference 2 5) sourceC585) = raw9842 := by
      apply Matrix.ext; unfold tripleCharges sourceA585 sourceB585 sourceC585 difference raw9842; decide +kernel
    rw [ha]
    exact (canonical9842 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA585 + sourceB585) sourceC585) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA585 + sourceB585) sourceC585) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA585 sourceB585 sourceC585 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA585 sourceB585 sourceC585
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm585, Integer.Sparse.eval]
  linarith only [hs]

def sourceA586 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB586 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC586 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceForm586 : Integer.Sparse Master := [(Sum.inr 2480, 1), (Sum.inr 2485, 1), (Sum.inr 2489, 1), (Sum.inr 2514, 1), (Sum.inr 2723, 1), (Sum.inr 3808, 1), (Sum.inr 4091, -1)]

theorem sourceEq586 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm586 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA586 + difference 0 3) (sourceB586 + difference 3 0) sourceC586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA586 + difference 0 3) (sourceB586 + difference 3 0) sourceC586) = raw9823 := by
      apply Matrix.ext; unfold tripleCharges sourceA586 sourceB586 sourceC586 difference raw9823; decide +kernel
    rw [ha]
    exact (canonical9823 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA586 + difference 1 3) (sourceB586 + difference 3 1) sourceC586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2514) := by
    have ha : (tripleCharges (sourceA586 + difference 1 3) (sourceB586 + difference 3 1) sourceC586) = raw9833 := by
      apply Matrix.ext; unfold tripleCharges sourceA586 sourceB586 sourceC586 difference raw9833; decide +kernel
    rw [ha]
    exact (canonical9833 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA586 + difference 2 3) (sourceB586 + difference 3 2) sourceC586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA586 + difference 2 3) (sourceB586 + difference 3 2) sourceC586) = raw9843 := by
      apply Matrix.ext; unfold tripleCharges sourceA586 sourceB586 sourceC586 difference raw9843; decide +kernel
    rw [ha]
    exact (canonical9843 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA586 + difference 3 3) (sourceB586 + difference 3 3) sourceC586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA586 + difference 3 3) (sourceB586 + difference 3 3) sourceC586) = raw9820 := by
      apply Matrix.ext; unfold tripleCharges sourceA586 sourceB586 sourceC586 difference raw9820; decide +kernel
    rw [ha]
    exact (canonical9820 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA586 + difference 4 3) (sourceB586 + difference 3 4) sourceC586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA586 + difference 4 3) (sourceB586 + difference 3 4) sourceC586) = raw9844 := by
      apply Matrix.ext; unfold tripleCharges sourceA586 sourceB586 sourceC586 difference raw9844; decide +kernel
    rw [ha]
    exact (canonical9844 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA586 + difference 5 3) (sourceB586 + difference 3 5) sourceC586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA586 + difference 5 3) (sourceB586 + difference 3 5) sourceC586) = raw9845 := by
      apply Matrix.ext; unfold tripleCharges sourceA586 sourceB586 sourceC586 difference raw9845; decide +kernel
    rw [ha]
    exact (canonical9845 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA586 + sourceB586) sourceC586) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA586 + sourceB586) sourceC586) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA586 sourceB586 sourceC586 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA586 sourceB586 sourceC586
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm586, Integer.Sparse.eval]
  linarith only [hs]

def sourceA587 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB587 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC587 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceForm587 : Integer.Sparse Master := [(Sum.inr 1220, 1), (Sum.inr 2489, 1), (Sum.inr 2546, 1), (Sum.inr 2621, 1), (Sum.inr 2723, 2), (Sum.inr 4091, -1)]

theorem sourceEq587 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm587 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA587 + difference 4 0) (sourceB587 + difference 0 4) sourceC587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA587 + difference 4 0) (sourceB587 + difference 0 4) sourceC587) = raw9830 := by
      apply Matrix.ext; unfold tripleCharges sourceA587 sourceB587 sourceC587 difference raw9830; decide +kernel
    rw [ha]
    exact (canonical9830 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA587 + difference 4 1) (sourceB587 + difference 1 4) sourceC587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2621) := by
    have ha : (tripleCharges (sourceA587 + difference 4 1) (sourceB587 + difference 1 4) sourceC587) = raw9838 := by
      apply Matrix.ext; unfold tripleCharges sourceA587 sourceB587 sourceC587 difference raw9838; decide +kernel
    rw [ha]
    exact (canonical9838 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA587 + difference 4 2) (sourceB587 + difference 2 4) sourceC587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2546) := by
    have ha : (tripleCharges (sourceA587 + difference 4 2) (sourceB587 + difference 2 4) sourceC587) = raw9841 := by
      apply Matrix.ext; unfold tripleCharges sourceA587 sourceB587 sourceC587 difference raw9841; decide +kernel
    rw [ha]
    exact (canonical9841 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA587 + difference 4 3) (sourceB587 + difference 3 4) sourceC587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA587 + difference 4 3) (sourceB587 + difference 3 4) sourceC587) = raw9844 := by
      apply Matrix.ext; unfold tripleCharges sourceA587 sourceB587 sourceC587 difference raw9844; decide +kernel
    rw [ha]
    exact (canonical9844 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA587 + difference 4 4) (sourceB587 + difference 4 4) sourceC587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA587 + difference 4 4) (sourceB587 + difference 4 4) sourceC587) = raw9820 := by
      apply Matrix.ext; unfold tripleCharges sourceA587 sourceB587 sourceC587 difference raw9820; decide +kernel
    rw [ha]
    exact (canonical9820 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA587 + difference 4 5) (sourceB587 + difference 5 4) sourceC587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA587 + difference 4 5) (sourceB587 + difference 5 4) sourceC587) = raw9846 := by
      apply Matrix.ext; unfold tripleCharges sourceA587 sourceB587 sourceC587 difference raw9846; decide +kernel
    rw [ha]
    exact (canonical9846 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA587 + sourceB587) sourceC587) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA587 + sourceB587) sourceC587) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA587 sourceB587 sourceC587 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA587 sourceB587 sourceC587
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm587, Integer.Sparse.eval]
  linarith only [hs]

def sourceA588 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB588 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC588 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceForm588 : Integer.Sparse Master := [(Sum.inr 4399, 1), (Sum.inr 4401, 1), (Sum.inr 4404, 1), (Sum.inr 4424, 1), (Sum.inr 4458, 1), (Sum.inr 4998, 1), (Sum.inr 5000, 1), (Sum.inr 5003, 1), (Sum.inr 5018, 1), (Sum.inr 5047, 1), (Sum.inr 5050, 1), (Sum.inr 5059, 1), (Sum.inr 5073, 1), (Sum.inr 5075, 1), (Sum.inr 5137, 1), (Sum.inr 5141, 1), (Sum.inr 5169, 1), (Sum.inr 5257, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5261, 1), (Sum.inr 5271, 1), (Sum.inr 5275, 1), (Sum.inr 5292, 1), (Sum.inr 5293, 1), (Sum.inr 5473, 1), (Sum.inr 5477, 1), (Sum.inr 5483, 1), (Sum.inr 5490, 1), (Sum.inr 5491, 1)]

theorem sourceEq588 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm588 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA588 + difference 0 1) (sourceB588 + difference 1 0) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA588 + difference 0 1) (sourceB588 + difference 1 0) sourceC588) = raw3145 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw3145; decide +kernel
    rw [ha]
    exact (canonical3145 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA588 + difference 0 2) (sourceB588 + difference 2 0) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA588 + difference 0 2) (sourceB588 + difference 2 0) sourceC588) = raw3146 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw3146; decide +kernel
    rw [ha]
    exact (canonical3146 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA588 + difference 0 3) (sourceB588 + difference 3 0) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA588 + difference 0 3) (sourceB588 + difference 3 0) sourceC588) = raw3147 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw3147; decide +kernel
    rw [ha]
    exact (canonical3147 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA588 + difference 0 4) (sourceB588 + difference 4 0) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA588 + difference 0 4) (sourceB588 + difference 4 0) sourceC588) = raw3148 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw3148; decide +kernel
    rw [ha]
    exact (canonical3148 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA588 + difference 0 5) (sourceB588 + difference 5 0) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA588 + difference 0 5) (sourceB588 + difference 5 0) sourceC588) = raw9847 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9847; decide +kernel
    rw [ha]
    exact (canonical9847 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA588 + difference 1 0) (sourceB588 + difference 0 1) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA588 + difference 1 0) (sourceB588 + difference 0 1) sourceC588) = raw9848 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9848; decide +kernel
    rw [ha]
    exact (canonical9848 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA588 + difference 1 2) (sourceB588 + difference 2 1) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA588 + difference 1 2) (sourceB588 + difference 2 1) sourceC588) = raw9849 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9849; decide +kernel
    rw [ha]
    exact (canonical9849 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA588 + difference 1 3) (sourceB588 + difference 3 1) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA588 + difference 1 3) (sourceB588 + difference 3 1) sourceC588) = raw9850 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9850; decide +kernel
    rw [ha]
    exact (canonical9850 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA588 + difference 1 4) (sourceB588 + difference 4 1) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA588 + difference 1 4) (sourceB588 + difference 4 1) sourceC588) = raw9851 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9851; decide +kernel
    rw [ha]
    exact (canonical9851 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA588 + difference 1 5) (sourceB588 + difference 5 1) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA588 + difference 1 5) (sourceB588 + difference 5 1) sourceC588) = raw3124 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw3124; decide +kernel
    rw [ha]
    exact (canonical3124 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA588 + difference 2 0) (sourceB588 + difference 0 2) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA588 + difference 2 0) (sourceB588 + difference 0 2) sourceC588) = raw9852 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9852; decide +kernel
    rw [ha]
    exact (canonical9852 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA588 + difference 2 1) (sourceB588 + difference 1 2) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA588 + difference 2 1) (sourceB588 + difference 1 2) sourceC588) = raw9853 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9853; decide +kernel
    rw [ha]
    exact (canonical9853 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA588 + difference 2 3) (sourceB588 + difference 3 2) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA588 + difference 2 3) (sourceB588 + difference 3 2) sourceC588) = raw9854 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9854; decide +kernel
    rw [ha]
    exact (canonical9854 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA588 + difference 2 4) (sourceB588 + difference 4 2) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA588 + difference 2 4) (sourceB588 + difference 4 2) sourceC588) = raw9855 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9855; decide +kernel
    rw [ha]
    exact (canonical9855 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA588 + difference 2 5) (sourceB588 + difference 5 2) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA588 + difference 2 5) (sourceB588 + difference 5 2) sourceC588) = raw3129 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw3129; decide +kernel
    rw [ha]
    exact (canonical3129 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA588 + difference 3 0) (sourceB588 + difference 0 3) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA588 + difference 3 0) (sourceB588 + difference 0 3) sourceC588) = raw9856 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9856; decide +kernel
    rw [ha]
    exact (canonical9856 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA588 + difference 3 1) (sourceB588 + difference 1 3) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA588 + difference 3 1) (sourceB588 + difference 1 3) sourceC588) = raw9857 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9857; decide +kernel
    rw [ha]
    exact (canonical9857 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA588 + difference 3 2) (sourceB588 + difference 2 3) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA588 + difference 3 2) (sourceB588 + difference 2 3) sourceC588) = raw9858 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9858; decide +kernel
    rw [ha]
    exact (canonical9858 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA588 + difference 3 4) (sourceB588 + difference 4 3) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA588 + difference 3 4) (sourceB588 + difference 4 3) sourceC588) = raw9859 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9859; decide +kernel
    rw [ha]
    exact (canonical9859 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA588 + difference 3 5) (sourceB588 + difference 5 3) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA588 + difference 3 5) (sourceB588 + difference 5 3) sourceC588) = raw3134 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw3134; decide +kernel
    rw [ha]
    exact (canonical3134 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA588 + difference 4 0) (sourceB588 + difference 0 4) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA588 + difference 4 0) (sourceB588 + difference 0 4) sourceC588) = raw9860 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9860; decide +kernel
    rw [ha]
    exact (canonical9860 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA588 + difference 4 1) (sourceB588 + difference 1 4) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA588 + difference 4 1) (sourceB588 + difference 1 4) sourceC588) = raw9861 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9861; decide +kernel
    rw [ha]
    exact (canonical9861 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA588 + difference 4 2) (sourceB588 + difference 2 4) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA588 + difference 4 2) (sourceB588 + difference 2 4) sourceC588) = raw9862 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9862; decide +kernel
    rw [ha]
    exact (canonical9862 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA588 + difference 4 3) (sourceB588 + difference 3 4) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA588 + difference 4 3) (sourceB588 + difference 3 4) sourceC588) = raw9863 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9863; decide +kernel
    rw [ha]
    exact (canonical9863 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA588 + difference 4 5) (sourceB588 + difference 5 4) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA588 + difference 4 5) (sourceB588 + difference 5 4) sourceC588) = raw3139 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw3139; decide +kernel
    rw [ha]
    exact (canonical3139 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA588 + difference 5 0) (sourceB588 + difference 0 5) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA588 + difference 5 0) (sourceB588 + difference 0 5) sourceC588) = raw9864 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9864; decide +kernel
    rw [ha]
    exact (canonical9864 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA588 + difference 5 1) (sourceB588 + difference 1 5) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA588 + difference 5 1) (sourceB588 + difference 1 5) sourceC588) = raw9865 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9865; decide +kernel
    rw [ha]
    exact (canonical9865 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA588 + difference 5 2) (sourceB588 + difference 2 5) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5047) := by
    have ha : (tripleCharges (sourceA588 + difference 5 2) (sourceB588 + difference 2 5) sourceC588) = raw9866 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9866; decide +kernel
    rw [ha]
    exact (canonical9866 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA588 + difference 5 3) (sourceB588 + difference 3 5) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA588 + difference 5 3) (sourceB588 + difference 3 5) sourceC588) = raw9867 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9867; decide +kernel
    rw [ha]
    exact (canonical9867 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA588 + difference 5 4) (sourceB588 + difference 4 5) sourceC588) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA588 + difference 5 4) (sourceB588 + difference 4 5) sourceC588) = raw9868 := by
      apply Matrix.ext; unfold tripleCharges sourceA588 sourceB588 sourceC588 difference raw9868; decide +kernel
    rw [ha]
    exact (canonical9868 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA588 sourceB588 sourceC588
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm588, Integer.Sparse.eval]
  linarith only [hs]

def sourceA589 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB589 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC589 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceForm589 : Integer.Sparse Master := [(Sum.inr 980, 1), (Sum.inr 982, 1), (Sum.inr 985, 1), (Sum.inr 1005, 1), (Sum.inr 1041, 1), (Sum.inr 2383, 1), (Sum.inr 2385, 1), (Sum.inr 2388, 1), (Sum.inr 2404, 1), (Sum.inr 2449, 1), (Sum.inr 2452, 1), (Sum.inr 2462, 1), (Sum.inr 2480, 1), (Sum.inr 2482, 1), (Sum.inr 2556, 1), (Sum.inr 2561, 1), (Sum.inr 2595, 1), (Sum.inr 2721, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 2726, 1), (Sum.inr 2739, 1), (Sum.inr 2743, 1), (Sum.inr 2766, 1), (Sum.inr 2767, 1), (Sum.inr 3958, 1), (Sum.inr 3971, 1), (Sum.inr 3981, 1), (Sum.inr 4013, 1), (Sum.inr 4014, 1)]

theorem sourceEq589 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm589 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA589 + difference 0 1) (sourceB589 + difference 1 0) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA589 + difference 0 1) (sourceB589 + difference 1 0) sourceC589) = raw3175 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw3175; decide +kernel
    rw [ha]
    exact (canonical3175 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA589 + difference 0 2) (sourceB589 + difference 2 0) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3971) := by
    have ha : (tripleCharges (sourceA589 + difference 0 2) (sourceB589 + difference 2 0) sourceC589) = raw3176 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw3176; decide +kernel
    rw [ha]
    exact (canonical3176 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA589 + difference 0 3) (sourceB589 + difference 3 0) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA589 + difference 0 3) (sourceB589 + difference 3 0) sourceC589) = raw3177 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw3177; decide +kernel
    rw [ha]
    exact (canonical3177 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA589 + difference 0 4) (sourceB589 + difference 4 0) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4014) := by
    have ha : (tripleCharges (sourceA589 + difference 0 4) (sourceB589 + difference 4 0) sourceC589) = raw3178 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw3178; decide +kernel
    rw [ha]
    exact (canonical3178 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA589 + difference 0 5) (sourceB589 + difference 5 0) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA589 + difference 0 5) (sourceB589 + difference 5 0) sourceC589) = raw9869 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9869; decide +kernel
    rw [ha]
    exact (canonical9869 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA589 + difference 1 0) (sourceB589 + difference 0 1) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA589 + difference 1 0) (sourceB589 + difference 0 1) sourceC589) = raw9870 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9870; decide +kernel
    rw [ha]
    exact (canonical9870 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA589 + difference 1 2) (sourceB589 + difference 2 1) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA589 + difference 1 2) (sourceB589 + difference 2 1) sourceC589) = raw9871 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9871; decide +kernel
    rw [ha]
    exact (canonical9871 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA589 + difference 1 3) (sourceB589 + difference 3 1) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2404) := by
    have ha : (tripleCharges (sourceA589 + difference 1 3) (sourceB589 + difference 3 1) sourceC589) = raw9872 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9872; decide +kernel
    rw [ha]
    exact (canonical9872 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA589 + difference 1 4) (sourceB589 + difference 4 1) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA589 + difference 1 4) (sourceB589 + difference 4 1) sourceC589) = raw9873 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9873; decide +kernel
    rw [ha]
    exact (canonical9873 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA589 + difference 1 5) (sourceB589 + difference 5 1) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA589 + difference 1 5) (sourceB589 + difference 5 1) sourceC589) = raw3154 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw3154; decide +kernel
    rw [ha]
    exact (canonical3154 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA589 + difference 2 0) (sourceB589 + difference 0 2) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA589 + difference 2 0) (sourceB589 + difference 0 2) sourceC589) = raw9874 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9874; decide +kernel
    rw [ha]
    exact (canonical9874 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA589 + difference 2 1) (sourceB589 + difference 1 2) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA589 + difference 2 1) (sourceB589 + difference 1 2) sourceC589) = raw9875 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9875; decide +kernel
    rw [ha]
    exact (canonical9875 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA589 + difference 2 3) (sourceB589 + difference 3 2) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2383) := by
    have ha : (tripleCharges (sourceA589 + difference 2 3) (sourceB589 + difference 3 2) sourceC589) = raw9876 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9876; decide +kernel
    rw [ha]
    exact (canonical9876 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA589 + difference 2 4) (sourceB589 + difference 4 2) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA589 + difference 2 4) (sourceB589 + difference 4 2) sourceC589) = raw9877 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9877; decide +kernel
    rw [ha]
    exact (canonical9877 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA589 + difference 2 5) (sourceB589 + difference 5 2) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA589 + difference 2 5) (sourceB589 + difference 5 2) sourceC589) = raw3159 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw3159; decide +kernel
    rw [ha]
    exact (canonical3159 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA589 + difference 3 0) (sourceB589 + difference 0 3) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA589 + difference 3 0) (sourceB589 + difference 0 3) sourceC589) = raw9878 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9878; decide +kernel
    rw [ha]
    exact (canonical9878 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA589 + difference 3 1) (sourceB589 + difference 1 3) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA589 + difference 3 1) (sourceB589 + difference 1 3) sourceC589) = raw9879 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9879; decide +kernel
    rw [ha]
    exact (canonical9879 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA589 + difference 3 2) (sourceB589 + difference 2 3) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA589 + difference 3 2) (sourceB589 + difference 2 3) sourceC589) = raw9880 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9880; decide +kernel
    rw [ha]
    exact (canonical9880 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA589 + difference 3 4) (sourceB589 + difference 4 3) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA589 + difference 3 4) (sourceB589 + difference 4 3) sourceC589) = raw9881 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9881; decide +kernel
    rw [ha]
    exact (canonical9881 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA589 + difference 3 5) (sourceB589 + difference 5 3) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA589 + difference 3 5) (sourceB589 + difference 5 3) sourceC589) = raw3164 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw3164; decide +kernel
    rw [ha]
    exact (canonical3164 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA589 + difference 4 0) (sourceB589 + difference 0 4) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA589 + difference 4 0) (sourceB589 + difference 0 4) sourceC589) = raw9882 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9882; decide +kernel
    rw [ha]
    exact (canonical9882 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA589 + difference 4 1) (sourceB589 + difference 1 4) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA589 + difference 4 1) (sourceB589 + difference 1 4) sourceC589) = raw9883 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9883; decide +kernel
    rw [ha]
    exact (canonical9883 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA589 + difference 4 2) (sourceB589 + difference 2 4) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA589 + difference 4 2) (sourceB589 + difference 2 4) sourceC589) = raw9884 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9884; decide +kernel
    rw [ha]
    exact (canonical9884 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA589 + difference 4 3) (sourceB589 + difference 3 4) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2388) := by
    have ha : (tripleCharges (sourceA589 + difference 4 3) (sourceB589 + difference 3 4) sourceC589) = raw9885 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9885; decide +kernel
    rw [ha]
    exact (canonical9885 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA589 + difference 4 5) (sourceB589 + difference 5 4) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA589 + difference 4 5) (sourceB589 + difference 5 4) sourceC589) = raw3169 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw3169; decide +kernel
    rw [ha]
    exact (canonical3169 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA589 + difference 5 0) (sourceB589 + difference 0 5) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA589 + difference 5 0) (sourceB589 + difference 0 5) sourceC589) = raw9886 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9886; decide +kernel
    rw [ha]
    exact (canonical9886 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA589 + difference 5 1) (sourceB589 + difference 1 5) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA589 + difference 5 1) (sourceB589 + difference 1 5) sourceC589) = raw9887 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9887; decide +kernel
    rw [ha]
    exact (canonical9887 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA589 + difference 5 2) (sourceB589 + difference 2 5) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2449) := by
    have ha : (tripleCharges (sourceA589 + difference 5 2) (sourceB589 + difference 2 5) sourceC589) = raw9888 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9888; decide +kernel
    rw [ha]
    exact (canonical9888 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA589 + difference 5 3) (sourceB589 + difference 3 5) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA589 + difference 5 3) (sourceB589 + difference 3 5) sourceC589) = raw9889 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9889; decide +kernel
    rw [ha]
    exact (canonical9889 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA589 + difference 5 4) (sourceB589 + difference 4 5) sourceC589) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA589 + difference 5 4) (sourceB589 + difference 4 5) sourceC589) = raw9890 := by
      apply Matrix.ext; unfold tripleCharges sourceA589 sourceB589 sourceC589 difference raw9890; decide +kernel
    rw [ha]
    exact (canonical9890 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA589 sourceB589 sourceC589
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm589, Integer.Sparse.eval]
  linarith only [hs]

def sourceA590 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB590 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC590 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm590 : Integer.Sparse Master := [(Sum.inr 4831, 1), (Sum.inr 4834, 1), (Sum.inr 4835, 1), (Sum.inr 4839, 1), (Sum.inr 4895, 1), (Sum.inr 5220, 1), (Sum.inr 5228, 1), (Sum.inr 5229, 1), (Sum.inr 5233, 1), (Sum.inr 5241, 1), (Sum.inr 5242, 1), (Sum.inr 5244, 1), (Sum.inr 5250, 2), (Sum.inr 5251, 1), (Sum.inr 5258, 2), (Sum.inr 5259, 3), (Sum.inr 5260, 1), (Sum.inr 5266, 2), (Sum.inr 5267, 1), (Sum.inr 5274, 1), (Sum.inr 5275, 1), (Sum.inr 5293, 2), (Sum.inr 5294, 1), (Sum.inr 5309, 1)]

theorem sourceEq590 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm590 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA590 + difference 0 1) (sourceB590 + difference 1 0) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA590 + difference 0 1) (sourceB590 + difference 1 0) sourceC590) = raw9891 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9891; decide +kernel
    rw [ha]
    exact (canonical9891 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA590 + difference 0 2) (sourceB590 + difference 2 0) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA590 + difference 0 2) (sourceB590 + difference 2 0) sourceC590) = raw9892 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9892; decide +kernel
    rw [ha]
    exact (canonical9892 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA590 + difference 0 3) (sourceB590 + difference 3 0) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA590 + difference 0 3) (sourceB590 + difference 3 0) sourceC590) = raw9893 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9893; decide +kernel
    rw [ha]
    exact (canonical9893 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA590 + difference 0 4) (sourceB590 + difference 4 0) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA590 + difference 0 4) (sourceB590 + difference 4 0) sourceC590) = raw9894 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9894; decide +kernel
    rw [ha]
    exact (canonical9894 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA590 + difference 0 5) (sourceB590 + difference 5 0) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA590 + difference 0 5) (sourceB590 + difference 5 0) sourceC590) = raw9895 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9895; decide +kernel
    rw [ha]
    exact (canonical9895 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA590 + difference 1 0) (sourceB590 + difference 0 1) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA590 + difference 1 0) (sourceB590 + difference 0 1) sourceC590) = raw9896 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9896; decide +kernel
    rw [ha]
    exact (canonical9896 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA590 + difference 1 2) (sourceB590 + difference 2 1) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5244) := by
    have ha : (tripleCharges (sourceA590 + difference 1 2) (sourceB590 + difference 2 1) sourceC590) = raw9897 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9897; decide +kernel
    rw [ha]
    exact (canonical9897 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA590 + difference 1 3) (sourceB590 + difference 3 1) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA590 + difference 1 3) (sourceB590 + difference 3 1) sourceC590) = raw9898 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9898; decide +kernel
    rw [ha]
    exact (canonical9898 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA590 + difference 1 4) (sourceB590 + difference 4 1) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA590 + difference 1 4) (sourceB590 + difference 4 1) sourceC590) = raw9899 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9899; decide +kernel
    rw [ha]
    exact (canonical9899 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA590 + difference 1 5) (sourceB590 + difference 5 1) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA590 + difference 1 5) (sourceB590 + difference 5 1) sourceC590) = raw9900 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9900; decide +kernel
    rw [ha]
    exact (canonical9900 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA590 + difference 2 0) (sourceB590 + difference 0 2) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA590 + difference 2 0) (sourceB590 + difference 0 2) sourceC590) = raw9901 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9901; decide +kernel
    rw [ha]
    exact (canonical9901 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA590 + difference 2 1) (sourceB590 + difference 1 2) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA590 + difference 2 1) (sourceB590 + difference 1 2) sourceC590) = raw9902 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9902; decide +kernel
    rw [ha]
    exact (canonical9902 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA590 + difference 2 3) (sourceB590 + difference 3 2) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5220) := by
    have ha : (tripleCharges (sourceA590 + difference 2 3) (sourceB590 + difference 3 2) sourceC590) = raw9903 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9903; decide +kernel
    rw [ha]
    exact (canonical9903 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA590 + difference 2 4) (sourceB590 + difference 4 2) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA590 + difference 2 4) (sourceB590 + difference 4 2) sourceC590) = raw9904 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9904; decide +kernel
    rw [ha]
    exact (canonical9904 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA590 + difference 2 5) (sourceB590 + difference 5 2) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA590 + difference 2 5) (sourceB590 + difference 5 2) sourceC590) = raw9905 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9905; decide +kernel
    rw [ha]
    exact (canonical9905 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA590 + difference 3 0) (sourceB590 + difference 0 3) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA590 + difference 3 0) (sourceB590 + difference 0 3) sourceC590) = raw9906 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9906; decide +kernel
    rw [ha]
    exact (canonical9906 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA590 + difference 3 1) (sourceB590 + difference 1 3) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA590 + difference 3 1) (sourceB590 + difference 1 3) sourceC590) = raw7659 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw7659; decide +kernel
    rw [ha]
    exact (canonical7659 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA590 + difference 3 2) (sourceB590 + difference 2 3) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA590 + difference 3 2) (sourceB590 + difference 2 3) sourceC590) = raw9907 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9907; decide +kernel
    rw [ha]
    exact (canonical9907 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA590 + difference 3 4) (sourceB590 + difference 4 3) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA590 + difference 3 4) (sourceB590 + difference 4 3) sourceC590) = raw7923 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw7923; decide +kernel
    rw [ha]
    exact (canonical7923 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA590 + difference 3 5) (sourceB590 + difference 5 3) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA590 + difference 3 5) (sourceB590 + difference 5 3) sourceC590) = raw7651 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw7651; decide +kernel
    rw [ha]
    exact (canonical7651 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA590 + difference 4 0) (sourceB590 + difference 0 4) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA590 + difference 4 0) (sourceB590 + difference 0 4) sourceC590) = raw9908 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9908; decide +kernel
    rw [ha]
    exact (canonical9908 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA590 + difference 4 1) (sourceB590 + difference 1 4) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA590 + difference 4 1) (sourceB590 + difference 1 4) sourceC590) = raw7658 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw7658; decide +kernel
    rw [ha]
    exact (canonical7658 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA590 + difference 4 2) (sourceB590 + difference 2 4) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5242) := by
    have ha : (tripleCharges (sourceA590 + difference 4 2) (sourceB590 + difference 2 4) sourceC590) = raw9909 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9909; decide +kernel
    rw [ha]
    exact (canonical9909 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA590 + difference 4 3) (sourceB590 + difference 3 4) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA590 + difference 4 3) (sourceB590 + difference 3 4) sourceC590) = raw9910 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9910; decide +kernel
    rw [ha]
    exact (canonical9910 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA590 + difference 4 5) (sourceB590 + difference 5 4) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA590 + difference 4 5) (sourceB590 + difference 5 4) sourceC590) = raw7650 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw7650; decide +kernel
    rw [ha]
    exact (canonical7650 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA590 + difference 5 0) (sourceB590 + difference 0 5) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA590 + difference 5 0) (sourceB590 + difference 0 5) sourceC590) = raw9911 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9911; decide +kernel
    rw [ha]
    exact (canonical9911 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA590 + difference 5 1) (sourceB590 + difference 1 5) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA590 + difference 5 1) (sourceB590 + difference 1 5) sourceC590) = raw9912 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9912; decide +kernel
    rw [ha]
    exact (canonical9912 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA590 + difference 5 2) (sourceB590 + difference 2 5) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA590 + difference 5 2) (sourceB590 + difference 2 5) sourceC590) = raw9913 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9913; decide +kernel
    rw [ha]
    exact (canonical9913 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA590 + difference 5 3) (sourceB590 + difference 3 5) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA590 + difference 5 3) (sourceB590 + difference 3 5) sourceC590) = raw9914 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9914; decide +kernel
    rw [ha]
    exact (canonical9914 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA590 + difference 5 4) (sourceB590 + difference 4 5) sourceC590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA590 + difference 5 4) (sourceB590 + difference 4 5) sourceC590) = raw9670 := by
      apply Matrix.ext; unfold tripleCharges sourceA590 sourceB590 sourceC590 difference raw9670; decide +kernel
    rw [ha]
    exact (canonical9670 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA590 sourceB590 sourceC590
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm590, Integer.Sparse.eval]
  linarith only [hs]

def sourceA591 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB591 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC591 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm591 : Integer.Sparse Master := [(Sum.inr 2191, 1), (Sum.inr 2205, 1), (Sum.inr 2206, 1), (Sum.inr 2216, 1), (Sum.inr 2265, 1), (Sum.inr 2662, 1), (Sum.inr 2672, 1), (Sum.inr 2673, 1), (Sum.inr 2678, 1), (Sum.inr 2694, 1), (Sum.inr 2695, 1), (Sum.inr 2698, 1), (Sum.inr 2709, 1), (Sum.inr 2710, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 2), (Sum.inr 2724, 1), (Sum.inr 2731, 1), (Sum.inr 2732, 1), (Sum.inr 2742, 1), (Sum.inr 2743, 1), (Sum.inr 2767, 1), (Sum.inr 2768, 1), (Sum.inr 2787, 1), (Sum.inr 3039, 1), (Sum.inr 3065, 1), (Sum.inr 3088, 1), (Sum.inr 3089, 1), (Sum.inr 3102, 1)]

theorem sourceEq591 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm591 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA591 + difference 0 1) (sourceB591 + difference 1 0) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA591 + difference 0 1) (sourceB591 + difference 1 0) sourceC591) = raw9915 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9915; decide +kernel
    rw [ha]
    exact (canonical9915 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA591 + difference 0 2) (sourceB591 + difference 2 0) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA591 + difference 0 2) (sourceB591 + difference 2 0) sourceC591) = raw9916 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9916; decide +kernel
    rw [ha]
    exact (canonical9916 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA591 + difference 0 3) (sourceB591 + difference 3 0) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA591 + difference 0 3) (sourceB591 + difference 3 0) sourceC591) = raw9917 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9917; decide +kernel
    rw [ha]
    exact (canonical9917 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA591 + difference 0 4) (sourceB591 + difference 4 0) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA591 + difference 0 4) (sourceB591 + difference 4 0) sourceC591) = raw9918 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9918; decide +kernel
    rw [ha]
    exact (canonical9918 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA591 + difference 0 5) (sourceB591 + difference 5 0) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA591 + difference 0 5) (sourceB591 + difference 5 0) sourceC591) = raw9919 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9919; decide +kernel
    rw [ha]
    exact (canonical9919 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA591 + difference 1 0) (sourceB591 + difference 0 1) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA591 + difference 1 0) (sourceB591 + difference 0 1) sourceC591) = raw9920 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9920; decide +kernel
    rw [ha]
    exact (canonical9920 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA591 + difference 1 2) (sourceB591 + difference 2 1) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2698) := by
    have ha : (tripleCharges (sourceA591 + difference 1 2) (sourceB591 + difference 2 1) sourceC591) = raw9921 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9921; decide +kernel
    rw [ha]
    exact (canonical9921 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA591 + difference 1 3) (sourceB591 + difference 3 1) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA591 + difference 1 3) (sourceB591 + difference 3 1) sourceC591) = raw9922 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9922; decide +kernel
    rw [ha]
    exact (canonical9922 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA591 + difference 1 4) (sourceB591 + difference 4 1) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA591 + difference 1 4) (sourceB591 + difference 4 1) sourceC591) = raw9923 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9923; decide +kernel
    rw [ha]
    exact (canonical9923 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA591 + difference 1 5) (sourceB591 + difference 5 1) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA591 + difference 1 5) (sourceB591 + difference 5 1) sourceC591) = raw9924 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9924; decide +kernel
    rw [ha]
    exact (canonical9924 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA591 + difference 2 0) (sourceB591 + difference 0 2) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA591 + difference 2 0) (sourceB591 + difference 0 2) sourceC591) = raw9925 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9925; decide +kernel
    rw [ha]
    exact (canonical9925 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA591 + difference 2 1) (sourceB591 + difference 1 2) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA591 + difference 2 1) (sourceB591 + difference 1 2) sourceC591) = raw9926 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9926; decide +kernel
    rw [ha]
    exact (canonical9926 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA591 + difference 2 3) (sourceB591 + difference 3 2) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA591 + difference 2 3) (sourceB591 + difference 3 2) sourceC591) = raw9927 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9927; decide +kernel
    rw [ha]
    exact (canonical9927 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA591 + difference 2 4) (sourceB591 + difference 4 2) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA591 + difference 2 4) (sourceB591 + difference 4 2) sourceC591) = raw9928 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9928; decide +kernel
    rw [ha]
    exact (canonical9928 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA591 + difference 2 5) (sourceB591 + difference 5 2) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA591 + difference 2 5) (sourceB591 + difference 5 2) sourceC591) = raw9929 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9929; decide +kernel
    rw [ha]
    exact (canonical9929 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA591 + difference 3 0) (sourceB591 + difference 0 3) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA591 + difference 3 0) (sourceB591 + difference 0 3) sourceC591) = raw9930 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9930; decide +kernel
    rw [ha]
    exact (canonical9930 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA591 + difference 3 1) (sourceB591 + difference 1 3) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2787) := by
    have ha : (tripleCharges (sourceA591 + difference 3 1) (sourceB591 + difference 1 3) sourceC591) = raw7675 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw7675; decide +kernel
    rw [ha]
    exact (canonical7675 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA591 + difference 3 2) (sourceB591 + difference 2 3) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA591 + difference 3 2) (sourceB591 + difference 2 3) sourceC591) = raw9931 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9931; decide +kernel
    rw [ha]
    exact (canonical9931 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA591 + difference 3 4) (sourceB591 + difference 4 3) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA591 + difference 3 4) (sourceB591 + difference 4 3) sourceC591) = raw7936 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw7936; decide +kernel
    rw [ha]
    exact (canonical7936 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA591 + difference 3 5) (sourceB591 + difference 5 3) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA591 + difference 3 5) (sourceB591 + difference 5 3) sourceC591) = raw7667 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw7667; decide +kernel
    rw [ha]
    exact (canonical7667 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA591 + difference 4 0) (sourceB591 + difference 0 4) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA591 + difference 4 0) (sourceB591 + difference 0 4) sourceC591) = raw9932 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9932; decide +kernel
    rw [ha]
    exact (canonical9932 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA591 + difference 4 1) (sourceB591 + difference 1 4) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA591 + difference 4 1) (sourceB591 + difference 1 4) sourceC591) = raw7674 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw7674; decide +kernel
    rw [ha]
    exact (canonical7674 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA591 + difference 4 2) (sourceB591 + difference 2 4) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2695) := by
    have ha : (tripleCharges (sourceA591 + difference 4 2) (sourceB591 + difference 2 4) sourceC591) = raw9933 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9933; decide +kernel
    rw [ha]
    exact (canonical9933 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA591 + difference 4 3) (sourceB591 + difference 3 4) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA591 + difference 4 3) (sourceB591 + difference 3 4) sourceC591) = raw9934 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9934; decide +kernel
    rw [ha]
    exact (canonical9934 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA591 + difference 4 5) (sourceB591 + difference 5 4) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA591 + difference 4 5) (sourceB591 + difference 5 4) sourceC591) = raw7666 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw7666; decide +kernel
    rw [ha]
    exact (canonical7666 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA591 + difference 5 0) (sourceB591 + difference 0 5) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA591 + difference 5 0) (sourceB591 + difference 0 5) sourceC591) = raw9935 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9935; decide +kernel
    rw [ha]
    exact (canonical9935 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA591 + difference 5 1) (sourceB591 + difference 1 5) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA591 + difference 5 1) (sourceB591 + difference 1 5) sourceC591) = raw9936 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9936; decide +kernel
    rw [ha]
    exact (canonical9936 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA591 + difference 5 2) (sourceB591 + difference 2 5) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA591 + difference 5 2) (sourceB591 + difference 2 5) sourceC591) = raw9937 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9937; decide +kernel
    rw [ha]
    exact (canonical9937 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA591 + difference 5 3) (sourceB591 + difference 3 5) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA591 + difference 5 3) (sourceB591 + difference 3 5) sourceC591) = raw9938 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9938; decide +kernel
    rw [ha]
    exact (canonical9938 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA591 + difference 5 4) (sourceB591 + difference 4 5) sourceC591) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA591 + difference 5 4) (sourceB591 + difference 4 5) sourceC591) = raw9694 := by
      apply Matrix.ext; unfold tripleCharges sourceA591 sourceB591 sourceC591 difference raw9694; decide +kernel
    rw [ha]
    exact (canonical9694 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA591 sourceB591 sourceC591
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm591, Integer.Sparse.eval]
  linarith only [hs]

def sourceA592 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB592 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC592 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm592 : Integer.Sparse Master := [(Sum.inr 2709, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 2731, 1), (Sum.inr 2767, 1), (Sum.inr 3029, 1), (Sum.inr 3038, 1), (Sum.inr 3039, 1), (Sum.inr 3044, 1), (Sum.inr 3064, 1), (Sum.inr 3065, 1), (Sum.inr 3068, 1), (Sum.inr 3080, 1), (Sum.inr 3081, 1), (Sum.inr 3086, 1), (Sum.inr 3088, 2), (Sum.inr 3089, 1), (Sum.inr 3092, 1), (Sum.inr 3094, 1), (Sum.inr 3101, 1), (Sum.inr 3102, 1), (Sum.inr 3110, 1), (Sum.inr 3112, 1), (Sum.inr 3123, 1), (Sum.inr 3209, 1), (Sum.inr 3210, 1), (Sum.inr 3211, 1), (Sum.inr 3214, 1), (Sum.inr 3229, 1)]

theorem sourceEq592 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm592 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA592 + difference 0 1) (sourceB592 + difference 1 0) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA592 + difference 0 1) (sourceB592 + difference 1 0) sourceC592) = raw9939 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9939; decide +kernel
    rw [ha]
    exact (canonical9939 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA592 + difference 0 2) (sourceB592 + difference 2 0) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA592 + difference 0 2) (sourceB592 + difference 2 0) sourceC592) = raw9940 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9940; decide +kernel
    rw [ha]
    exact (canonical9940 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA592 + difference 0 3) (sourceB592 + difference 3 0) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA592 + difference 0 3) (sourceB592 + difference 3 0) sourceC592) = raw9941 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9941; decide +kernel
    rw [ha]
    exact (canonical9941 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA592 + difference 0 4) (sourceB592 + difference 4 0) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA592 + difference 0 4) (sourceB592 + difference 4 0) sourceC592) = raw9942 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9942; decide +kernel
    rw [ha]
    exact (canonical9942 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA592 + difference 0 5) (sourceB592 + difference 5 0) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA592 + difference 0 5) (sourceB592 + difference 5 0) sourceC592) = raw9943 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9943; decide +kernel
    rw [ha]
    exact (canonical9943 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA592 + difference 1 0) (sourceB592 + difference 0 1) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3210) := by
    have ha : (tripleCharges (sourceA592 + difference 1 0) (sourceB592 + difference 0 1) sourceC592) = raw9944 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9944; decide +kernel
    rw [ha]
    exact (canonical9944 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA592 + difference 1 2) (sourceB592 + difference 2 1) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3029) := by
    have ha : (tripleCharges (sourceA592 + difference 1 2) (sourceB592 + difference 2 1) sourceC592) = raw9945 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9945; decide +kernel
    rw [ha]
    exact (canonical9945 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA592 + difference 1 3) (sourceB592 + difference 3 1) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3044) := by
    have ha : (tripleCharges (sourceA592 + difference 1 3) (sourceB592 + difference 3 1) sourceC592) = raw9946 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9946; decide +kernel
    rw [ha]
    exact (canonical9946 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA592 + difference 1 4) (sourceB592 + difference 4 1) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA592 + difference 1 4) (sourceB592 + difference 4 1) sourceC592) = raw9947 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9947; decide +kernel
    rw [ha]
    exact (canonical9947 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA592 + difference 1 5) (sourceB592 + difference 5 1) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA592 + difference 1 5) (sourceB592 + difference 5 1) sourceC592) = raw9948 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9948; decide +kernel
    rw [ha]
    exact (canonical9948 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA592 + difference 2 0) (sourceB592 + difference 0 2) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3209) := by
    have ha : (tripleCharges (sourceA592 + difference 2 0) (sourceB592 + difference 0 2) sourceC592) = raw9949 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9949; decide +kernel
    rw [ha]
    exact (canonical9949 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA592 + difference 2 1) (sourceB592 + difference 1 2) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA592 + difference 2 1) (sourceB592 + difference 1 2) sourceC592) = raw9950 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9950; decide +kernel
    rw [ha]
    exact (canonical9950 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA592 + difference 2 3) (sourceB592 + difference 3 2) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3068) := by
    have ha : (tripleCharges (sourceA592 + difference 2 3) (sourceB592 + difference 3 2) sourceC592) = raw9951 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9951; decide +kernel
    rw [ha]
    exact (canonical9951 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA592 + difference 2 4) (sourceB592 + difference 4 2) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA592 + difference 2 4) (sourceB592 + difference 4 2) sourceC592) = raw9952 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9952; decide +kernel
    rw [ha]
    exact (canonical9952 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA592 + difference 2 5) (sourceB592 + difference 5 2) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA592 + difference 2 5) (sourceB592 + difference 5 2) sourceC592) = raw9953 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9953; decide +kernel
    rw [ha]
    exact (canonical9953 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA592 + difference 3 0) (sourceB592 + difference 0 3) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA592 + difference 3 0) (sourceB592 + difference 0 3) sourceC592) = raw9954 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9954; decide +kernel
    rw [ha]
    exact (canonical9954 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA592 + difference 3 1) (sourceB592 + difference 1 3) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3123) := by
    have ha : (tripleCharges (sourceA592 + difference 3 1) (sourceB592 + difference 1 3) sourceC592) = raw7691 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw7691; decide +kernel
    rw [ha]
    exact (canonical7691 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA592 + difference 3 2) (sourceB592 + difference 2 3) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA592 + difference 3 2) (sourceB592 + difference 2 3) sourceC592) = raw9955 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9955; decide +kernel
    rw [ha]
    exact (canonical9955 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA592 + difference 3 4) (sourceB592 + difference 4 3) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA592 + difference 3 4) (sourceB592 + difference 4 3) sourceC592) = raw7949 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw7949; decide +kernel
    rw [ha]
    exact (canonical7949 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA592 + difference 3 5) (sourceB592 + difference 5 3) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA592 + difference 3 5) (sourceB592 + difference 5 3) sourceC592) = raw7683 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw7683; decide +kernel
    rw [ha]
    exact (canonical7683 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA592 + difference 4 0) (sourceB592 + difference 0 4) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3211) := by
    have ha : (tripleCharges (sourceA592 + difference 4 0) (sourceB592 + difference 0 4) sourceC592) = raw9956 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9956; decide +kernel
    rw [ha]
    exact (canonical9956 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA592 + difference 4 1) (sourceB592 + difference 1 4) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA592 + difference 4 1) (sourceB592 + difference 1 4) sourceC592) = raw7690 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw7690; decide +kernel
    rw [ha]
    exact (canonical7690 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA592 + difference 4 2) (sourceB592 + difference 2 4) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3080) := by
    have ha : (tripleCharges (sourceA592 + difference 4 2) (sourceB592 + difference 2 4) sourceC592) = raw9957 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9957; decide +kernel
    rw [ha]
    exact (canonical9957 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA592 + difference 4 3) (sourceB592 + difference 3 4) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA592 + difference 4 3) (sourceB592 + difference 3 4) sourceC592) = raw9958 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9958; decide +kernel
    rw [ha]
    exact (canonical9958 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA592 + difference 4 5) (sourceB592 + difference 5 4) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA592 + difference 4 5) (sourceB592 + difference 5 4) sourceC592) = raw7682 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw7682; decide +kernel
    rw [ha]
    exact (canonical7682 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA592 + difference 5 0) (sourceB592 + difference 0 5) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3214) := by
    have ha : (tripleCharges (sourceA592 + difference 5 0) (sourceB592 + difference 0 5) sourceC592) = raw9959 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9959; decide +kernel
    rw [ha]
    exact (canonical9959 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA592 + difference 5 1) (sourceB592 + difference 1 5) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA592 + difference 5 1) (sourceB592 + difference 1 5) sourceC592) = raw9960 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9960; decide +kernel
    rw [ha]
    exact (canonical9960 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA592 + difference 5 2) (sourceB592 + difference 2 5) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3081) := by
    have ha : (tripleCharges (sourceA592 + difference 5 2) (sourceB592 + difference 2 5) sourceC592) = raw9961 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9961; decide +kernel
    rw [ha]
    exact (canonical9961 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA592 + difference 5 3) (sourceB592 + difference 3 5) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3094) := by
    have ha : (tripleCharges (sourceA592 + difference 5 3) (sourceB592 + difference 3 5) sourceC592) = raw9962 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9962; decide +kernel
    rw [ha]
    exact (canonical9962 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA592 + difference 5 4) (sourceB592 + difference 4 5) sourceC592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA592 + difference 5 4) (sourceB592 + difference 4 5) sourceC592) = raw9718 := by
      apply Matrix.ext; unfold tripleCharges sourceA592 sourceB592 sourceC592 difference raw9718; decide +kernel
    rw [ha]
    exact (canonical9718 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA592 sourceB592 sourceC592
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm592, Integer.Sparse.eval]
  linarith only [hs]

def sourceA593 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB593 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC593 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm593 : Integer.Sparse Master := [(Sum.inr 2051, 1), (Sum.inr 2053, 1), (Sum.inr 2054, 1), (Sum.inr 2058, 1), (Sum.inr 2291, 1), (Sum.inr 3544, 1), (Sum.inr 4084, -1)]

theorem sourceEq593 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm593 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA593 + difference 0 0) (sourceB593 + difference 0 0) sourceC593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA593 + difference 0 0) (sourceB593 + difference 0 0) sourceC593) = raw9963 := by
      apply Matrix.ext; unfold tripleCharges sourceA593 sourceB593 sourceC593 difference raw9963; decide +kernel
    rw [ha]
    exact (canonical9963 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA593 + difference 1 0) (sourceB593 + difference 0 1) sourceC593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA593 + difference 1 0) (sourceB593 + difference 0 1) sourceC593) = raw9964 := by
      apply Matrix.ext; unfold tripleCharges sourceA593 sourceB593 sourceC593 difference raw9964; decide +kernel
    rw [ha]
    exact (canonical9964 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA593 + difference 2 0) (sourceB593 + difference 0 2) sourceC593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2051) := by
    have ha : (tripleCharges (sourceA593 + difference 2 0) (sourceB593 + difference 0 2) sourceC593) = raw9965 := by
      apply Matrix.ext; unfold tripleCharges sourceA593 sourceB593 sourceC593 difference raw9965; decide +kernel
    rw [ha]
    exact (canonical9965 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA593 + difference 3 0) (sourceB593 + difference 0 3) sourceC593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA593 + difference 3 0) (sourceB593 + difference 0 3) sourceC593) = raw9966 := by
      apply Matrix.ext; unfold tripleCharges sourceA593 sourceB593 sourceC593 difference raw9966; decide +kernel
    rw [ha]
    exact (canonical9966 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA593 + difference 4 0) (sourceB593 + difference 0 4) sourceC593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA593 + difference 4 0) (sourceB593 + difference 0 4) sourceC593) = raw9967 := by
      apply Matrix.ext; unfold tripleCharges sourceA593 sourceB593 sourceC593 difference raw9967; decide +kernel
    rw [ha]
    exact (canonical9967 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA593 + difference 5 0) (sourceB593 + difference 0 5) sourceC593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2053) := by
    have ha : (tripleCharges (sourceA593 + difference 5 0) (sourceB593 + difference 0 5) sourceC593) = raw9968 := by
      apply Matrix.ext; unfold tripleCharges sourceA593 sourceB593 sourceC593 difference raw9968; decide +kernel
    rw [ha]
    exact (canonical9968 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA593 + sourceB593) sourceC593) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA593 + sourceB593) sourceC593) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA593 sourceB593 sourceC593 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA593 sourceB593 sourceC593
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm593, Integer.Sparse.eval]
  linarith only [hs]

def sourceA594 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB594 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC594 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceForm594 : Integer.Sparse Master := [(Sum.inr 4589, 1), (Sum.inr 4591, 1), (Sum.inr 4592, 1), (Sum.inr 4602, 1), (Sum.inr 4607, 1), (Sum.inr 5072, 1), (Sum.inr 5075, 1), (Sum.inr 5080, 1), (Sum.inr 5101, 1), (Sum.inr 5127, 1), (Sum.inr 5129, 1), (Sum.inr 5134, 1), (Sum.inr 5144, 1), (Sum.inr 5147, 1), (Sum.inr 5184, 1), (Sum.inr 5188, 1), (Sum.inr 5198, 1), (Sum.inr 5256, 1), (Sum.inr 5258, 1), (Sum.inr 5260, 1), (Sum.inr 5261, 1), (Sum.inr 5271, 1), (Sum.inr 5274, 1), (Sum.inr 5289, 1), (Sum.inr 5291, 1), (Sum.inr 5409, 1), (Sum.inr 5423, 1), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5441, 1)]

theorem sourceEq594 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm594 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA594 + difference 0 1) (sourceB594 + difference 1 0) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA594 + difference 0 1) (sourceB594 + difference 1 0) sourceC594) = raw9969 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9969; decide +kernel
    rw [ha]
    exact (canonical9969 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA594 + difference 0 2) (sourceB594 + difference 2 0) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA594 + difference 0 2) (sourceB594 + difference 2 0) sourceC594) = raw9970 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9970; decide +kernel
    rw [ha]
    exact (canonical9970 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA594 + difference 0 3) (sourceB594 + difference 3 0) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA594 + difference 0 3) (sourceB594 + difference 3 0) sourceC594) = raw9971 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9971; decide +kernel
    rw [ha]
    exact (canonical9971 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA594 + difference 0 4) (sourceB594 + difference 4 0) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA594 + difference 0 4) (sourceB594 + difference 4 0) sourceC594) = raw9972 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9972; decide +kernel
    rw [ha]
    exact (canonical9972 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA594 + difference 0 5) (sourceB594 + difference 5 0) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA594 + difference 0 5) (sourceB594 + difference 5 0) sourceC594) = raw9973 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9973; decide +kernel
    rw [ha]
    exact (canonical9973 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA594 + difference 1 0) (sourceB594 + difference 0 1) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA594 + difference 1 0) (sourceB594 + difference 0 1) sourceC594) = raw9974 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9974; decide +kernel
    rw [ha]
    exact (canonical9974 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA594 + difference 1 2) (sourceB594 + difference 2 1) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA594 + difference 1 2) (sourceB594 + difference 2 1) sourceC594) = raw9975 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9975; decide +kernel
    rw [ha]
    exact (canonical9975 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA594 + difference 1 3) (sourceB594 + difference 3 1) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA594 + difference 1 3) (sourceB594 + difference 3 1) sourceC594) = raw9976 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9976; decide +kernel
    rw [ha]
    exact (canonical9976 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA594 + difference 1 4) (sourceB594 + difference 4 1) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA594 + difference 1 4) (sourceB594 + difference 4 1) sourceC594) = raw9977 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9977; decide +kernel
    rw [ha]
    exact (canonical9977 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA594 + difference 1 5) (sourceB594 + difference 5 1) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA594 + difference 1 5) (sourceB594 + difference 5 1) sourceC594) = raw9978 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9978; decide +kernel
    rw [ha]
    exact (canonical9978 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA594 + difference 2 0) (sourceB594 + difference 0 2) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA594 + difference 2 0) (sourceB594 + difference 0 2) sourceC594) = raw9979 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9979; decide +kernel
    rw [ha]
    exact (canonical9979 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA594 + difference 2 1) (sourceB594 + difference 1 2) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA594 + difference 2 1) (sourceB594 + difference 1 2) sourceC594) = raw9980 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9980; decide +kernel
    rw [ha]
    exact (canonical9980 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA594 + difference 2 3) (sourceB594 + difference 3 2) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA594 + difference 2 3) (sourceB594 + difference 3 2) sourceC594) = raw9981 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9981; decide +kernel
    rw [ha]
    exact (canonical9981 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA594 + difference 2 4) (sourceB594 + difference 4 2) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA594 + difference 2 4) (sourceB594 + difference 4 2) sourceC594) = raw9982 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9982; decide +kernel
    rw [ha]
    exact (canonical9982 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA594 + difference 2 5) (sourceB594 + difference 5 2) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA594 + difference 2 5) (sourceB594 + difference 5 2) sourceC594) = raw9983 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9983; decide +kernel
    rw [ha]
    exact (canonical9983 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA594 + difference 3 0) (sourceB594 + difference 0 3) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA594 + difference 3 0) (sourceB594 + difference 0 3) sourceC594) = raw9984 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9984; decide +kernel
    rw [ha]
    exact (canonical9984 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA594 + difference 3 1) (sourceB594 + difference 1 3) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA594 + difference 3 1) (sourceB594 + difference 1 3) sourceC594) = raw9985 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9985; decide +kernel
    rw [ha]
    exact (canonical9985 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA594 + difference 3 2) (sourceB594 + difference 2 3) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA594 + difference 3 2) (sourceB594 + difference 2 3) sourceC594) = raw9986 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9986; decide +kernel
    rw [ha]
    exact (canonical9986 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA594 + difference 3 4) (sourceB594 + difference 4 3) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA594 + difference 3 4) (sourceB594 + difference 4 3) sourceC594) = raw9987 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9987; decide +kernel
    rw [ha]
    exact (canonical9987 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA594 + difference 3 5) (sourceB594 + difference 5 3) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA594 + difference 3 5) (sourceB594 + difference 5 3) sourceC594) = raw9988 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9988; decide +kernel
    rw [ha]
    exact (canonical9988 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA594 + difference 4 0) (sourceB594 + difference 0 4) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA594 + difference 4 0) (sourceB594 + difference 0 4) sourceC594) = raw9989 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9989; decide +kernel
    rw [ha]
    exact (canonical9989 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA594 + difference 4 1) (sourceB594 + difference 1 4) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA594 + difference 4 1) (sourceB594 + difference 1 4) sourceC594) = raw9990 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9990; decide +kernel
    rw [ha]
    exact (canonical9990 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA594 + difference 4 2) (sourceB594 + difference 2 4) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA594 + difference 4 2) (sourceB594 + difference 2 4) sourceC594) = raw9991 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9991; decide +kernel
    rw [ha]
    exact (canonical9991 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA594 + difference 4 3) (sourceB594 + difference 3 4) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA594 + difference 4 3) (sourceB594 + difference 3 4) sourceC594) = raw9992 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9992; decide +kernel
    rw [ha]
    exact (canonical9992 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA594 + difference 4 5) (sourceB594 + difference 5 4) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA594 + difference 4 5) (sourceB594 + difference 5 4) sourceC594) = raw9993 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9993; decide +kernel
    rw [ha]
    exact (canonical9993 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA594 + difference 5 0) (sourceB594 + difference 0 5) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA594 + difference 5 0) (sourceB594 + difference 0 5) sourceC594) = raw9994 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9994; decide +kernel
    rw [ha]
    exact (canonical9994 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA594 + difference 5 1) (sourceB594 + difference 1 5) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA594 + difference 5 1) (sourceB594 + difference 1 5) sourceC594) = raw9995 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9995; decide +kernel
    rw [ha]
    exact (canonical9995 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA594 + difference 5 2) (sourceB594 + difference 2 5) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5127) := by
    have ha : (tripleCharges (sourceA594 + difference 5 2) (sourceB594 + difference 2 5) sourceC594) = raw9996 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9996; decide +kernel
    rw [ha]
    exact (canonical9996 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA594 + difference 5 3) (sourceB594 + difference 3 5) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA594 + difference 5 3) (sourceB594 + difference 3 5) sourceC594) = raw9997 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9997; decide +kernel
    rw [ha]
    exact (canonical9997 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA594 + difference 5 4) (sourceB594 + difference 4 5) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA594 + difference 5 4) (sourceB594 + difference 4 5) sourceC594) = raw9998 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9998; decide +kernel
    rw [ha]
    exact (canonical9998 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA594 sourceB594 sourceC594
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm594, Integer.Sparse.eval]
  linarith only [hs]

def sourceA595 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB595 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC595 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceForm595 : Integer.Sparse Master := [(Sum.inr 1216, 1), (Sum.inr 1217, 1), (Sum.inr 1219, 1), (Sum.inr 1241, 1), (Sum.inr 1267, 1), (Sum.inr 2864, 1), (Sum.inr 2865, 1), (Sum.inr 2867, 1), (Sum.inr 2885, 1), (Sum.inr 2914, 1), (Sum.inr 2916, 1), (Sum.inr 2928, 1), (Sum.inr 2937, 1), (Sum.inr 2939, 1), (Sum.inr 2988, 1), (Sum.inr 2990, 1), (Sum.inr 3001, 1), (Sum.inr 3085, 1), (Sum.inr 3086, 1), (Sum.inr 3089, 1), (Sum.inr 3090, 1), (Sum.inr 3097, 1), (Sum.inr 3103, 1), (Sum.inr 3109, 1), (Sum.inr 3112, 1), (Sum.inr 3982, 1), (Sum.inr 4027, 1), (Sum.inr 4032, 1), (Sum.inr 4035, 1), (Sum.inr 4037, 1)]

theorem sourceEq595 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm595 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA595 + difference 0 1) (sourceB595 + difference 1 0) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4027) := by
    have ha : (tripleCharges (sourceA595 + difference 0 1) (sourceB595 + difference 1 0) sourceC595) = raw9999 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw9999; decide +kernel
    rw [ha]
    exact (canonical9999 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA595 + difference 0 2) (sourceB595 + difference 2 0) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4032) := by
    have ha : (tripleCharges (sourceA595 + difference 0 2) (sourceB595 + difference 2 0) sourceC595) = raw10000 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10000; decide +kernel
    rw [ha]
    exact (canonical10000 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA595 + difference 0 3) (sourceB595 + difference 3 0) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4035) := by
    have ha : (tripleCharges (sourceA595 + difference 0 3) (sourceB595 + difference 3 0) sourceC595) = raw10001 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10001; decide +kernel
    rw [ha]
    exact (canonical10001 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA595 + difference 0 4) (sourceB595 + difference 4 0) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4037) := by
    have ha : (tripleCharges (sourceA595 + difference 0 4) (sourceB595 + difference 4 0) sourceC595) = raw10002 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10002; decide +kernel
    rw [ha]
    exact (canonical10002 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA595 + difference 0 5) (sourceB595 + difference 5 0) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA595 + difference 0 5) (sourceB595 + difference 5 0) sourceC595) = raw10003 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10003; decide +kernel
    rw [ha]
    exact (canonical10003 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA595 + difference 1 0) (sourceB595 + difference 0 1) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1267) := by
    have ha : (tripleCharges (sourceA595 + difference 1 0) (sourceB595 + difference 0 1) sourceC595) = raw10004 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10004; decide +kernel
    rw [ha]
    exact (canonical10004 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA595 + difference 1 2) (sourceB595 + difference 2 1) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2937) := by
    have ha : (tripleCharges (sourceA595 + difference 1 2) (sourceB595 + difference 2 1) sourceC595) = raw10005 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10005; decide +kernel
    rw [ha]
    exact (canonical10005 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA595 + difference 1 3) (sourceB595 + difference 3 1) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3001) := by
    have ha : (tripleCharges (sourceA595 + difference 1 3) (sourceB595 + difference 3 1) sourceC595) = raw10006 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10006; decide +kernel
    rw [ha]
    exact (canonical10006 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA595 + difference 1 4) (sourceB595 + difference 4 1) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA595 + difference 1 4) (sourceB595 + difference 4 1) sourceC595) = raw10007 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10007; decide +kernel
    rw [ha]
    exact (canonical10007 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA595 + difference 1 5) (sourceB595 + difference 5 1) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA595 + difference 1 5) (sourceB595 + difference 5 1) sourceC595) = raw10008 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10008; decide +kernel
    rw [ha]
    exact (canonical10008 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA595 + difference 2 0) (sourceB595 + difference 0 2) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA595 + difference 2 0) (sourceB595 + difference 0 2) sourceC595) = raw10009 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10009; decide +kernel
    rw [ha]
    exact (canonical10009 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA595 + difference 2 1) (sourceB595 + difference 1 2) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2864) := by
    have ha : (tripleCharges (sourceA595 + difference 2 1) (sourceB595 + difference 1 2) sourceC595) = raw10010 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10010; decide +kernel
    rw [ha]
    exact (canonical10010 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA595 + difference 2 3) (sourceB595 + difference 3 2) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2988) := by
    have ha : (tripleCharges (sourceA595 + difference 2 3) (sourceB595 + difference 3 2) sourceC595) = raw10011 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10011; decide +kernel
    rw [ha]
    exact (canonical10011 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA595 + difference 2 4) (sourceB595 + difference 4 2) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA595 + difference 2 4) (sourceB595 + difference 4 2) sourceC595) = raw10012 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10012; decide +kernel
    rw [ha]
    exact (canonical10012 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA595 + difference 2 5) (sourceB595 + difference 5 2) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA595 + difference 2 5) (sourceB595 + difference 5 2) sourceC595) = raw10013 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10013; decide +kernel
    rw [ha]
    exact (canonical10013 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA595 + difference 3 0) (sourceB595 + difference 0 3) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA595 + difference 3 0) (sourceB595 + difference 0 3) sourceC595) = raw10014 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10014; decide +kernel
    rw [ha]
    exact (canonical10014 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA595 + difference 3 1) (sourceB595 + difference 1 3) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2885) := by
    have ha : (tripleCharges (sourceA595 + difference 3 1) (sourceB595 + difference 1 3) sourceC595) = raw10015 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10015; decide +kernel
    rw [ha]
    exact (canonical10015 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA595 + difference 3 2) (sourceB595 + difference 2 3) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2928) := by
    have ha : (tripleCharges (sourceA595 + difference 3 2) (sourceB595 + difference 2 3) sourceC595) = raw10016 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10016; decide +kernel
    rw [ha]
    exact (canonical10016 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA595 + difference 3 4) (sourceB595 + difference 4 3) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA595 + difference 3 4) (sourceB595 + difference 4 3) sourceC595) = raw10017 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10017; decide +kernel
    rw [ha]
    exact (canonical10017 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA595 + difference 3 5) (sourceB595 + difference 5 3) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA595 + difference 3 5) (sourceB595 + difference 5 3) sourceC595) = raw10018 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10018; decide +kernel
    rw [ha]
    exact (canonical10018 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA595 + difference 4 0) (sourceB595 + difference 0 4) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA595 + difference 4 0) (sourceB595 + difference 0 4) sourceC595) = raw10019 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10019; decide +kernel
    rw [ha]
    exact (canonical10019 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA595 + difference 4 1) (sourceB595 + difference 1 4) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA595 + difference 4 1) (sourceB595 + difference 1 4) sourceC595) = raw10020 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10020; decide +kernel
    rw [ha]
    exact (canonical10020 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA595 + difference 4 2) (sourceB595 + difference 2 4) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA595 + difference 4 2) (sourceB595 + difference 2 4) sourceC595) = raw10021 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10021; decide +kernel
    rw [ha]
    exact (canonical10021 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA595 + difference 4 3) (sourceB595 + difference 3 4) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2990) := by
    have ha : (tripleCharges (sourceA595 + difference 4 3) (sourceB595 + difference 3 4) sourceC595) = raw10022 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10022; decide +kernel
    rw [ha]
    exact (canonical10022 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA595 + difference 4 5) (sourceB595 + difference 5 4) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA595 + difference 4 5) (sourceB595 + difference 5 4) sourceC595) = raw10023 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10023; decide +kernel
    rw [ha]
    exact (canonical10023 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA595 + difference 5 0) (sourceB595 + difference 0 5) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA595 + difference 5 0) (sourceB595 + difference 0 5) sourceC595) = raw10024 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10024; decide +kernel
    rw [ha]
    exact (canonical10024 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA595 + difference 5 1) (sourceB595 + difference 1 5) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA595 + difference 5 1) (sourceB595 + difference 1 5) sourceC595) = raw10025 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10025; decide +kernel
    rw [ha]
    exact (canonical10025 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA595 + difference 5 2) (sourceB595 + difference 2 5) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2914) := by
    have ha : (tripleCharges (sourceA595 + difference 5 2) (sourceB595 + difference 2 5) sourceC595) = raw10026 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10026; decide +kernel
    rw [ha]
    exact (canonical10026 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA595 + difference 5 3) (sourceB595 + difference 3 5) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2939) := by
    have ha : (tripleCharges (sourceA595 + difference 5 3) (sourceB595 + difference 3 5) sourceC595) = raw10027 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10027; decide +kernel
    rw [ha]
    exact (canonical10027 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA595 + difference 5 4) (sourceB595 + difference 4 5) sourceC595) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA595 + difference 5 4) (sourceB595 + difference 4 5) sourceC595) = raw10028 := by
      apply Matrix.ext; unfold tripleCharges sourceA595 sourceB595 sourceC595 difference raw10028; decide +kernel
    rw [ha]
    exact (canonical10028 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA595 sourceB595 sourceC595
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm595, Integer.Sparse.eval]
  linarith only [hs]

def sourceA596 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB596 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC596 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceForm596 : Integer.Sparse Master := [(Sum.inr 3288, 1), (Sum.inr 3291, 1), (Sum.inr 3293, 1), (Sum.inr 3295, 1), (Sum.inr 3296, 1), (Sum.inr 3459, 1), (Sum.inr 3468, 1), (Sum.inr 3470, 1), (Sum.inr 3478, 1), (Sum.inr 3513, 1), (Sum.inr 3514, 1), (Sum.inr 3516, 1), (Sum.inr 3524, 1), (Sum.inr 3525, 1), (Sum.inr 3530, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1), (Sum.inr 3538, 1), (Sum.inr 3540, 1), (Sum.inr 3545, 1), (Sum.inr 3547, 1), (Sum.inr 3557, 1), (Sum.inr 3570, 1), (Sum.inr 3572, 1), (Sum.inr 3582, 1), (Sum.inr 3807, 1), (Sum.inr 3837, 1), (Sum.inr 3850, 1), (Sum.inr 3852, 1), (Sum.inr 3860, 1)]

theorem sourceEq596 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm596 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA596 + difference 0 1) (sourceB596 + difference 1 0) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA596 + difference 0 1) (sourceB596 + difference 1 0) sourceC596) = raw10029 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10029; decide +kernel
    rw [ha]
    exact (canonical10029 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA596 + difference 0 2) (sourceB596 + difference 2 0) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA596 + difference 0 2) (sourceB596 + difference 2 0) sourceC596) = raw10030 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10030; decide +kernel
    rw [ha]
    exact (canonical10030 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA596 + difference 0 3) (sourceB596 + difference 3 0) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA596 + difference 0 3) (sourceB596 + difference 3 0) sourceC596) = raw10031 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10031; decide +kernel
    rw [ha]
    exact (canonical10031 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA596 + difference 0 4) (sourceB596 + difference 4 0) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3860) := by
    have ha : (tripleCharges (sourceA596 + difference 0 4) (sourceB596 + difference 4 0) sourceC596) = raw10032 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10032; decide +kernel
    rw [ha]
    exact (canonical10032 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA596 + difference 0 5) (sourceB596 + difference 5 0) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA596 + difference 0 5) (sourceB596 + difference 5 0) sourceC596) = raw10033 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10033; decide +kernel
    rw [ha]
    exact (canonical10033 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA596 + difference 1 0) (sourceB596 + difference 0 1) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA596 + difference 1 0) (sourceB596 + difference 0 1) sourceC596) = raw10034 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10034; decide +kernel
    rw [ha]
    exact (canonical10034 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA596 + difference 1 2) (sourceB596 + difference 2 1) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA596 + difference 1 2) (sourceB596 + difference 2 1) sourceC596) = raw10035 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10035; decide +kernel
    rw [ha]
    exact (canonical10035 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA596 + difference 1 3) (sourceB596 + difference 3 1) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA596 + difference 1 3) (sourceB596 + difference 3 1) sourceC596) = raw10036 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10036; decide +kernel
    rw [ha]
    exact (canonical10036 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA596 + difference 1 4) (sourceB596 + difference 4 1) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA596 + difference 1 4) (sourceB596 + difference 4 1) sourceC596) = raw10037 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10037; decide +kernel
    rw [ha]
    exact (canonical10037 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA596 + difference 1 5) (sourceB596 + difference 5 1) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA596 + difference 1 5) (sourceB596 + difference 5 1) sourceC596) = raw10038 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10038; decide +kernel
    rw [ha]
    exact (canonical10038 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA596 + difference 2 0) (sourceB596 + difference 0 2) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA596 + difference 2 0) (sourceB596 + difference 0 2) sourceC596) = raw10039 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10039; decide +kernel
    rw [ha]
    exact (canonical10039 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA596 + difference 2 1) (sourceB596 + difference 1 2) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA596 + difference 2 1) (sourceB596 + difference 1 2) sourceC596) = raw10040 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10040; decide +kernel
    rw [ha]
    exact (canonical10040 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA596 + difference 2 3) (sourceB596 + difference 3 2) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3459) := by
    have ha : (tripleCharges (sourceA596 + difference 2 3) (sourceB596 + difference 3 2) sourceC596) = raw10041 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10041; decide +kernel
    rw [ha]
    exact (canonical10041 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA596 + difference 2 4) (sourceB596 + difference 4 2) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA596 + difference 2 4) (sourceB596 + difference 4 2) sourceC596) = raw10042 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10042; decide +kernel
    rw [ha]
    exact (canonical10042 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA596 + difference 2 5) (sourceB596 + difference 5 2) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA596 + difference 2 5) (sourceB596 + difference 5 2) sourceC596) = raw10043 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10043; decide +kernel
    rw [ha]
    exact (canonical10043 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA596 + difference 3 0) (sourceB596 + difference 0 3) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA596 + difference 3 0) (sourceB596 + difference 0 3) sourceC596) = raw10044 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10044; decide +kernel
    rw [ha]
    exact (canonical10044 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA596 + difference 3 1) (sourceB596 + difference 1 3) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA596 + difference 3 1) (sourceB596 + difference 1 3) sourceC596) = raw10045 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10045; decide +kernel
    rw [ha]
    exact (canonical10045 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA596 + difference 3 2) (sourceB596 + difference 2 3) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA596 + difference 3 2) (sourceB596 + difference 2 3) sourceC596) = raw10046 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10046; decide +kernel
    rw [ha]
    exact (canonical10046 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA596 + difference 3 4) (sourceB596 + difference 4 3) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA596 + difference 3 4) (sourceB596 + difference 4 3) sourceC596) = raw10047 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10047; decide +kernel
    rw [ha]
    exact (canonical10047 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA596 + difference 3 5) (sourceB596 + difference 5 3) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA596 + difference 3 5) (sourceB596 + difference 5 3) sourceC596) = raw10048 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10048; decide +kernel
    rw [ha]
    exact (canonical10048 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA596 + difference 4 0) (sourceB596 + difference 0 4) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3295) := by
    have ha : (tripleCharges (sourceA596 + difference 4 0) (sourceB596 + difference 0 4) sourceC596) = raw10049 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10049; decide +kernel
    rw [ha]
    exact (canonical10049 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA596 + difference 4 1) (sourceB596 + difference 1 4) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA596 + difference 4 1) (sourceB596 + difference 1 4) sourceC596) = raw10050 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10050; decide +kernel
    rw [ha]
    exact (canonical10050 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA596 + difference 4 2) (sourceB596 + difference 2 4) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA596 + difference 4 2) (sourceB596 + difference 2 4) sourceC596) = raw10051 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10051; decide +kernel
    rw [ha]
    exact (canonical10051 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA596 + difference 4 3) (sourceB596 + difference 3 4) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA596 + difference 4 3) (sourceB596 + difference 3 4) sourceC596) = raw10052 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10052; decide +kernel
    rw [ha]
    exact (canonical10052 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA596 + difference 4 5) (sourceB596 + difference 5 4) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA596 + difference 4 5) (sourceB596 + difference 5 4) sourceC596) = raw10053 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10053; decide +kernel
    rw [ha]
    exact (canonical10053 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA596 + difference 5 0) (sourceB596 + difference 0 5) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA596 + difference 5 0) (sourceB596 + difference 0 5) sourceC596) = raw10054 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10054; decide +kernel
    rw [ha]
    exact (canonical10054 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA596 + difference 5 1) (sourceB596 + difference 1 5) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA596 + difference 5 1) (sourceB596 + difference 1 5) sourceC596) = raw10055 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10055; decide +kernel
    rw [ha]
    exact (canonical10055 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA596 + difference 5 2) (sourceB596 + difference 2 5) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA596 + difference 5 2) (sourceB596 + difference 2 5) sourceC596) = raw10056 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10056; decide +kernel
    rw [ha]
    exact (canonical10056 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA596 + difference 5 3) (sourceB596 + difference 3 5) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA596 + difference 5 3) (sourceB596 + difference 3 5) sourceC596) = raw10057 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10057; decide +kernel
    rw [ha]
    exact (canonical10057 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA596 + difference 5 4) (sourceB596 + difference 4 5) sourceC596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA596 + difference 5 4) (sourceB596 + difference 4 5) sourceC596) = raw10058 := by
      apply Matrix.ext; unfold tripleCharges sourceA596 sourceB596 sourceC596 difference raw10058; decide +kernel
    rw [ha]
    exact (canonical10058 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA596 sourceB596 sourceC596
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm596, Integer.Sparse.eval]
  linarith only [hs]

def sourceA597 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB597 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC597 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceForm597 : Integer.Sparse Master := [(Sum.inr 2722, 1), (Sum.inr 3807, 1), (Sum.inr 3837, 1), (Sum.inr 3850, 1), (Sum.inr 3903, 1), (Sum.inr 3905, 1), (Sum.inr 4092, -1)]

theorem sourceEq597 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm597 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA597 + difference 0 0) (sourceB597 + difference 0 0) sourceC597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA597 + difference 0 0) (sourceB597 + difference 0 0) sourceC597) = raw10059 := by
      apply Matrix.ext; unfold tripleCharges sourceA597 sourceB597 sourceC597 difference raw10059; decide +kernel
    rw [ha]
    exact (canonical10059 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA597 + difference 0 1) (sourceB597 + difference 1 0) sourceC597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA597 + difference 0 1) (sourceB597 + difference 1 0) sourceC597) = raw10060 := by
      apply Matrix.ext; unfold tripleCharges sourceA597 sourceB597 sourceC597 difference raw10060; decide +kernel
    rw [ha]
    exact (canonical10060 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA597 + difference 0 2) (sourceB597 + difference 2 0) sourceC597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA597 + difference 0 2) (sourceB597 + difference 2 0) sourceC597) = raw10061 := by
      apply Matrix.ext; unfold tripleCharges sourceA597 sourceB597 sourceC597 difference raw10061; decide +kernel
    rw [ha]
    exact (canonical10061 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA597 + difference 0 3) (sourceB597 + difference 3 0) sourceC597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA597 + difference 0 3) (sourceB597 + difference 3 0) sourceC597) = raw10062 := by
      apply Matrix.ext; unfold tripleCharges sourceA597 sourceB597 sourceC597 difference raw10062; decide +kernel
    rw [ha]
    exact (canonical10062 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA597 + difference 0 4) (sourceB597 + difference 4 0) sourceC597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3905) := by
    have ha : (tripleCharges (sourceA597 + difference 0 4) (sourceB597 + difference 4 0) sourceC597) = raw10063 := by
      apply Matrix.ext; unfold tripleCharges sourceA597 sourceB597 sourceC597 difference raw10063; decide +kernel
    rw [ha]
    exact (canonical10063 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA597 + difference 0 5) (sourceB597 + difference 5 0) sourceC597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3903) := by
    have ha : (tripleCharges (sourceA597 + difference 0 5) (sourceB597 + difference 5 0) sourceC597) = raw10064 := by
      apply Matrix.ext; unfold tripleCharges sourceA597 sourceB597 sourceC597 difference raw10064; decide +kernel
    rw [ha]
    exact (canonical10064 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA597 + sourceB597) sourceC597) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA597 + sourceB597) sourceC597) = raw10065 := by
      apply Matrix.ext; unfold doubleCharges sourceA597 sourceB597 sourceC597 raw10065; decide +kernel
    rw [ha]
    exact (canonical10065 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA597 sourceB597 sourceC597
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm597, Integer.Sparse.eval]
  linarith only [hs]

def sourceA598 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB598 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC598 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceForm598 : Integer.Sparse Master := [(Sum.inr 1212, 1), (Sum.inr 1215, 1), (Sum.inr 1219, 1), (Sum.inr 1236, 1), (Sum.inr 1261, 1), (Sum.inr 2722, 1), (Sum.inr 4092, -1)]

theorem sourceEq598 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm598 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA598 + difference 0 0) (sourceB598 + difference 0 0) sourceC598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA598 + difference 0 0) (sourceB598 + difference 0 0) sourceC598) = raw10059 := by
      apply Matrix.ext; unfold tripleCharges sourceA598 sourceB598 sourceC598 difference raw10059; decide +kernel
    rw [ha]
    exact (canonical10059 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA598 + difference 1 0) (sourceB598 + difference 0 1) sourceC598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA598 + difference 1 0) (sourceB598 + difference 0 1) sourceC598) = raw10066 := by
      apply Matrix.ext; unfold tripleCharges sourceA598 sourceB598 sourceC598 difference raw10066; decide +kernel
    rw [ha]
    exact (canonical10066 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA598 + difference 2 0) (sourceB598 + difference 0 2) sourceC598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA598 + difference 2 0) (sourceB598 + difference 0 2) sourceC598) = raw10067 := by
      apply Matrix.ext; unfold tripleCharges sourceA598 sourceB598 sourceC598 difference raw10067; decide +kernel
    rw [ha]
    exact (canonical10067 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA598 + difference 3 0) (sourceB598 + difference 0 3) sourceC598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA598 + difference 3 0) (sourceB598 + difference 0 3) sourceC598) = raw10068 := by
      apply Matrix.ext; unfold tripleCharges sourceA598 sourceB598 sourceC598 difference raw10068; decide +kernel
    rw [ha]
    exact (canonical10068 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA598 + difference 4 0) (sourceB598 + difference 0 4) sourceC598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA598 + difference 4 0) (sourceB598 + difference 0 4) sourceC598) = raw10069 := by
      apply Matrix.ext; unfold tripleCharges sourceA598 sourceB598 sourceC598 difference raw10069; decide +kernel
    rw [ha]
    exact (canonical10069 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA598 + difference 5 0) (sourceB598 + difference 0 5) sourceC598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA598 + difference 5 0) (sourceB598 + difference 0 5) sourceC598) = raw10070 := by
      apply Matrix.ext; unfold tripleCharges sourceA598 sourceB598 sourceC598 difference raw10070; decide +kernel
    rw [ha]
    exact (canonical10070 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA598 + sourceB598) sourceC598) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA598 + sourceB598) sourceC598) = raw10065 := by
      apply Matrix.ext; unfold doubleCharges sourceA598 sourceB598 sourceC598 raw10065; decide +kernel
    rw [ha]
    exact (canonical10065 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA598 sourceB598 sourceC598
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm598, Integer.Sparse.eval]
  linarith only [hs]

def sourceA599 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB599 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC599 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceForm599 : Integer.Sparse Master := [(Sum.inr 1236, 1), (Sum.inr 2511, 1), (Sum.inr 2553, 1), (Sum.inr 2722, 1), (Sum.inr 2739, 1), (Sum.inr 2742, 1), (Sum.inr 4092, -1)]

theorem sourceEq599 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm599 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA599 + difference 1 0) (sourceB599 + difference 0 1) sourceC599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA599 + difference 1 0) (sourceB599 + difference 0 1) sourceC599) = raw10066 := by
      apply Matrix.ext; unfold tripleCharges sourceA599 sourceB599 sourceC599 difference raw10066; decide +kernel
    rw [ha]
    exact (canonical10066 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA599 + difference 1 1) (sourceB599 + difference 1 1) sourceC599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA599 + difference 1 1) (sourceB599 + difference 1 1) sourceC599) = raw10059 := by
      apply Matrix.ext; unfold tripleCharges sourceA599 sourceB599 sourceC599 difference raw10059; decide +kernel
    rw [ha]
    exact (canonical10059 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA599 + difference 1 2) (sourceB599 + difference 2 1) sourceC599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA599 + difference 1 2) (sourceB599 + difference 2 1) sourceC599) = raw10071 := by
      apply Matrix.ext; unfold tripleCharges sourceA599 sourceB599 sourceC599 difference raw10071; decide +kernel
    rw [ha]
    exact (canonical10071 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA599 + difference 1 3) (sourceB599 + difference 3 1) sourceC599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2511) := by
    have ha : (tripleCharges (sourceA599 + difference 1 3) (sourceB599 + difference 3 1) sourceC599) = raw10072 := by
      apply Matrix.ext; unfold tripleCharges sourceA599 sourceB599 sourceC599 difference raw10072; decide +kernel
    rw [ha]
    exact (canonical10072 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA599 + difference 1 4) (sourceB599 + difference 4 1) sourceC599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA599 + difference 1 4) (sourceB599 + difference 4 1) sourceC599) = raw10073 := by
      apply Matrix.ext; unfold tripleCharges sourceA599 sourceB599 sourceC599 difference raw10073; decide +kernel
    rw [ha]
    exact (canonical10073 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA599 + difference 1 5) (sourceB599 + difference 5 1) sourceC599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA599 + difference 1 5) (sourceB599 + difference 5 1) sourceC599) = raw10074 := by
      apply Matrix.ext; unfold tripleCharges sourceA599 sourceB599 sourceC599 difference raw10074; decide +kernel
    rw [ha]
    exact (canonical10074 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA599 + sourceB599) sourceC599) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA599 + sourceB599) sourceC599) = raw10065 := by
      apply Matrix.ext; unfold doubleCharges sourceA599 sourceB599 sourceC599 raw10065; decide +kernel
    rw [ha]
    exact (canonical10065 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA599 sourceB599 sourceC599
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm599, Integer.Sparse.eval]
  linarith only [hs]

def sourceA600 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB600 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC600 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceForm600 : Integer.Sparse Master := [(Sum.inr 2569, 1), (Sum.inr 2614, 1), (Sum.inr 2620, 1), (Sum.inr 2632, 1), (Sum.inr 2722, 1), (Sum.inr 3850, 1), (Sum.inr 4092, -1)]

theorem sourceEq600 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm600 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA600 + difference 0 1) (sourceB600 + difference 1 0) sourceC600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA600 + difference 0 1) (sourceB600 + difference 1 0) sourceC600) = raw10060 := by
      apply Matrix.ext; unfold tripleCharges sourceA600 sourceB600 sourceC600 difference raw10060; decide +kernel
    rw [ha]
    exact (canonical10060 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA600 + difference 1 1) (sourceB600 + difference 1 1) sourceC600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA600 + difference 1 1) (sourceB600 + difference 1 1) sourceC600) = raw10059 := by
      apply Matrix.ext; unfold tripleCharges sourceA600 sourceB600 sourceC600 difference raw10059; decide +kernel
    rw [ha]
    exact (canonical10059 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA600 + difference 2 1) (sourceB600 + difference 1 2) sourceC600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2614) := by
    have ha : (tripleCharges (sourceA600 + difference 2 1) (sourceB600 + difference 1 2) sourceC600) = raw10075 := by
      apply Matrix.ext; unfold tripleCharges sourceA600 sourceB600 sourceC600 difference raw10075; decide +kernel
    rw [ha]
    exact (canonical10075 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA600 + difference 3 1) (sourceB600 + difference 1 3) sourceC600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2632) := by
    have ha : (tripleCharges (sourceA600 + difference 3 1) (sourceB600 + difference 1 3) sourceC600) = raw10076 := by
      apply Matrix.ext; unfold tripleCharges sourceA600 sourceB600 sourceC600 difference raw10076; decide +kernel
    rw [ha]
    exact (canonical10076 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA600 + difference 4 1) (sourceB600 + difference 1 4) sourceC600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2620) := by
    have ha : (tripleCharges (sourceA600 + difference 4 1) (sourceB600 + difference 1 4) sourceC600) = raw10077 := by
      apply Matrix.ext; unfold tripleCharges sourceA600 sourceB600 sourceC600 difference raw10077; decide +kernel
    rw [ha]
    exact (canonical10077 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA600 + difference 5 1) (sourceB600 + difference 1 5) sourceC600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2569) := by
    have ha : (tripleCharges (sourceA600 + difference 5 1) (sourceB600 + difference 1 5) sourceC600) = raw10078 := by
      apply Matrix.ext; unfold tripleCharges sourceA600 sourceB600 sourceC600 difference raw10078; decide +kernel
    rw [ha]
    exact (canonical10078 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA600 + sourceB600) sourceC600) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA600 + sourceB600) sourceC600) = raw10065 := by
      apply Matrix.ext; unfold doubleCharges sourceA600 sourceB600 sourceC600 raw10065; decide +kernel
    rw [ha]
    exact (canonical10065 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA600 sourceB600 sourceC600
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm600, Integer.Sparse.eval]
  linarith only [hs]

def sourceA601 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB601 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC601 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceForm601 : Integer.Sparse Master := [(Sum.inr 1212, 1), (Sum.inr 2479, 1), (Sum.inr 2614, 1), (Sum.inr 2720, 1), (Sum.inr 2722, 2), (Sum.inr 4092, -1)]

theorem sourceEq601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm601 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA601 + difference 2 0) (sourceB601 + difference 0 2) sourceC601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA601 + difference 2 0) (sourceB601 + difference 0 2) sourceC601) = raw10067 := by
      apply Matrix.ext; unfold tripleCharges sourceA601 sourceB601 sourceC601 difference raw10067; decide +kernel
    rw [ha]
    exact (canonical10067 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA601 + difference 2 1) (sourceB601 + difference 1 2) sourceC601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2614) := by
    have ha : (tripleCharges (sourceA601 + difference 2 1) (sourceB601 + difference 1 2) sourceC601) = raw10075 := by
      apply Matrix.ext; unfold tripleCharges sourceA601 sourceB601 sourceC601 difference raw10075; decide +kernel
    rw [ha]
    exact (canonical10075 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA601 + difference 2 2) (sourceB601 + difference 2 2) sourceC601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA601 + difference 2 2) (sourceB601 + difference 2 2) sourceC601) = raw10059 := by
      apply Matrix.ext; unfold tripleCharges sourceA601 sourceB601 sourceC601 difference raw10059; decide +kernel
    rw [ha]
    exact (canonical10059 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA601 + difference 2 3) (sourceB601 + difference 3 2) sourceC601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2479) := by
    have ha : (tripleCharges (sourceA601 + difference 2 3) (sourceB601 + difference 3 2) sourceC601) = raw10079 := by
      apply Matrix.ext; unfold tripleCharges sourceA601 sourceB601 sourceC601 difference raw10079; decide +kernel
    rw [ha]
    exact (canonical10079 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA601 + difference 2 4) (sourceB601 + difference 4 2) sourceC601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA601 + difference 2 4) (sourceB601 + difference 4 2) sourceC601) = raw10080 := by
      apply Matrix.ext; unfold tripleCharges sourceA601 sourceB601 sourceC601 difference raw10080; decide +kernel
    rw [ha]
    exact (canonical10080 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA601 + difference 2 5) (sourceB601 + difference 5 2) sourceC601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA601 + difference 2 5) (sourceB601 + difference 5 2) sourceC601) = raw10081 := by
      apply Matrix.ext; unfold tripleCharges sourceA601 sourceB601 sourceC601 difference raw10081; decide +kernel
    rw [ha]
    exact (canonical10081 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA601 + sourceB601) sourceC601) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA601 + sourceB601) sourceC601) = raw10065 := by
      apply Matrix.ext; unfold doubleCharges sourceA601 sourceB601 sourceC601 raw10065; decide +kernel
    rw [ha]
    exact (canonical10065 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA601 sourceB601 sourceC601
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm601, Integer.Sparse.eval]
  linarith only [hs]

def sourceA602 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB602 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC602 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceForm602 : Integer.Sparse Master := [(Sum.inr 2542, 1), (Sum.inr 2545, 1), (Sum.inr 2553, 1), (Sum.inr 2566, 1), (Sum.inr 2722, 1), (Sum.inr 3837, 1), (Sum.inr 4092, -1)]

theorem sourceEq602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm602 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA602 + difference 0 2) (sourceB602 + difference 2 0) sourceC602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA602 + difference 0 2) (sourceB602 + difference 2 0) sourceC602) = raw10061 := by
      apply Matrix.ext; unfold tripleCharges sourceA602 sourceB602 sourceC602 difference raw10061; decide +kernel
    rw [ha]
    exact (canonical10061 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA602 + difference 1 2) (sourceB602 + difference 2 1) sourceC602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA602 + difference 1 2) (sourceB602 + difference 2 1) sourceC602) = raw10071 := by
      apply Matrix.ext; unfold tripleCharges sourceA602 sourceB602 sourceC602 difference raw10071; decide +kernel
    rw [ha]
    exact (canonical10071 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA602 + difference 2 2) (sourceB602 + difference 2 2) sourceC602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA602 + difference 2 2) (sourceB602 + difference 2 2) sourceC602) = raw10059 := by
      apply Matrix.ext; unfold tripleCharges sourceA602 sourceB602 sourceC602 difference raw10059; decide +kernel
    rw [ha]
    exact (canonical10059 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA602 + difference 3 2) (sourceB602 + difference 2 3) sourceC602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2566) := by
    have ha : (tripleCharges (sourceA602 + difference 3 2) (sourceB602 + difference 2 3) sourceC602) = raw10082 := by
      apply Matrix.ext; unfold tripleCharges sourceA602 sourceB602 sourceC602 difference raw10082; decide +kernel
    rw [ha]
    exact (canonical10082 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA602 + difference 4 2) (sourceB602 + difference 2 4) sourceC602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA602 + difference 4 2) (sourceB602 + difference 2 4) sourceC602) = raw10083 := by
      apply Matrix.ext; unfold tripleCharges sourceA602 sourceB602 sourceC602 difference raw10083; decide +kernel
    rw [ha]
    exact (canonical10083 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA602 + difference 5 2) (sourceB602 + difference 2 5) sourceC602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2542) := by
    have ha : (tripleCharges (sourceA602 + difference 5 2) (sourceB602 + difference 2 5) sourceC602) = raw10084 := by
      apply Matrix.ext; unfold tripleCharges sourceA602 sourceB602 sourceC602 difference raw10084; decide +kernel
    rw [ha]
    exact (canonical10084 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA602 + sourceB602) sourceC602) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA602 + sourceB602) sourceC602) = raw10065 := by
      apply Matrix.ext; unfold doubleCharges sourceA602 sourceB602 sourceC602 raw10065; decide +kernel
    rw [ha]
    exact (canonical10065 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA602 sourceB602 sourceC602
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm602, Integer.Sparse.eval]
  linarith only [hs]

def sourceA603 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB603 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC603 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceForm603 : Integer.Sparse Master := [(Sum.inr 4396, 1), (Sum.inr 4398, 1), (Sum.inr 4404, 1), (Sum.inr 4419, 1), (Sum.inr 4457, 1), (Sum.inr 4779, 1), (Sum.inr 4788, 1), (Sum.inr 4804, 1), (Sum.inr 4832, 1), (Sum.inr 4996, 1), (Sum.inr 5003, 1), (Sum.inr 5015, 1), (Sum.inr 5050, 1), (Sum.inr 5056, 1), (Sum.inr 5072, 1), (Sum.inr 5134, 1), (Sum.inr 5141, 1), (Sum.inr 5168, 1), (Sum.inr 5241, 1), (Sum.inr 5248, 1), (Sum.inr 5257, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5271, 1), (Sum.inr 5292, 1), (Sum.inr 5424, 1), (Sum.inr 5428, 1), (Sum.inr 5434, 1), (Sum.inr 5439, 1), (Sum.inr 5490, 1)]

theorem sourceEq603 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm603 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA603 + difference 0 1) (sourceB603 + difference 1 0) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA603 + difference 0 1) (sourceB603 + difference 1 0) sourceC603) = raw10085 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10085; decide +kernel
    rw [ha]
    exact (canonical10085 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA603 + difference 0 2) (sourceB603 + difference 2 0) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA603 + difference 0 2) (sourceB603 + difference 2 0) sourceC603) = raw10086 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10086; decide +kernel
    rw [ha]
    exact (canonical10086 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA603 + difference 0 3) (sourceB603 + difference 3 0) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA603 + difference 0 3) (sourceB603 + difference 3 0) sourceC603) = raw10087 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10087; decide +kernel
    rw [ha]
    exact (canonical10087 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA603 + difference 0 4) (sourceB603 + difference 4 0) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA603 + difference 0 4) (sourceB603 + difference 4 0) sourceC603) = raw10088 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10088; decide +kernel
    rw [ha]
    exact (canonical10088 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA603 + difference 0 5) (sourceB603 + difference 5 0) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA603 + difference 0 5) (sourceB603 + difference 5 0) sourceC603) = raw10089 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10089; decide +kernel
    rw [ha]
    exact (canonical10089 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA603 + difference 1 0) (sourceB603 + difference 0 1) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA603 + difference 1 0) (sourceB603 + difference 0 1) sourceC603) = raw10090 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10090; decide +kernel
    rw [ha]
    exact (canonical10090 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA603 + difference 1 2) (sourceB603 + difference 2 1) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA603 + difference 1 2) (sourceB603 + difference 2 1) sourceC603) = raw10091 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10091; decide +kernel
    rw [ha]
    exact (canonical10091 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA603 + difference 1 3) (sourceB603 + difference 3 1) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA603 + difference 1 3) (sourceB603 + difference 3 1) sourceC603) = raw10092 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10092; decide +kernel
    rw [ha]
    exact (canonical10092 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA603 + difference 1 4) (sourceB603 + difference 4 1) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA603 + difference 1 4) (sourceB603 + difference 4 1) sourceC603) = raw10093 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10093; decide +kernel
    rw [ha]
    exact (canonical10093 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA603 + difference 1 5) (sourceB603 + difference 5 1) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA603 + difference 1 5) (sourceB603 + difference 5 1) sourceC603) = raw10094 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10094; decide +kernel
    rw [ha]
    exact (canonical10094 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA603 + difference 2 0) (sourceB603 + difference 0 2) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA603 + difference 2 0) (sourceB603 + difference 0 2) sourceC603) = raw10095 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10095; decide +kernel
    rw [ha]
    exact (canonical10095 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA603 + difference 2 1) (sourceB603 + difference 1 2) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA603 + difference 2 1) (sourceB603 + difference 1 2) sourceC603) = raw10096 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10096; decide +kernel
    rw [ha]
    exact (canonical10096 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA603 + difference 2 3) (sourceB603 + difference 3 2) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA603 + difference 2 3) (sourceB603 + difference 3 2) sourceC603) = raw10097 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10097; decide +kernel
    rw [ha]
    exact (canonical10097 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA603 + difference 2 4) (sourceB603 + difference 4 2) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA603 + difference 2 4) (sourceB603 + difference 4 2) sourceC603) = raw10098 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10098; decide +kernel
    rw [ha]
    exact (canonical10098 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA603 + difference 2 5) (sourceB603 + difference 5 2) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA603 + difference 2 5) (sourceB603 + difference 5 2) sourceC603) = raw10099 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10099; decide +kernel
    rw [ha]
    exact (canonical10099 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA603 + difference 3 0) (sourceB603 + difference 0 3) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA603 + difference 3 0) (sourceB603 + difference 0 3) sourceC603) = raw10100 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10100; decide +kernel
    rw [ha]
    exact (canonical10100 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA603 + difference 3 1) (sourceB603 + difference 1 3) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA603 + difference 3 1) (sourceB603 + difference 1 3) sourceC603) = raw10101 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10101; decide +kernel
    rw [ha]
    exact (canonical10101 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA603 + difference 3 2) (sourceB603 + difference 2 3) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA603 + difference 3 2) (sourceB603 + difference 2 3) sourceC603) = raw10102 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10102; decide +kernel
    rw [ha]
    exact (canonical10102 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA603 + difference 3 4) (sourceB603 + difference 4 3) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA603 + difference 3 4) (sourceB603 + difference 4 3) sourceC603) = raw10103 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10103; decide +kernel
    rw [ha]
    exact (canonical10103 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA603 + difference 3 5) (sourceB603 + difference 5 3) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA603 + difference 3 5) (sourceB603 + difference 5 3) sourceC603) = raw10104 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10104; decide +kernel
    rw [ha]
    exact (canonical10104 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA603 + difference 4 0) (sourceB603 + difference 0 4) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA603 + difference 4 0) (sourceB603 + difference 0 4) sourceC603) = raw10105 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10105; decide +kernel
    rw [ha]
    exact (canonical10105 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA603 + difference 4 1) (sourceB603 + difference 1 4) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA603 + difference 4 1) (sourceB603 + difference 1 4) sourceC603) = raw10106 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10106; decide +kernel
    rw [ha]
    exact (canonical10106 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA603 + difference 4 2) (sourceB603 + difference 2 4) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA603 + difference 4 2) (sourceB603 + difference 2 4) sourceC603) = raw10107 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10107; decide +kernel
    rw [ha]
    exact (canonical10107 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA603 + difference 4 3) (sourceB603 + difference 3 4) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA603 + difference 4 3) (sourceB603 + difference 3 4) sourceC603) = raw10108 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10108; decide +kernel
    rw [ha]
    exact (canonical10108 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA603 + difference 4 5) (sourceB603 + difference 5 4) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA603 + difference 4 5) (sourceB603 + difference 5 4) sourceC603) = raw10109 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10109; decide +kernel
    rw [ha]
    exact (canonical10109 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA603 + difference 5 0) (sourceB603 + difference 0 5) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA603 + difference 5 0) (sourceB603 + difference 0 5) sourceC603) = raw10110 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10110; decide +kernel
    rw [ha]
    exact (canonical10110 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA603 + difference 5 1) (sourceB603 + difference 1 5) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA603 + difference 5 1) (sourceB603 + difference 1 5) sourceC603) = raw10111 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10111; decide +kernel
    rw [ha]
    exact (canonical10111 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA603 + difference 5 2) (sourceB603 + difference 2 5) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA603 + difference 5 2) (sourceB603 + difference 2 5) sourceC603) = raw10112 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10112; decide +kernel
    rw [ha]
    exact (canonical10112 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA603 + difference 5 3) (sourceB603 + difference 3 5) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA603 + difference 5 3) (sourceB603 + difference 3 5) sourceC603) = raw10113 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10113; decide +kernel
    rw [ha]
    exact (canonical10113 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA603 + difference 5 4) (sourceB603 + difference 4 5) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA603 + difference 5 4) (sourceB603 + difference 4 5) sourceC603) = raw10114 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10114; decide +kernel
    rw [ha]
    exact (canonical10114 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA603 sourceB603 sourceC603
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm603, Integer.Sparse.eval]
  linarith only [hs]

def sourceA604 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB604 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC604 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceForm604 : Integer.Sparse Master := [(Sum.inr 977, 1), (Sum.inr 979, 1), (Sum.inr 985, 1), (Sum.inr 1000, 1), (Sum.inr 1040, 1), (Sum.inr 1987, 1), (Sum.inr 2003, 1), (Sum.inr 2022, 1), (Sum.inr 2193, 1), (Sum.inr 2382, 1), (Sum.inr 2388, 1), (Sum.inr 2400, 1), (Sum.inr 2452, 1), (Sum.inr 2459, 1), (Sum.inr 2479, 1), (Sum.inr 2553, 1), (Sum.inr 2561, 1), (Sum.inr 2594, 1), (Sum.inr 2694, 1), (Sum.inr 2705, 1), (Sum.inr 2721, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 2739, 1), (Sum.inr 2766, 1), (Sum.inr 3838, 1), (Sum.inr 3845, 1), (Sum.inr 3852, 1), (Sum.inr 3902, 1), (Sum.inr 4013, 1)]

theorem sourceEq604 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm604 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA604 + difference 0 1) (sourceB604 + difference 1 0) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA604 + difference 0 1) (sourceB604 + difference 1 0) sourceC604) = raw10115 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10115; decide +kernel
    rw [ha]
    exact (canonical10115 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA604 + difference 0 2) (sourceB604 + difference 2 0) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA604 + difference 0 2) (sourceB604 + difference 2 0) sourceC604) = raw10116 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10116; decide +kernel
    rw [ha]
    exact (canonical10116 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA604 + difference 0 3) (sourceB604 + difference 3 0) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA604 + difference 0 3) (sourceB604 + difference 3 0) sourceC604) = raw10117 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10117; decide +kernel
    rw [ha]
    exact (canonical10117 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA604 + difference 0 4) (sourceB604 + difference 4 0) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA604 + difference 0 4) (sourceB604 + difference 4 0) sourceC604) = raw10118 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10118; decide +kernel
    rw [ha]
    exact (canonical10118 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA604 + difference 0 5) (sourceB604 + difference 5 0) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA604 + difference 0 5) (sourceB604 + difference 5 0) sourceC604) = raw10119 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10119; decide +kernel
    rw [ha]
    exact (canonical10119 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA604 + difference 1 0) (sourceB604 + difference 0 1) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA604 + difference 1 0) (sourceB604 + difference 0 1) sourceC604) = raw10120 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10120; decide +kernel
    rw [ha]
    exact (canonical10120 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA604 + difference 1 2) (sourceB604 + difference 2 1) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA604 + difference 1 2) (sourceB604 + difference 2 1) sourceC604) = raw10121 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10121; decide +kernel
    rw [ha]
    exact (canonical10121 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA604 + difference 1 3) (sourceB604 + difference 3 1) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2400) := by
    have ha : (tripleCharges (sourceA604 + difference 1 3) (sourceB604 + difference 3 1) sourceC604) = raw10122 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10122; decide +kernel
    rw [ha]
    exact (canonical10122 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA604 + difference 1 4) (sourceB604 + difference 4 1) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA604 + difference 1 4) (sourceB604 + difference 4 1) sourceC604) = raw10123 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10123; decide +kernel
    rw [ha]
    exact (canonical10123 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA604 + difference 1 5) (sourceB604 + difference 5 1) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA604 + difference 1 5) (sourceB604 + difference 5 1) sourceC604) = raw10124 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10124; decide +kernel
    rw [ha]
    exact (canonical10124 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA604 + difference 2 0) (sourceB604 + difference 0 2) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA604 + difference 2 0) (sourceB604 + difference 0 2) sourceC604) = raw10125 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10125; decide +kernel
    rw [ha]
    exact (canonical10125 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA604 + difference 2 1) (sourceB604 + difference 1 2) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA604 + difference 2 1) (sourceB604 + difference 1 2) sourceC604) = raw10126 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10126; decide +kernel
    rw [ha]
    exact (canonical10126 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA604 + difference 2 3) (sourceB604 + difference 3 2) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2382) := by
    have ha : (tripleCharges (sourceA604 + difference 2 3) (sourceB604 + difference 3 2) sourceC604) = raw10127 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10127; decide +kernel
    rw [ha]
    exact (canonical10127 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA604 + difference 2 4) (sourceB604 + difference 4 2) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA604 + difference 2 4) (sourceB604 + difference 4 2) sourceC604) = raw10128 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10128; decide +kernel
    rw [ha]
    exact (canonical10128 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA604 + difference 2 5) (sourceB604 + difference 5 2) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA604 + difference 2 5) (sourceB604 + difference 5 2) sourceC604) = raw10129 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10129; decide +kernel
    rw [ha]
    exact (canonical10129 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA604 + difference 3 0) (sourceB604 + difference 0 3) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA604 + difference 3 0) (sourceB604 + difference 0 3) sourceC604) = raw10130 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10130; decide +kernel
    rw [ha]
    exact (canonical10130 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA604 + difference 3 1) (sourceB604 + difference 1 3) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2594) := by
    have ha : (tripleCharges (sourceA604 + difference 3 1) (sourceB604 + difference 1 3) sourceC604) = raw10131 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10131; decide +kernel
    rw [ha]
    exact (canonical10131 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA604 + difference 3 2) (sourceB604 + difference 2 3) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2479) := by
    have ha : (tripleCharges (sourceA604 + difference 3 2) (sourceB604 + difference 2 3) sourceC604) = raw10132 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10132; decide +kernel
    rw [ha]
    exact (canonical10132 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA604 + difference 3 4) (sourceB604 + difference 4 3) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA604 + difference 3 4) (sourceB604 + difference 4 3) sourceC604) = raw10133 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10133; decide +kernel
    rw [ha]
    exact (canonical10133 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA604 + difference 3 5) (sourceB604 + difference 5 3) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA604 + difference 3 5) (sourceB604 + difference 5 3) sourceC604) = raw10134 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10134; decide +kernel
    rw [ha]
    exact (canonical10134 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA604 + difference 4 0) (sourceB604 + difference 0 4) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA604 + difference 4 0) (sourceB604 + difference 0 4) sourceC604) = raw10135 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10135; decide +kernel
    rw [ha]
    exact (canonical10135 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA604 + difference 4 1) (sourceB604 + difference 1 4) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA604 + difference 4 1) (sourceB604 + difference 1 4) sourceC604) = raw10136 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10136; decide +kernel
    rw [ha]
    exact (canonical10136 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA604 + difference 4 2) (sourceB604 + difference 2 4) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA604 + difference 4 2) (sourceB604 + difference 2 4) sourceC604) = raw10137 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10137; decide +kernel
    rw [ha]
    exact (canonical10137 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA604 + difference 4 3) (sourceB604 + difference 3 4) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2388) := by
    have ha : (tripleCharges (sourceA604 + difference 4 3) (sourceB604 + difference 3 4) sourceC604) = raw10138 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10138; decide +kernel
    rw [ha]
    exact (canonical10138 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA604 + difference 4 5) (sourceB604 + difference 5 4) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA604 + difference 4 5) (sourceB604 + difference 5 4) sourceC604) = raw10139 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10139; decide +kernel
    rw [ha]
    exact (canonical10139 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA604 + difference 5 0) (sourceB604 + difference 0 5) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA604 + difference 5 0) (sourceB604 + difference 0 5) sourceC604) = raw10140 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10140; decide +kernel
    rw [ha]
    exact (canonical10140 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA604 + difference 5 1) (sourceB604 + difference 1 5) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA604 + difference 5 1) (sourceB604 + difference 1 5) sourceC604) = raw10141 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10141; decide +kernel
    rw [ha]
    exact (canonical10141 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA604 + difference 5 2) (sourceB604 + difference 2 5) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1987) := by
    have ha : (tripleCharges (sourceA604 + difference 5 2) (sourceB604 + difference 2 5) sourceC604) = raw10142 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10142; decide +kernel
    rw [ha]
    exact (canonical10142 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA604 + difference 5 3) (sourceB604 + difference 3 5) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2003) := by
    have ha : (tripleCharges (sourceA604 + difference 5 3) (sourceB604 + difference 3 5) sourceC604) = raw10143 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10143; decide +kernel
    rw [ha]
    exact (canonical10143 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA604 + difference 5 4) (sourceB604 + difference 4 5) sourceC604) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA604 + difference 5 4) (sourceB604 + difference 4 5) sourceC604) = raw10144 := by
      apply Matrix.ext; unfold tripleCharges sourceA604 sourceB604 sourceC604 difference raw10144; decide +kernel
    rw [ha]
    exact (canonical10144 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA604 sourceB604 sourceC604
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm604, Integer.Sparse.eval]
  linarith only [hs]

def sourceA605 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB605 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC605 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm605 : Integer.Sparse Master := [(Sum.inr 4801, 1), (Sum.inr 4804, 1), (Sum.inr 4810, 1), (Sum.inr 4834, 1), (Sum.inr 4894, 1), (Sum.inr 5133, 1), (Sum.inr 5140, 1), (Sum.inr 5161, 1), (Sum.inr 5219, 1), (Sum.inr 5228, 1), (Sum.inr 5232, 1), (Sum.inr 5241, 1), (Sum.inr 5243, 1), (Sum.inr 5249, 1), (Sum.inr 5250, 1), (Sum.inr 5251, 1), (Sum.inr 5258, 2), (Sum.inr 5259, 2), (Sum.inr 5260, 1), (Sum.inr 5264, 1), (Sum.inr 5266, 1), (Sum.inr 5267, 1), (Sum.inr 5272, 1), (Sum.inr 5274, 1), (Sum.inr 5291, 1), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5308, 1)]

theorem sourceEq605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm605 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA605 + difference 0 1) (sourceB605 + difference 1 0) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA605 + difference 0 1) (sourceB605 + difference 1 0) sourceC605) = raw10145 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw10145; decide +kernel
    rw [ha]
    exact (canonical10145 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA605 + difference 0 2) (sourceB605 + difference 2 0) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA605 + difference 0 2) (sourceB605 + difference 2 0) sourceC605) = raw10146 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw10146; decide +kernel
    rw [ha]
    exact (canonical10146 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA605 + difference 0 3) (sourceB605 + difference 3 0) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA605 + difference 0 3) (sourceB605 + difference 3 0) sourceC605) = raw10147 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw10147; decide +kernel
    rw [ha]
    exact (canonical10147 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA605 + difference 0 4) (sourceB605 + difference 4 0) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA605 + difference 0 4) (sourceB605 + difference 4 0) sourceC605) = raw9654 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw9654; decide +kernel
    rw [ha]
    exact (canonical9654 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA605 + difference 0 5) (sourceB605 + difference 5 0) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA605 + difference 0 5) (sourceB605 + difference 5 0) sourceC605) = raw9894 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw9894; decide +kernel
    rw [ha]
    exact (canonical9894 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA605 + difference 1 0) (sourceB605 + difference 0 1) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA605 + difference 1 0) (sourceB605 + difference 0 1) sourceC605) = raw10148 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw10148; decide +kernel
    rw [ha]
    exact (canonical10148 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA605 + difference 1 2) (sourceB605 + difference 2 1) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5243) := by
    have ha : (tripleCharges (sourceA605 + difference 1 2) (sourceB605 + difference 2 1) sourceC605) = raw10149 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw10149; decide +kernel
    rw [ha]
    exact (canonical10149 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA605 + difference 1 3) (sourceB605 + difference 3 1) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA605 + difference 1 3) (sourceB605 + difference 3 1) sourceC605) = raw10150 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw10150; decide +kernel
    rw [ha]
    exact (canonical10150 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA605 + difference 1 4) (sourceB605 + difference 4 1) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA605 + difference 1 4) (sourceB605 + difference 4 1) sourceC605) = raw9659 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw9659; decide +kernel
    rw [ha]
    exact (canonical9659 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA605 + difference 1 5) (sourceB605 + difference 5 1) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA605 + difference 1 5) (sourceB605 + difference 5 1) sourceC605) = raw9899 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw9899; decide +kernel
    rw [ha]
    exact (canonical9899 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA605 + difference 2 0) (sourceB605 + difference 0 2) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA605 + difference 2 0) (sourceB605 + difference 0 2) sourceC605) = raw10151 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw10151; decide +kernel
    rw [ha]
    exact (canonical10151 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA605 + difference 2 1) (sourceB605 + difference 1 2) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA605 + difference 2 1) (sourceB605 + difference 1 2) sourceC605) = raw10152 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw10152; decide +kernel
    rw [ha]
    exact (canonical10152 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA605 + difference 2 3) (sourceB605 + difference 3 2) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA605 + difference 2 3) (sourceB605 + difference 3 2) sourceC605) = raw10153 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw10153; decide +kernel
    rw [ha]
    exact (canonical10153 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA605 + difference 2 4) (sourceB605 + difference 4 2) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA605 + difference 2 4) (sourceB605 + difference 4 2) sourceC605) = raw9663 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw9663; decide +kernel
    rw [ha]
    exact (canonical9663 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA605 + difference 2 5) (sourceB605 + difference 5 2) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA605 + difference 2 5) (sourceB605 + difference 5 2) sourceC605) = raw9904 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw9904; decide +kernel
    rw [ha]
    exact (canonical9904 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA605 + difference 3 0) (sourceB605 + difference 0 3) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA605 + difference 3 0) (sourceB605 + difference 0 3) sourceC605) = raw9668 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw9668; decide +kernel
    rw [ha]
    exact (canonical9668 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA605 + difference 3 1) (sourceB605 + difference 1 3) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA605 + difference 3 1) (sourceB605 + difference 1 3) sourceC605) = raw7929 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw7929; decide +kernel
    rw [ha]
    exact (canonical7929 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA605 + difference 3 2) (sourceB605 + difference 2 3) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA605 + difference 3 2) (sourceB605 + difference 2 3) sourceC605) = raw9669 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw9669; decide +kernel
    rw [ha]
    exact (canonical9669 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA605 + difference 3 4) (sourceB605 + difference 4 3) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA605 + difference 3 4) (sourceB605 + difference 4 3) sourceC605) = raw10154 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw10154; decide +kernel
    rw [ha]
    exact (canonical10154 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA605 + difference 3 5) (sourceB605 + difference 5 3) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA605 + difference 3 5) (sourceB605 + difference 5 3) sourceC605) = raw7923 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw7923; decide +kernel
    rw [ha]
    exact (canonical7923 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA605 + difference 4 0) (sourceB605 + difference 0 4) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA605 + difference 4 0) (sourceB605 + difference 0 4) sourceC605) = raw9911 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw9911; decide +kernel
    rw [ha]
    exact (canonical9911 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA605 + difference 4 1) (sourceB605 + difference 1 4) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA605 + difference 4 1) (sourceB605 + difference 1 4) sourceC605) = raw9912 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw9912; decide +kernel
    rw [ha]
    exact (canonical9912 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA605 + difference 4 2) (sourceB605 + difference 2 4) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA605 + difference 4 2) (sourceB605 + difference 2 4) sourceC605) = raw9913 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw9913; decide +kernel
    rw [ha]
    exact (canonical9913 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA605 + difference 4 3) (sourceB605 + difference 3 4) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA605 + difference 4 3) (sourceB605 + difference 3 4) sourceC605) = raw9914 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw9914; decide +kernel
    rw [ha]
    exact (canonical9914 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA605 + difference 4 5) (sourceB605 + difference 5 4) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA605 + difference 4 5) (sourceB605 + difference 5 4) sourceC605) = raw10155 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw10155; decide +kernel
    rw [ha]
    exact (canonical10155 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA605 + difference 5 0) (sourceB605 + difference 0 5) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA605 + difference 5 0) (sourceB605 + difference 0 5) sourceC605) = raw10156 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw10156; decide +kernel
    rw [ha]
    exact (canonical10156 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA605 + difference 5 1) (sourceB605 + difference 1 5) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA605 + difference 5 1) (sourceB605 + difference 1 5) sourceC605) = raw10157 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw10157; decide +kernel
    rw [ha]
    exact (canonical10157 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA605 + difference 5 2) (sourceB605 + difference 2 5) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5133) := by
    have ha : (tripleCharges (sourceA605 + difference 5 2) (sourceB605 + difference 2 5) sourceC605) = raw10158 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw10158; decide +kernel
    rw [ha]
    exact (canonical10158 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA605 + difference 5 3) (sourceB605 + difference 3 5) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA605 + difference 5 3) (sourceB605 + difference 3 5) sourceC605) = raw10159 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw10159; decide +kernel
    rw [ha]
    exact (canonical10159 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA605 + difference 5 4) (sourceB605 + difference 4 5) sourceC605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA605 + difference 5 4) (sourceB605 + difference 4 5) sourceC605) = raw9674 := by
      apply Matrix.ext; unfold tripleCharges sourceA605 sourceB605 sourceC605 difference raw9674; decide +kernel
    rw [ha]
    exact (canonical9674 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA605 sourceB605 sourceC605
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm605, Integer.Sparse.eval]
  linarith only [hs]

def sourceA606 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB606 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC606 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm606 : Integer.Sparse Master := [(Sum.inr 2190, 1), (Sum.inr 2203, 1), (Sum.inr 2205, 1), (Sum.inr 2215, 1), (Sum.inr 2264, 1), (Sum.inr 2661, 1), (Sum.inr 2670, 1), (Sum.inr 2672, 1), (Sum.inr 2677, 1), (Sum.inr 2693, 1), (Sum.inr 2694, 1), (Sum.inr 2697, 1), (Sum.inr 2708, 1), (Sum.inr 2709, 1), (Sum.inr 2719, 1), (Sum.inr 2722, 2), (Sum.inr 2723, 1), (Sum.inr 2729, 1), (Sum.inr 2731, 1), (Sum.inr 2740, 1), (Sum.inr 2742, 1), (Sum.inr 2765, 1), (Sum.inr 2767, 1), (Sum.inr 2786, 1), (Sum.inr 3038, 1), (Sum.inr 3064, 1), (Sum.inr 3086, 1), (Sum.inr 3088, 1), (Sum.inr 3101, 1)]

theorem sourceEq606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm606 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA606 + difference 0 1) (sourceB606 + difference 1 0) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA606 + difference 0 1) (sourceB606 + difference 1 0) sourceC606) = raw10160 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw10160; decide +kernel
    rw [ha]
    exact (canonical10160 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA606 + difference 0 2) (sourceB606 + difference 2 0) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA606 + difference 0 2) (sourceB606 + difference 2 0) sourceC606) = raw10161 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw10161; decide +kernel
    rw [ha]
    exact (canonical10161 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA606 + difference 0 3) (sourceB606 + difference 3 0) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA606 + difference 0 3) (sourceB606 + difference 3 0) sourceC606) = raw10162 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw10162; decide +kernel
    rw [ha]
    exact (canonical10162 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA606 + difference 0 4) (sourceB606 + difference 4 0) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA606 + difference 0 4) (sourceB606 + difference 4 0) sourceC606) = raw9678 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw9678; decide +kernel
    rw [ha]
    exact (canonical9678 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA606 + difference 0 5) (sourceB606 + difference 5 0) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA606 + difference 0 5) (sourceB606 + difference 5 0) sourceC606) = raw9918 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw9918; decide +kernel
    rw [ha]
    exact (canonical9918 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA606 + difference 1 0) (sourceB606 + difference 0 1) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA606 + difference 1 0) (sourceB606 + difference 0 1) sourceC606) = raw10163 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw10163; decide +kernel
    rw [ha]
    exact (canonical10163 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA606 + difference 1 2) (sourceB606 + difference 2 1) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA606 + difference 1 2) (sourceB606 + difference 2 1) sourceC606) = raw10164 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw10164; decide +kernel
    rw [ha]
    exact (canonical10164 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA606 + difference 1 3) (sourceB606 + difference 3 1) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA606 + difference 1 3) (sourceB606 + difference 3 1) sourceC606) = raw10165 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw10165; decide +kernel
    rw [ha]
    exact (canonical10165 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA606 + difference 1 4) (sourceB606 + difference 4 1) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA606 + difference 1 4) (sourceB606 + difference 4 1) sourceC606) = raw9683 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw9683; decide +kernel
    rw [ha]
    exact (canonical9683 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA606 + difference 1 5) (sourceB606 + difference 5 1) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA606 + difference 1 5) (sourceB606 + difference 5 1) sourceC606) = raw9923 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw9923; decide +kernel
    rw [ha]
    exact (canonical9923 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA606 + difference 2 0) (sourceB606 + difference 0 2) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA606 + difference 2 0) (sourceB606 + difference 0 2) sourceC606) = raw10166 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw10166; decide +kernel
    rw [ha]
    exact (canonical10166 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA606 + difference 2 1) (sourceB606 + difference 1 2) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA606 + difference 2 1) (sourceB606 + difference 1 2) sourceC606) = raw10167 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw10167; decide +kernel
    rw [ha]
    exact (canonical10167 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA606 + difference 2 3) (sourceB606 + difference 3 2) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA606 + difference 2 3) (sourceB606 + difference 3 2) sourceC606) = raw10168 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw10168; decide +kernel
    rw [ha]
    exact (canonical10168 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA606 + difference 2 4) (sourceB606 + difference 4 2) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA606 + difference 2 4) (sourceB606 + difference 4 2) sourceC606) = raw9687 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw9687; decide +kernel
    rw [ha]
    exact (canonical9687 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA606 + difference 2 5) (sourceB606 + difference 5 2) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA606 + difference 2 5) (sourceB606 + difference 5 2) sourceC606) = raw9928 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw9928; decide +kernel
    rw [ha]
    exact (canonical9928 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA606 + difference 3 0) (sourceB606 + difference 0 3) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA606 + difference 3 0) (sourceB606 + difference 0 3) sourceC606) = raw9692 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw9692; decide +kernel
    rw [ha]
    exact (canonical9692 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA606 + difference 3 1) (sourceB606 + difference 1 3) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2786) := by
    have ha : (tripleCharges (sourceA606 + difference 3 1) (sourceB606 + difference 1 3) sourceC606) = raw7942 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw7942; decide +kernel
    rw [ha]
    exact (canonical7942 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA606 + difference 3 2) (sourceB606 + difference 2 3) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA606 + difference 3 2) (sourceB606 + difference 2 3) sourceC606) = raw9693 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw9693; decide +kernel
    rw [ha]
    exact (canonical9693 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA606 + difference 3 4) (sourceB606 + difference 4 3) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA606 + difference 3 4) (sourceB606 + difference 4 3) sourceC606) = raw10169 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw10169; decide +kernel
    rw [ha]
    exact (canonical10169 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA606 + difference 3 5) (sourceB606 + difference 5 3) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA606 + difference 3 5) (sourceB606 + difference 5 3) sourceC606) = raw7936 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw7936; decide +kernel
    rw [ha]
    exact (canonical7936 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA606 + difference 4 0) (sourceB606 + difference 0 4) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA606 + difference 4 0) (sourceB606 + difference 0 4) sourceC606) = raw9935 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw9935; decide +kernel
    rw [ha]
    exact (canonical9935 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA606 + difference 4 1) (sourceB606 + difference 1 4) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA606 + difference 4 1) (sourceB606 + difference 1 4) sourceC606) = raw9936 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw9936; decide +kernel
    rw [ha]
    exact (canonical9936 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA606 + difference 4 2) (sourceB606 + difference 2 4) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA606 + difference 4 2) (sourceB606 + difference 2 4) sourceC606) = raw9937 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw9937; decide +kernel
    rw [ha]
    exact (canonical9937 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA606 + difference 4 3) (sourceB606 + difference 3 4) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA606 + difference 4 3) (sourceB606 + difference 3 4) sourceC606) = raw9938 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw9938; decide +kernel
    rw [ha]
    exact (canonical9938 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA606 + difference 4 5) (sourceB606 + difference 5 4) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA606 + difference 4 5) (sourceB606 + difference 5 4) sourceC606) = raw10170 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw10170; decide +kernel
    rw [ha]
    exact (canonical10170 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA606 + difference 5 0) (sourceB606 + difference 0 5) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA606 + difference 5 0) (sourceB606 + difference 0 5) sourceC606) = raw10171 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw10171; decide +kernel
    rw [ha]
    exact (canonical10171 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA606 + difference 5 1) (sourceB606 + difference 1 5) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA606 + difference 5 1) (sourceB606 + difference 1 5) sourceC606) = raw10172 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw10172; decide +kernel
    rw [ha]
    exact (canonical10172 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA606 + difference 5 2) (sourceB606 + difference 2 5) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA606 + difference 5 2) (sourceB606 + difference 2 5) sourceC606) = raw10173 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw10173; decide +kernel
    rw [ha]
    exact (canonical10173 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA606 + difference 5 3) (sourceB606 + difference 3 5) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA606 + difference 5 3) (sourceB606 + difference 3 5) sourceC606) = raw10174 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw10174; decide +kernel
    rw [ha]
    exact (canonical10174 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA606 + difference 5 4) (sourceB606 + difference 4 5) sourceC606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA606 + difference 5 4) (sourceB606 + difference 4 5) sourceC606) = raw9698 := by
      apply Matrix.ext; unfold tripleCharges sourceA606 sourceB606 sourceC606 difference raw9698; decide +kernel
    rw [ha]
    exact (canonical9698 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA606 sourceB606 sourceC606
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm606, Integer.Sparse.eval]
  linarith only [hs]

def sourceA607 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB607 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC607 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm607 : Integer.Sparse Master := [(Sum.inr 2710, 1), (Sum.inr 2723, 1), (Sum.inr 2724, 1), (Sum.inr 2732, 1), (Sum.inr 2768, 1), (Sum.inr 2940, 1), (Sum.inr 2941, 1), (Sum.inr 2942, 1), (Sum.inr 2964, 1), (Sum.inr 3030, 1), (Sum.inr 3039, 1), (Sum.inr 3040, 1), (Sum.inr 3045, 1), (Sum.inr 3065, 1), (Sum.inr 3066, 1), (Sum.inr 3069, 1), (Sum.inr 3081, 1), (Sum.inr 3088, 1), (Sum.inr 3089, 2), (Sum.inr 3094, 1), (Sum.inr 3102, 1), (Sum.inr 3103, 1), (Sum.inr 3112, 1), (Sum.inr 3113, 1), (Sum.inr 3124, 1), (Sum.inr 3205, 1), (Sum.inr 3206, 1), (Sum.inr 3214, 1), (Sum.inr 3230, 1)]

theorem sourceEq607 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm607 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA607 + difference 0 1) (sourceB607 + difference 1 0) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA607 + difference 0 1) (sourceB607 + difference 1 0) sourceC607) = raw10175 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw10175; decide +kernel
    rw [ha]
    exact (canonical10175 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA607 + difference 0 2) (sourceB607 + difference 2 0) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA607 + difference 0 2) (sourceB607 + difference 2 0) sourceC607) = raw10176 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw10176; decide +kernel
    rw [ha]
    exact (canonical10176 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA607 + difference 0 3) (sourceB607 + difference 3 0) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA607 + difference 0 3) (sourceB607 + difference 3 0) sourceC607) = raw10177 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw10177; decide +kernel
    rw [ha]
    exact (canonical10177 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA607 + difference 0 4) (sourceB607 + difference 4 0) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA607 + difference 0 4) (sourceB607 + difference 4 0) sourceC607) = raw9702 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw9702; decide +kernel
    rw [ha]
    exact (canonical9702 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA607 + difference 0 5) (sourceB607 + difference 5 0) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA607 + difference 0 5) (sourceB607 + difference 5 0) sourceC607) = raw9942 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw9942; decide +kernel
    rw [ha]
    exact (canonical9942 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA607 + difference 1 0) (sourceB607 + difference 0 1) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA607 + difference 1 0) (sourceB607 + difference 0 1) sourceC607) = raw10178 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw10178; decide +kernel
    rw [ha]
    exact (canonical10178 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA607 + difference 1 2) (sourceB607 + difference 2 1) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3030) := by
    have ha : (tripleCharges (sourceA607 + difference 1 2) (sourceB607 + difference 2 1) sourceC607) = raw10179 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw10179; decide +kernel
    rw [ha]
    exact (canonical10179 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA607 + difference 1 3) (sourceB607 + difference 3 1) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3045) := by
    have ha : (tripleCharges (sourceA607 + difference 1 3) (sourceB607 + difference 3 1) sourceC607) = raw10180 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw10180; decide +kernel
    rw [ha]
    exact (canonical10180 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA607 + difference 1 4) (sourceB607 + difference 4 1) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3040) := by
    have ha : (tripleCharges (sourceA607 + difference 1 4) (sourceB607 + difference 4 1) sourceC607) = raw9707 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw9707; decide +kernel
    rw [ha]
    exact (canonical9707 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA607 + difference 1 5) (sourceB607 + difference 5 1) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA607 + difference 1 5) (sourceB607 + difference 5 1) sourceC607) = raw9947 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw9947; decide +kernel
    rw [ha]
    exact (canonical9947 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA607 + difference 2 0) (sourceB607 + difference 0 2) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3205) := by
    have ha : (tripleCharges (sourceA607 + difference 2 0) (sourceB607 + difference 0 2) sourceC607) = raw10181 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw10181; decide +kernel
    rw [ha]
    exact (canonical10181 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA607 + difference 2 1) (sourceB607 + difference 1 2) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA607 + difference 2 1) (sourceB607 + difference 1 2) sourceC607) = raw10182 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw10182; decide +kernel
    rw [ha]
    exact (canonical10182 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA607 + difference 2 3) (sourceB607 + difference 3 2) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3069) := by
    have ha : (tripleCharges (sourceA607 + difference 2 3) (sourceB607 + difference 3 2) sourceC607) = raw10183 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw10183; decide +kernel
    rw [ha]
    exact (canonical10183 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA607 + difference 2 4) (sourceB607 + difference 4 2) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3066) := by
    have ha : (tripleCharges (sourceA607 + difference 2 4) (sourceB607 + difference 4 2) sourceC607) = raw9711 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw9711; decide +kernel
    rw [ha]
    exact (canonical9711 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA607 + difference 2 5) (sourceB607 + difference 5 2) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA607 + difference 2 5) (sourceB607 + difference 5 2) sourceC607) = raw9952 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw9952; decide +kernel
    rw [ha]
    exact (canonical9952 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA607 + difference 3 0) (sourceB607 + difference 0 3) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA607 + difference 3 0) (sourceB607 + difference 0 3) sourceC607) = raw9716 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw9716; decide +kernel
    rw [ha]
    exact (canonical9716 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA607 + difference 3 1) (sourceB607 + difference 1 3) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA607 + difference 3 1) (sourceB607 + difference 1 3) sourceC607) = raw7955 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw7955; decide +kernel
    rw [ha]
    exact (canonical7955 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA607 + difference 3 2) (sourceB607 + difference 2 3) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA607 + difference 3 2) (sourceB607 + difference 2 3) sourceC607) = raw9717 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw9717; decide +kernel
    rw [ha]
    exact (canonical9717 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA607 + difference 3 4) (sourceB607 + difference 4 3) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA607 + difference 3 4) (sourceB607 + difference 4 3) sourceC607) = raw10184 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw10184; decide +kernel
    rw [ha]
    exact (canonical10184 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA607 + difference 3 5) (sourceB607 + difference 5 3) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA607 + difference 3 5) (sourceB607 + difference 5 3) sourceC607) = raw7949 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw7949; decide +kernel
    rw [ha]
    exact (canonical7949 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA607 + difference 4 0) (sourceB607 + difference 0 4) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3214) := by
    have ha : (tripleCharges (sourceA607 + difference 4 0) (sourceB607 + difference 0 4) sourceC607) = raw9959 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw9959; decide +kernel
    rw [ha]
    exact (canonical9959 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA607 + difference 4 1) (sourceB607 + difference 1 4) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA607 + difference 4 1) (sourceB607 + difference 1 4) sourceC607) = raw9960 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw9960; decide +kernel
    rw [ha]
    exact (canonical9960 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA607 + difference 4 2) (sourceB607 + difference 2 4) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3081) := by
    have ha : (tripleCharges (sourceA607 + difference 4 2) (sourceB607 + difference 2 4) sourceC607) = raw9961 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw9961; decide +kernel
    rw [ha]
    exact (canonical9961 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA607 + difference 4 3) (sourceB607 + difference 3 4) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3094) := by
    have ha : (tripleCharges (sourceA607 + difference 4 3) (sourceB607 + difference 3 4) sourceC607) = raw9962 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw9962; decide +kernel
    rw [ha]
    exact (canonical9962 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA607 + difference 4 5) (sourceB607 + difference 5 4) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA607 + difference 4 5) (sourceB607 + difference 5 4) sourceC607) = raw10185 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw10185; decide +kernel
    rw [ha]
    exact (canonical10185 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA607 + difference 5 0) (sourceB607 + difference 0 5) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA607 + difference 5 0) (sourceB607 + difference 0 5) sourceC607) = raw10186 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw10186; decide +kernel
    rw [ha]
    exact (canonical10186 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA607 + difference 5 1) (sourceB607 + difference 1 5) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3113) := by
    have ha : (tripleCharges (sourceA607 + difference 5 1) (sourceB607 + difference 1 5) sourceC607) = raw10187 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw10187; decide +kernel
    rw [ha]
    exact (canonical10187 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA607 + difference 5 2) (sourceB607 + difference 2 5) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2940) := by
    have ha : (tripleCharges (sourceA607 + difference 5 2) (sourceB607 + difference 2 5) sourceC607) = raw10188 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw10188; decide +kernel
    rw [ha]
    exact (canonical10188 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA607 + difference 5 3) (sourceB607 + difference 3 5) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA607 + difference 5 3) (sourceB607 + difference 3 5) sourceC607) = raw10189 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw10189; decide +kernel
    rw [ha]
    exact (canonical10189 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA607 + difference 5 4) (sourceB607 + difference 4 5) sourceC607) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA607 + difference 5 4) (sourceB607 + difference 4 5) sourceC607) = raw9722 := by
      apply Matrix.ext; unfold tripleCharges sourceA607 sourceB607 sourceC607 difference raw9722; decide +kernel
    rw [ha]
    exact (canonical9722 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA607 sourceB607 sourceC607
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm607, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
