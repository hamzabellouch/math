import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical63

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA416 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB416 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC416 : Charge := ![2, 0, 0, 0, -3, 1]
def sourceForm416 : Integer.Sparse Master := [(Sum.inr 1287, 3), (Sum.inr 1289, 1), (Sum.inr 1310, 1), (Sum.inr 1659, 3), (Sum.inr 1747, 1), (Sum.inr 2267, 3), (Sum.inr 2294, 1), (Sum.inr 2725, 6), (Sum.inr 2744, 3), (Sum.inr 2769, 3), (Sum.inr 2788, 1), (Sum.inr 2967, 3), (Sum.inr 3125, 1)]

theorem sourceEq416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm416 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA416 + difference 0 1) (sourceB416 + difference 1 0) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA416 + difference 0 1) (sourceB416 + difference 1 0) sourceC416) = raw7731 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7731; decide +kernel
    rw [ha]
    exact (canonical7731 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA416 + difference 0 2) (sourceB416 + difference 2 0) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA416 + difference 0 2) (sourceB416 + difference 2 0) sourceC416) = raw7732 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7732; decide +kernel
    rw [ha]
    exact (canonical7732 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA416 + difference 0 3) (sourceB416 + difference 3 0) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA416 + difference 0 3) (sourceB416 + difference 3 0) sourceC416) = raw7733 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7733; decide +kernel
    rw [ha]
    exact (canonical7733 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA416 + difference 0 4) (sourceB416 + difference 4 0) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA416 + difference 0 4) (sourceB416 + difference 4 0) sourceC416) = raw7734 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7734; decide +kernel
    rw [ha]
    exact (canonical7734 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA416 + difference 0 5) (sourceB416 + difference 5 0) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA416 + difference 0 5) (sourceB416 + difference 5 0) sourceC416) = raw7735 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7735; decide +kernel
    rw [ha]
    exact (canonical7735 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA416 + difference 1 0) (sourceB416 + difference 0 1) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1287) := by
    have ha : (tripleCharges (sourceA416 + difference 1 0) (sourceB416 + difference 0 1) sourceC416) = raw7736 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7736; decide +kernel
    rw [ha]
    exact (canonical7736 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA416 + difference 1 2) (sourceB416 + difference 2 1) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2725) := by
    have ha : (tripleCharges (sourceA416 + difference 1 2) (sourceB416 + difference 2 1) sourceC416) = raw7737 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7737; decide +kernel
    rw [ha]
    exact (canonical7737 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA416 + difference 1 3) (sourceB416 + difference 3 1) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2725) := by
    have ha : (tripleCharges (sourceA416 + difference 1 3) (sourceB416 + difference 3 1) sourceC416) = raw7738 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7738; decide +kernel
    rw [ha]
    exact (canonical7738 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA416 + difference 1 4) (sourceB416 + difference 4 1) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA416 + difference 1 4) (sourceB416 + difference 4 1) sourceC416) = raw7739 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7739; decide +kernel
    rw [ha]
    exact (canonical7739 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA416 + difference 1 5) (sourceB416 + difference 5 1) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA416 + difference 1 5) (sourceB416 + difference 5 1) sourceC416) = raw7740 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7740; decide +kernel
    rw [ha]
    exact (canonical7740 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA416 + difference 2 0) (sourceB416 + difference 0 2) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1287) := by
    have ha : (tripleCharges (sourceA416 + difference 2 0) (sourceB416 + difference 0 2) sourceC416) = raw7741 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7741; decide +kernel
    rw [ha]
    exact (canonical7741 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA416 + difference 2 1) (sourceB416 + difference 1 2) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2725) := by
    have ha : (tripleCharges (sourceA416 + difference 2 1) (sourceB416 + difference 1 2) sourceC416) = raw7742 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7742; decide +kernel
    rw [ha]
    exact (canonical7742 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA416 + difference 2 3) (sourceB416 + difference 3 2) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2725) := by
    have ha : (tripleCharges (sourceA416 + difference 2 3) (sourceB416 + difference 3 2) sourceC416) = raw7743 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7743; decide +kernel
    rw [ha]
    exact (canonical7743 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA416 + difference 2 4) (sourceB416 + difference 4 2) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA416 + difference 2 4) (sourceB416 + difference 4 2) sourceC416) = raw7744 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7744; decide +kernel
    rw [ha]
    exact (canonical7744 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA416 + difference 2 5) (sourceB416 + difference 5 2) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA416 + difference 2 5) (sourceB416 + difference 5 2) sourceC416) = raw7745 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7745; decide +kernel
    rw [ha]
    exact (canonical7745 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA416 + difference 3 0) (sourceB416 + difference 0 3) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1287) := by
    have ha : (tripleCharges (sourceA416 + difference 3 0) (sourceB416 + difference 0 3) sourceC416) = raw7746 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7746; decide +kernel
    rw [ha]
    exact (canonical7746 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA416 + difference 3 1) (sourceB416 + difference 1 3) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2725) := by
    have ha : (tripleCharges (sourceA416 + difference 3 1) (sourceB416 + difference 1 3) sourceC416) = raw7747 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7747; decide +kernel
    rw [ha]
    exact (canonical7747 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA416 + difference 3 2) (sourceB416 + difference 2 3) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2725) := by
    have ha : (tripleCharges (sourceA416 + difference 3 2) (sourceB416 + difference 2 3) sourceC416) = raw7748 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7748; decide +kernel
    rw [ha]
    exact (canonical7748 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA416 + difference 3 4) (sourceB416 + difference 4 3) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA416 + difference 3 4) (sourceB416 + difference 4 3) sourceC416) = raw7749 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7749; decide +kernel
    rw [ha]
    exact (canonical7749 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA416 + difference 3 5) (sourceB416 + difference 5 3) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA416 + difference 3 5) (sourceB416 + difference 5 3) sourceC416) = raw7750 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7750; decide +kernel
    rw [ha]
    exact (canonical7750 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA416 + difference 4 0) (sourceB416 + difference 0 4) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1310) := by
    have ha : (tripleCharges (sourceA416 + difference 4 0) (sourceB416 + difference 0 4) sourceC416) = raw7751 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7751; decide +kernel
    rw [ha]
    exact (canonical7751 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA416 + difference 4 1) (sourceB416 + difference 1 4) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA416 + difference 4 1) (sourceB416 + difference 1 4) sourceC416) = raw7752 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7752; decide +kernel
    rw [ha]
    exact (canonical7752 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA416 + difference 4 2) (sourceB416 + difference 2 4) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA416 + difference 4 2) (sourceB416 + difference 2 4) sourceC416) = raw7753 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7753; decide +kernel
    rw [ha]
    exact (canonical7753 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA416 + difference 4 3) (sourceB416 + difference 3 4) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA416 + difference 4 3) (sourceB416 + difference 3 4) sourceC416) = raw7754 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7754; decide +kernel
    rw [ha]
    exact (canonical7754 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA416 + difference 4 5) (sourceB416 + difference 5 4) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3125) := by
    have ha : (tripleCharges (sourceA416 + difference 4 5) (sourceB416 + difference 5 4) sourceC416) = raw7755 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7755; decide +kernel
    rw [ha]
    exact (canonical7755 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA416 + difference 5 0) (sourceB416 + difference 0 5) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1289) := by
    have ha : (tripleCharges (sourceA416 + difference 5 0) (sourceB416 + difference 0 5) sourceC416) = raw7756 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7756; decide +kernel
    rw [ha]
    exact (canonical7756 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA416 + difference 5 1) (sourceB416 + difference 1 5) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1659) := by
    have ha : (tripleCharges (sourceA416 + difference 5 1) (sourceB416 + difference 1 5) sourceC416) = raw7757 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7757; decide +kernel
    rw [ha]
    exact (canonical7757 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA416 + difference 5 2) (sourceB416 + difference 2 5) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1659) := by
    have ha : (tripleCharges (sourceA416 + difference 5 2) (sourceB416 + difference 2 5) sourceC416) = raw7758 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7758; decide +kernel
    rw [ha]
    exact (canonical7758 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA416 + difference 5 3) (sourceB416 + difference 3 5) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1659) := by
    have ha : (tripleCharges (sourceA416 + difference 5 3) (sourceB416 + difference 3 5) sourceC416) = raw7759 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7759; decide +kernel
    rw [ha]
    exact (canonical7759 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA416 + difference 5 4) (sourceB416 + difference 4 5) sourceC416) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1747) := by
    have ha : (tripleCharges (sourceA416 + difference 5 4) (sourceB416 + difference 4 5) sourceC416) = raw7760 := by
      apply Matrix.ext; unfold tripleCharges sourceA416 sourceB416 sourceC416 difference raw7760; decide +kernel
    rw [ha]
    exact (canonical7760 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA416 sourceB416 sourceC416
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm416, Integer.Sparse.eval]
  linarith only [hs]

def sourceA417 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB417 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC417 : Charge := ![2, 0, 0, 0, -3, 1]
def sourceForm417 : Integer.Sparse Master := [(Sum.inr 1088, 3), (Sum.inr 1092, 1), (Sum.inr 1093, 1), (Sum.inr 2516, 6), (Sum.inr 2520, 3), (Sum.inr 2521, 3), (Sum.inr 2761, 3), (Sum.inr 2777, 3), (Sum.inr 2778, 1), (Sum.inr 2780, 1), (Sum.inr 2783, 1), (Sum.inr 3098, 3), (Sum.inr 3121, 1)]

theorem sourceEq417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm417 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA417 + difference 0 1) (sourceB417 + difference 1 0) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA417 + difference 0 1) (sourceB417 + difference 1 0) sourceC417) = raw7761 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7761; decide +kernel
    rw [ha]
    exact (canonical7761 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA417 + difference 0 2) (sourceB417 + difference 2 0) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA417 + difference 0 2) (sourceB417 + difference 2 0) sourceC417) = raw7762 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7762; decide +kernel
    rw [ha]
    exact (canonical7762 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA417 + difference 0 3) (sourceB417 + difference 3 0) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA417 + difference 0 3) (sourceB417 + difference 3 0) sourceC417) = raw7763 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7763; decide +kernel
    rw [ha]
    exact (canonical7763 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA417 + difference 0 4) (sourceB417 + difference 4 0) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2778) := by
    have ha : (tripleCharges (sourceA417 + difference 0 4) (sourceB417 + difference 4 0) sourceC417) = raw7764 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7764; decide +kernel
    rw [ha]
    exact (canonical7764 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA417 + difference 0 5) (sourceB417 + difference 5 0) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA417 + difference 0 5) (sourceB417 + difference 5 0) sourceC417) = raw7765 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7765; decide +kernel
    rw [ha]
    exact (canonical7765 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA417 + difference 1 0) (sourceB417 + difference 0 1) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2521) := by
    have ha : (tripleCharges (sourceA417 + difference 1 0) (sourceB417 + difference 0 1) sourceC417) = raw7766 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7766; decide +kernel
    rw [ha]
    exact (canonical7766 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA417 + difference 1 2) (sourceB417 + difference 2 1) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA417 + difference 1 2) (sourceB417 + difference 2 1) sourceC417) = raw7767 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7767; decide +kernel
    rw [ha]
    exact (canonical7767 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA417 + difference 1 3) (sourceB417 + difference 3 1) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA417 + difference 1 3) (sourceB417 + difference 3 1) sourceC417) = raw7768 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7768; decide +kernel
    rw [ha]
    exact (canonical7768 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA417 + difference 1 4) (sourceB417 + difference 4 1) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA417 + difference 1 4) (sourceB417 + difference 4 1) sourceC417) = raw7769 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7769; decide +kernel
    rw [ha]
    exact (canonical7769 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA417 + difference 1 5) (sourceB417 + difference 5 1) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA417 + difference 1 5) (sourceB417 + difference 5 1) sourceC417) = raw7770 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7770; decide +kernel
    rw [ha]
    exact (canonical7770 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA417 + difference 2 0) (sourceB417 + difference 0 2) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2521) := by
    have ha : (tripleCharges (sourceA417 + difference 2 0) (sourceB417 + difference 0 2) sourceC417) = raw7771 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7771; decide +kernel
    rw [ha]
    exact (canonical7771 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA417 + difference 2 1) (sourceB417 + difference 1 2) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA417 + difference 2 1) (sourceB417 + difference 1 2) sourceC417) = raw7772 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7772; decide +kernel
    rw [ha]
    exact (canonical7772 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA417 + difference 2 3) (sourceB417 + difference 3 2) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA417 + difference 2 3) (sourceB417 + difference 3 2) sourceC417) = raw7773 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7773; decide +kernel
    rw [ha]
    exact (canonical7773 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA417 + difference 2 4) (sourceB417 + difference 4 2) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA417 + difference 2 4) (sourceB417 + difference 4 2) sourceC417) = raw7774 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7774; decide +kernel
    rw [ha]
    exact (canonical7774 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA417 + difference 2 5) (sourceB417 + difference 5 2) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA417 + difference 2 5) (sourceB417 + difference 5 2) sourceC417) = raw7775 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7775; decide +kernel
    rw [ha]
    exact (canonical7775 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA417 + difference 3 0) (sourceB417 + difference 0 3) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2521) := by
    have ha : (tripleCharges (sourceA417 + difference 3 0) (sourceB417 + difference 0 3) sourceC417) = raw7776 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7776; decide +kernel
    rw [ha]
    exact (canonical7776 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA417 + difference 3 1) (sourceB417 + difference 1 3) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA417 + difference 3 1) (sourceB417 + difference 1 3) sourceC417) = raw7777 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7777; decide +kernel
    rw [ha]
    exact (canonical7777 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA417 + difference 3 2) (sourceB417 + difference 2 3) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA417 + difference 3 2) (sourceB417 + difference 2 3) sourceC417) = raw7778 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7778; decide +kernel
    rw [ha]
    exact (canonical7778 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA417 + difference 3 4) (sourceB417 + difference 4 3) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA417 + difference 3 4) (sourceB417 + difference 4 3) sourceC417) = raw7779 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7779; decide +kernel
    rw [ha]
    exact (canonical7779 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA417 + difference 3 5) (sourceB417 + difference 5 3) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA417 + difference 3 5) (sourceB417 + difference 5 3) sourceC417) = raw7780 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7780; decide +kernel
    rw [ha]
    exact (canonical7780 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA417 + difference 4 0) (sourceB417 + difference 0 4) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2780) := by
    have ha : (tripleCharges (sourceA417 + difference 4 0) (sourceB417 + difference 0 4) sourceC417) = raw7781 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7781; decide +kernel
    rw [ha]
    exact (canonical7781 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA417 + difference 4 1) (sourceB417 + difference 1 4) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA417 + difference 4 1) (sourceB417 + difference 1 4) sourceC417) = raw7782 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7782; decide +kernel
    rw [ha]
    exact (canonical7782 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA417 + difference 4 2) (sourceB417 + difference 2 4) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA417 + difference 4 2) (sourceB417 + difference 2 4) sourceC417) = raw7783 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7783; decide +kernel
    rw [ha]
    exact (canonical7783 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA417 + difference 4 3) (sourceB417 + difference 3 4) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA417 + difference 4 3) (sourceB417 + difference 3 4) sourceC417) = raw7784 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7784; decide +kernel
    rw [ha]
    exact (canonical7784 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA417 + difference 4 5) (sourceB417 + difference 5 4) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA417 + difference 4 5) (sourceB417 + difference 5 4) sourceC417) = raw7785 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7785; decide +kernel
    rw [ha]
    exact (canonical7785 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA417 + difference 5 0) (sourceB417 + difference 0 5) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1093) := by
    have ha : (tripleCharges (sourceA417 + difference 5 0) (sourceB417 + difference 0 5) sourceC417) = raw7786 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7786; decide +kernel
    rw [ha]
    exact (canonical7786 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA417 + difference 5 1) (sourceB417 + difference 1 5) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1088) := by
    have ha : (tripleCharges (sourceA417 + difference 5 1) (sourceB417 + difference 1 5) sourceC417) = raw7787 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7787; decide +kernel
    rw [ha]
    exact (canonical7787 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA417 + difference 5 2) (sourceB417 + difference 2 5) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1088) := by
    have ha : (tripleCharges (sourceA417 + difference 5 2) (sourceB417 + difference 2 5) sourceC417) = raw7788 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7788; decide +kernel
    rw [ha]
    exact (canonical7788 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA417 + difference 5 3) (sourceB417 + difference 3 5) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1088) := by
    have ha : (tripleCharges (sourceA417 + difference 5 3) (sourceB417 + difference 3 5) sourceC417) = raw7789 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7789; decide +kernel
    rw [ha]
    exact (canonical7789 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA417 + difference 5 4) (sourceB417 + difference 4 5) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1092) := by
    have ha : (tripleCharges (sourceA417 + difference 5 4) (sourceB417 + difference 4 5) sourceC417) = raw7790 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7790; decide +kernel
    rw [ha]
    exact (canonical7790 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA417 sourceB417 sourceC417
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm417, Integer.Sparse.eval]
  linarith only [hs]

def sourceA418 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB418 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC418 : Charge := ![2, 0, 0, 0, -3, 1]
def sourceForm418 : Integer.Sparse Master := [(Sum.inr 1303, 3), (Sum.inr 1309, 1), (Sum.inr 1310, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

theorem sourceEq418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm418 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA418 + difference 0 0) (sourceB418 + difference 0 0) sourceC418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA418 + difference 0 0) (sourceB418 + difference 0 0) sourceC418) = raw7791 := by
      apply Matrix.ext; unfold tripleCharges sourceA418 sourceB418 sourceC418 difference raw7791; decide +kernel
    rw [ha]
    exact (canonical7791 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA418 + difference 1 0) (sourceB418 + difference 0 1) sourceC418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1303) := by
    have ha : (tripleCharges (sourceA418 + difference 1 0) (sourceB418 + difference 0 1) sourceC418) = raw7792 := by
      apply Matrix.ext; unfold tripleCharges sourceA418 sourceB418 sourceC418 difference raw7792; decide +kernel
    rw [ha]
    exact (canonical7792 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA418 + difference 2 0) (sourceB418 + difference 0 2) sourceC418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1303) := by
    have ha : (tripleCharges (sourceA418 + difference 2 0) (sourceB418 + difference 0 2) sourceC418) = raw7793 := by
      apply Matrix.ext; unfold tripleCharges sourceA418 sourceB418 sourceC418 difference raw7793; decide +kernel
    rw [ha]
    exact (canonical7793 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA418 + difference 3 0) (sourceB418 + difference 0 3) sourceC418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1303) := by
    have ha : (tripleCharges (sourceA418 + difference 3 0) (sourceB418 + difference 0 3) sourceC418) = raw7794 := by
      apply Matrix.ext; unfold tripleCharges sourceA418 sourceB418 sourceC418 difference raw7794; decide +kernel
    rw [ha]
    exact (canonical7794 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA418 + difference 4 0) (sourceB418 + difference 0 4) sourceC418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1310) := by
    have ha : (tripleCharges (sourceA418 + difference 4 0) (sourceB418 + difference 0 4) sourceC418) = raw7795 := by
      apply Matrix.ext; unfold tripleCharges sourceA418 sourceB418 sourceC418 difference raw7795; decide +kernel
    rw [ha]
    exact (canonical7795 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA418 + difference 5 0) (sourceB418 + difference 0 5) sourceC418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1309) := by
    have ha : (tripleCharges (sourceA418 + difference 5 0) (sourceB418 + difference 0 5) sourceC418) = raw7796 := by
      apply Matrix.ext; unfold tripleCharges sourceA418 sourceB418 sourceC418 difference raw7796; decide +kernel
    rw [ha]
    exact (canonical7796 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA418 + sourceB418) sourceC418) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA418 + sourceB418) sourceC418) = raw7797 := by
      apply Matrix.ext; unfold doubleCharges sourceA418 sourceB418 sourceC418 raw7797; decide +kernel
    rw [ha]
    exact (canonical7797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA418 sourceB418 sourceC418
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm418, Integer.Sparse.eval]
  linarith only [hs]

def sourceA419 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB419 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC419 : Charge := ![2, 0, 0, 0, -3, 1]
def sourceForm419 : Integer.Sparse Master := [(Sum.inr 1303, 1), (Sum.inr 2134, 1), (Sum.inr 2597, 2), (Sum.inr 2781, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

theorem sourceEq419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm419 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA419 + difference 1 0) (sourceB419 + difference 0 1) sourceC419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1303) := by
    have ha : (tripleCharges (sourceA419 + difference 1 0) (sourceB419 + difference 0 1) sourceC419) = raw7792 := by
      apply Matrix.ext; unfold tripleCharges sourceA419 sourceB419 sourceC419 difference raw7792; decide +kernel
    rw [ha]
    exact (canonical7792 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA419 + difference 1 1) (sourceB419 + difference 1 1) sourceC419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA419 + difference 1 1) (sourceB419 + difference 1 1) sourceC419) = raw7791 := by
      apply Matrix.ext; unfold tripleCharges sourceA419 sourceB419 sourceC419 difference raw7791; decide +kernel
    rw [ha]
    exact (canonical7791 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA419 + difference 1 2) (sourceB419 + difference 2 1) sourceC419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2597) := by
    have ha : (tripleCharges (sourceA419 + difference 1 2) (sourceB419 + difference 2 1) sourceC419) = raw7798 := by
      apply Matrix.ext; unfold tripleCharges sourceA419 sourceB419 sourceC419 difference raw7798; decide +kernel
    rw [ha]
    exact (canonical7798 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA419 + difference 1 3) (sourceB419 + difference 3 1) sourceC419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2597) := by
    have ha : (tripleCharges (sourceA419 + difference 1 3) (sourceB419 + difference 3 1) sourceC419) = raw7799 := by
      apply Matrix.ext; unfold tripleCharges sourceA419 sourceB419 sourceC419 difference raw7799; decide +kernel
    rw [ha]
    exact (canonical7799 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA419 + difference 1 4) (sourceB419 + difference 4 1) sourceC419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA419 + difference 1 4) (sourceB419 + difference 4 1) sourceC419) = raw7800 := by
      apply Matrix.ext; unfold tripleCharges sourceA419 sourceB419 sourceC419 difference raw7800; decide +kernel
    rw [ha]
    exact (canonical7800 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA419 + difference 1 5) (sourceB419 + difference 5 1) sourceC419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA419 + difference 1 5) (sourceB419 + difference 5 1) sourceC419) = raw7801 := by
      apply Matrix.ext; unfold tripleCharges sourceA419 sourceB419 sourceC419 difference raw7801; decide +kernel
    rw [ha]
    exact (canonical7801 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA419 + sourceB419) sourceC419) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA419 + sourceB419) sourceC419) = raw7797 := by
      apply Matrix.ext; unfold doubleCharges sourceA419 sourceB419 sourceC419 raw7797; decide +kernel
    rw [ha]
    exact (canonical7797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA419 sourceB419 sourceC419
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm419, Integer.Sparse.eval]
  linarith only [hs]

def sourceA420 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB420 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC420 : Charge := ![2, 0, 0, 0, -3, 1]
def sourceForm420 : Integer.Sparse Master := [(Sum.inr 1310, 1), (Sum.inr 2603, 3), (Sum.inr 2783, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

theorem sourceEq420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm420 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA420 + difference 4 0) (sourceB420 + difference 0 4) sourceC420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1310) := by
    have ha : (tripleCharges (sourceA420 + difference 4 0) (sourceB420 + difference 0 4) sourceC420) = raw7795 := by
      apply Matrix.ext; unfold tripleCharges sourceA420 sourceB420 sourceC420 difference raw7795; decide +kernel
    rw [ha]
    exact (canonical7795 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA420 + difference 4 1) (sourceB420 + difference 1 4) sourceC420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2603) := by
    have ha : (tripleCharges (sourceA420 + difference 4 1) (sourceB420 + difference 1 4) sourceC420) = raw7802 := by
      apply Matrix.ext; unfold tripleCharges sourceA420 sourceB420 sourceC420 difference raw7802; decide +kernel
    rw [ha]
    exact (canonical7802 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA420 + difference 4 2) (sourceB420 + difference 2 4) sourceC420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2603) := by
    have ha : (tripleCharges (sourceA420 + difference 4 2) (sourceB420 + difference 2 4) sourceC420) = raw7803 := by
      apply Matrix.ext; unfold tripleCharges sourceA420 sourceB420 sourceC420 difference raw7803; decide +kernel
    rw [ha]
    exact (canonical7803 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA420 + difference 4 3) (sourceB420 + difference 3 4) sourceC420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2603) := by
    have ha : (tripleCharges (sourceA420 + difference 4 3) (sourceB420 + difference 3 4) sourceC420) = raw7804 := by
      apply Matrix.ext; unfold tripleCharges sourceA420 sourceB420 sourceC420 difference raw7804; decide +kernel
    rw [ha]
    exact (canonical7804 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA420 + difference 4 4) (sourceB420 + difference 4 4) sourceC420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA420 + difference 4 4) (sourceB420 + difference 4 4) sourceC420) = raw7791 := by
      apply Matrix.ext; unfold tripleCharges sourceA420 sourceB420 sourceC420 difference raw7791; decide +kernel
    rw [ha]
    exact (canonical7791 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA420 + difference 4 5) (sourceB420 + difference 5 4) sourceC420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA420 + difference 4 5) (sourceB420 + difference 5 4) sourceC420) = raw7805 := by
      apply Matrix.ext; unfold tripleCharges sourceA420 sourceB420 sourceC420 difference raw7805; decide +kernel
    rw [ha]
    exact (canonical7805 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA420 + sourceB420) sourceC420) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA420 + sourceB420) sourceC420) = raw7797 := by
      apply Matrix.ext; unfold doubleCharges sourceA420 sourceB420 sourceC420 raw7797; decide +kernel
    rw [ha]
    exact (canonical7797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA420 sourceB420 sourceC420
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm420, Integer.Sparse.eval]
  linarith only [hs]

def sourceA421 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB421 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC421 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceForm421 : Integer.Sparse Master := [(Sum.inr 4606, 2), (Sum.inr 4608, 1), (Sum.inr 4612, 1), (Sum.inr 4624, 1), (Sum.inr 5078, 2), (Sum.inr 5109, 1), (Sum.inr 5148, 2), (Sum.inr 5152, 2), (Sum.inr 5169, 2), (Sum.inr 5203, 2), (Sum.inr 5207, 1), (Sum.inr 5292, 2), (Sum.inr 5293, 2), (Sum.inr 5294, 1), (Sum.inr 5296, 1), (Sum.inr 5307, 1), (Sum.inr 5309, 1), (Sum.inr 5434, 2), (Sum.inr 5451, 1), (Sum.inr 5454, 1), (Sum.inr 5455, 1)]

theorem sourceEq421 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm421 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA421 + difference 0 1) (sourceB421 + difference 1 0) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA421 + difference 0 1) (sourceB421 + difference 1 0) sourceC421) = raw7806 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7806; decide +kernel
    rw [ha]
    exact (canonical7806 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA421 + difference 0 2) (sourceB421 + difference 2 0) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA421 + difference 0 2) (sourceB421 + difference 2 0) sourceC421) = raw7807 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7807; decide +kernel
    rw [ha]
    exact (canonical7807 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA421 + difference 0 3) (sourceB421 + difference 3 0) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA421 + difference 0 3) (sourceB421 + difference 3 0) sourceC421) = raw7808 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7808; decide +kernel
    rw [ha]
    exact (canonical7808 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA421 + difference 0 4) (sourceB421 + difference 4 0) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA421 + difference 0 4) (sourceB421 + difference 4 0) sourceC421) = raw7809 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7809; decide +kernel
    rw [ha]
    exact (canonical7809 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA421 + difference 0 5) (sourceB421 + difference 5 0) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA421 + difference 0 5) (sourceB421 + difference 5 0) sourceC421) = raw7810 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7810; decide +kernel
    rw [ha]
    exact (canonical7810 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA421 + difference 1 0) (sourceB421 + difference 0 1) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA421 + difference 1 0) (sourceB421 + difference 0 1) sourceC421) = raw7811 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7811; decide +kernel
    rw [ha]
    exact (canonical7811 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA421 + difference 1 2) (sourceB421 + difference 2 1) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA421 + difference 1 2) (sourceB421 + difference 2 1) sourceC421) = raw7812 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7812; decide +kernel
    rw [ha]
    exact (canonical7812 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA421 + difference 1 3) (sourceB421 + difference 3 1) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA421 + difference 1 3) (sourceB421 + difference 3 1) sourceC421) = raw7813 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7813; decide +kernel
    rw [ha]
    exact (canonical7813 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA421 + difference 1 4) (sourceB421 + difference 4 1) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA421 + difference 1 4) (sourceB421 + difference 4 1) sourceC421) = raw7814 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7814; decide +kernel
    rw [ha]
    exact (canonical7814 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA421 + difference 1 5) (sourceB421 + difference 5 1) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA421 + difference 1 5) (sourceB421 + difference 5 1) sourceC421) = raw7815 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7815; decide +kernel
    rw [ha]
    exact (canonical7815 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA421 + difference 2 0) (sourceB421 + difference 0 2) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA421 + difference 2 0) (sourceB421 + difference 0 2) sourceC421) = raw7816 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7816; decide +kernel
    rw [ha]
    exact (canonical7816 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA421 + difference 2 1) (sourceB421 + difference 1 2) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA421 + difference 2 1) (sourceB421 + difference 1 2) sourceC421) = raw7817 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7817; decide +kernel
    rw [ha]
    exact (canonical7817 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA421 + difference 2 3) (sourceB421 + difference 3 2) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA421 + difference 2 3) (sourceB421 + difference 3 2) sourceC421) = raw7818 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7818; decide +kernel
    rw [ha]
    exact (canonical7818 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA421 + difference 2 4) (sourceB421 + difference 4 2) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA421 + difference 2 4) (sourceB421 + difference 4 2) sourceC421) = raw7819 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7819; decide +kernel
    rw [ha]
    exact (canonical7819 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA421 + difference 2 5) (sourceB421 + difference 5 2) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA421 + difference 2 5) (sourceB421 + difference 5 2) sourceC421) = raw7820 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7820; decide +kernel
    rw [ha]
    exact (canonical7820 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA421 + difference 3 0) (sourceB421 + difference 0 3) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA421 + difference 3 0) (sourceB421 + difference 0 3) sourceC421) = raw7821 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7821; decide +kernel
    rw [ha]
    exact (canonical7821 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA421 + difference 3 1) (sourceB421 + difference 1 3) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA421 + difference 3 1) (sourceB421 + difference 1 3) sourceC421) = raw7822 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7822; decide +kernel
    rw [ha]
    exact (canonical7822 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA421 + difference 3 2) (sourceB421 + difference 2 3) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA421 + difference 3 2) (sourceB421 + difference 2 3) sourceC421) = raw7823 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7823; decide +kernel
    rw [ha]
    exact (canonical7823 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA421 + difference 3 4) (sourceB421 + difference 4 3) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA421 + difference 3 4) (sourceB421 + difference 4 3) sourceC421) = raw7824 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7824; decide +kernel
    rw [ha]
    exact (canonical7824 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA421 + difference 3 5) (sourceB421 + difference 5 3) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA421 + difference 3 5) (sourceB421 + difference 5 3) sourceC421) = raw7825 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7825; decide +kernel
    rw [ha]
    exact (canonical7825 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA421 + difference 4 0) (sourceB421 + difference 0 4) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA421 + difference 4 0) (sourceB421 + difference 0 4) sourceC421) = raw7826 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7826; decide +kernel
    rw [ha]
    exact (canonical7826 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA421 + difference 4 1) (sourceB421 + difference 1 4) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA421 + difference 4 1) (sourceB421 + difference 1 4) sourceC421) = raw7827 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7827; decide +kernel
    rw [ha]
    exact (canonical7827 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA421 + difference 4 2) (sourceB421 + difference 2 4) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA421 + difference 4 2) (sourceB421 + difference 2 4) sourceC421) = raw7828 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7828; decide +kernel
    rw [ha]
    exact (canonical7828 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA421 + difference 4 3) (sourceB421 + difference 3 4) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA421 + difference 4 3) (sourceB421 + difference 3 4) sourceC421) = raw7829 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7829; decide +kernel
    rw [ha]
    exact (canonical7829 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA421 + difference 4 5) (sourceB421 + difference 5 4) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA421 + difference 4 5) (sourceB421 + difference 5 4) sourceC421) = raw7830 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7830; decide +kernel
    rw [ha]
    exact (canonical7830 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA421 + difference 5 0) (sourceB421 + difference 0 5) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA421 + difference 5 0) (sourceB421 + difference 0 5) sourceC421) = raw7831 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7831; decide +kernel
    rw [ha]
    exact (canonical7831 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA421 + difference 5 1) (sourceB421 + difference 1 5) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA421 + difference 5 1) (sourceB421 + difference 1 5) sourceC421) = raw7832 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7832; decide +kernel
    rw [ha]
    exact (canonical7832 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA421 + difference 5 2) (sourceB421 + difference 2 5) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA421 + difference 5 2) (sourceB421 + difference 2 5) sourceC421) = raw7833 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7833; decide +kernel
    rw [ha]
    exact (canonical7833 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA421 + difference 5 3) (sourceB421 + difference 3 5) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA421 + difference 5 3) (sourceB421 + difference 3 5) sourceC421) = raw7834 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7834; decide +kernel
    rw [ha]
    exact (canonical7834 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA421 + difference 5 4) (sourceB421 + difference 4 5) sourceC421) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA421 + difference 5 4) (sourceB421 + difference 4 5) sourceC421) = raw7835 := by
      apply Matrix.ext; unfold tripleCharges sourceA421 sourceB421 sourceC421 difference raw7835; decide +kernel
    rw [ha]
    exact (canonical7835 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA421 sourceB421 sourceC421
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm421, Integer.Sparse.eval]
  linarith only [hs]

def sourceA422 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB422 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC422 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceForm422 : Integer.Sparse Master := [(Sum.inr 1240, 2), (Sum.inr 1242, 1), (Sum.inr 1246, 1), (Sum.inr 1301, 1), (Sum.inr 2485, 2), (Sum.inr 2519, 1), (Sum.inr 2770, 1), (Sum.inr 2884, 2), (Sum.inr 2889, 1), (Sum.inr 2927, 2), (Sum.inr 2931, 2), (Sum.inr 2960, 2), (Sum.inr 3100, 2), (Sum.inr 3101, 1), (Sum.inr 3102, 2), (Sum.inr 3122, 1), (Sum.inr 3123, 1), (Sum.inr 3982, 2), (Sum.inr 3987, 1), (Sum.inr 4019, 1), (Sum.inr 4040, 1)]

theorem sourceEq422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm422 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA422 + difference 0 1) (sourceB422 + difference 1 0) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA422 + difference 0 1) (sourceB422 + difference 1 0) sourceC422) = raw7836 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7836; decide +kernel
    rw [ha]
    exact (canonical7836 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA422 + difference 0 2) (sourceB422 + difference 2 0) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA422 + difference 0 2) (sourceB422 + difference 2 0) sourceC422) = raw7837 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7837; decide +kernel
    rw [ha]
    exact (canonical7837 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA422 + difference 0 3) (sourceB422 + difference 3 0) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA422 + difference 0 3) (sourceB422 + difference 3 0) sourceC422) = raw7838 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7838; decide +kernel
    rw [ha]
    exact (canonical7838 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA422 + difference 0 4) (sourceB422 + difference 4 0) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4019) := by
    have ha : (tripleCharges (sourceA422 + difference 0 4) (sourceB422 + difference 4 0) sourceC422) = raw7839 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7839; decide +kernel
    rw [ha]
    exact (canonical7839 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA422 + difference 0 5) (sourceB422 + difference 5 0) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4040) := by
    have ha : (tripleCharges (sourceA422 + difference 0 5) (sourceB422 + difference 5 0) sourceC422) = raw7840 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7840; decide +kernel
    rw [ha]
    exact (canonical7840 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA422 + difference 1 0) (sourceB422 + difference 0 1) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA422 + difference 1 0) (sourceB422 + difference 0 1) sourceC422) = raw7841 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7841; decide +kernel
    rw [ha]
    exact (canonical7841 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA422 + difference 1 2) (sourceB422 + difference 2 1) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2927) := by
    have ha : (tripleCharges (sourceA422 + difference 1 2) (sourceB422 + difference 2 1) sourceC422) = raw7842 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7842; decide +kernel
    rw [ha]
    exact (canonical7842 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA422 + difference 1 3) (sourceB422 + difference 3 1) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA422 + difference 1 3) (sourceB422 + difference 3 1) sourceC422) = raw7843 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7843; decide +kernel
    rw [ha]
    exact (canonical7843 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA422 + difference 1 4) (sourceB422 + difference 4 1) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA422 + difference 1 4) (sourceB422 + difference 4 1) sourceC422) = raw7844 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7844; decide +kernel
    rw [ha]
    exact (canonical7844 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA422 + difference 1 5) (sourceB422 + difference 5 1) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA422 + difference 1 5) (sourceB422 + difference 5 1) sourceC422) = raw7845 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7845; decide +kernel
    rw [ha]
    exact (canonical7845 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA422 + difference 2 0) (sourceB422 + difference 0 2) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA422 + difference 2 0) (sourceB422 + difference 0 2) sourceC422) = raw7846 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7846; decide +kernel
    rw [ha]
    exact (canonical7846 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA422 + difference 2 1) (sourceB422 + difference 1 2) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2927) := by
    have ha : (tripleCharges (sourceA422 + difference 2 1) (sourceB422 + difference 1 2) sourceC422) = raw7847 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7847; decide +kernel
    rw [ha]
    exact (canonical7847 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA422 + difference 2 3) (sourceB422 + difference 3 2) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA422 + difference 2 3) (sourceB422 + difference 3 2) sourceC422) = raw7848 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7848; decide +kernel
    rw [ha]
    exact (canonical7848 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA422 + difference 2 4) (sourceB422 + difference 4 2) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA422 + difference 2 4) (sourceB422 + difference 4 2) sourceC422) = raw7849 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7849; decide +kernel
    rw [ha]
    exact (canonical7849 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA422 + difference 2 5) (sourceB422 + difference 5 2) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA422 + difference 2 5) (sourceB422 + difference 5 2) sourceC422) = raw7850 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7850; decide +kernel
    rw [ha]
    exact (canonical7850 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA422 + difference 3 0) (sourceB422 + difference 0 3) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA422 + difference 3 0) (sourceB422 + difference 0 3) sourceC422) = raw7851 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7851; decide +kernel
    rw [ha]
    exact (canonical7851 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA422 + difference 3 1) (sourceB422 + difference 1 3) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA422 + difference 3 1) (sourceB422 + difference 1 3) sourceC422) = raw7852 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7852; decide +kernel
    rw [ha]
    exact (canonical7852 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA422 + difference 3 2) (sourceB422 + difference 2 3) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA422 + difference 3 2) (sourceB422 + difference 2 3) sourceC422) = raw7853 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7853; decide +kernel
    rw [ha]
    exact (canonical7853 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA422 + difference 3 4) (sourceB422 + difference 4 3) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3123) := by
    have ha : (tripleCharges (sourceA422 + difference 3 4) (sourceB422 + difference 4 3) sourceC422) = raw7854 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7854; decide +kernel
    rw [ha]
    exact (canonical7854 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA422 + difference 3 5) (sourceB422 + difference 5 3) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3122) := by
    have ha : (tripleCharges (sourceA422 + difference 3 5) (sourceB422 + difference 5 3) sourceC422) = raw7855 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7855; decide +kernel
    rw [ha]
    exact (canonical7855 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA422 + difference 4 0) (sourceB422 + difference 0 4) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA422 + difference 4 0) (sourceB422 + difference 0 4) sourceC422) = raw7856 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7856; decide +kernel
    rw [ha]
    exact (canonical7856 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA422 + difference 4 1) (sourceB422 + difference 1 4) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA422 + difference 4 1) (sourceB422 + difference 1 4) sourceC422) = raw7857 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7857; decide +kernel
    rw [ha]
    exact (canonical7857 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA422 + difference 4 2) (sourceB422 + difference 2 4) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA422 + difference 4 2) (sourceB422 + difference 2 4) sourceC422) = raw7858 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7858; decide +kernel
    rw [ha]
    exact (canonical7858 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA422 + difference 4 3) (sourceB422 + difference 3 4) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA422 + difference 4 3) (sourceB422 + difference 3 4) sourceC422) = raw7859 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7859; decide +kernel
    rw [ha]
    exact (canonical7859 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA422 + difference 4 5) (sourceB422 + difference 5 4) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA422 + difference 4 5) (sourceB422 + difference 5 4) sourceC422) = raw7860 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7860; decide +kernel
    rw [ha]
    exact (canonical7860 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA422 + difference 5 0) (sourceB422 + difference 0 5) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA422 + difference 5 0) (sourceB422 + difference 0 5) sourceC422) = raw7861 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7861; decide +kernel
    rw [ha]
    exact (canonical7861 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA422 + difference 5 1) (sourceB422 + difference 1 5) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA422 + difference 5 1) (sourceB422 + difference 1 5) sourceC422) = raw7862 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7862; decide +kernel
    rw [ha]
    exact (canonical7862 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA422 + difference 5 2) (sourceB422 + difference 2 5) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA422 + difference 5 2) (sourceB422 + difference 2 5) sourceC422) = raw7863 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7863; decide +kernel
    rw [ha]
    exact (canonical7863 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA422 + difference 5 3) (sourceB422 + difference 3 5) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA422 + difference 5 3) (sourceB422 + difference 3 5) sourceC422) = raw7864 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7864; decide +kernel
    rw [ha]
    exact (canonical7864 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA422 + difference 5 4) (sourceB422 + difference 4 5) sourceC422) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA422 + difference 5 4) (sourceB422 + difference 4 5) sourceC422) = raw7865 := by
      apply Matrix.ext; unfold tripleCharges sourceA422 sourceB422 sourceC422 difference raw7865; decide +kernel
    rw [ha]
    exact (canonical7865 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA422 sourceB422 sourceC422
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm422, Integer.Sparse.eval]
  linarith only [hs]

def sourceA423 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB423 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC423 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceForm423 : Integer.Sparse Master := [(Sum.inr 4458, 2), (Sum.inr 4460, 1), (Sum.inr 4467, 1), (Sum.inr 4499, 1), (Sum.inr 5073, 2), (Sum.inr 5075, 2), (Sum.inr 5081, 2), (Sum.inr 5102, 2), (Sum.inr 5169, 2), (Sum.inr 5171, 1), (Sum.inr 5177, 1), (Sum.inr 5259, 2), (Sum.inr 5261, 1), (Sum.inr 5275, 1), (Sum.inr 5292, 2), (Sum.inr 5293, 1), (Sum.inr 5306, 1), (Sum.inr 5483, 2), (Sum.inr 5487, 1), (Sum.inr 5491, 1), (Sum.inr 5493, 1)]

theorem sourceEq423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm423 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA423 + difference 0 1) (sourceB423 + difference 1 0) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA423 + difference 0 1) (sourceB423 + difference 1 0) sourceC423) = raw3257 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw3257; decide +kernel
    rw [ha]
    exact (canonical3257 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA423 + difference 0 2) (sourceB423 + difference 2 0) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA423 + difference 0 2) (sourceB423 + difference 2 0) sourceC423) = raw3258 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw3258; decide +kernel
    rw [ha]
    exact (canonical3258 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA423 + difference 0 3) (sourceB423 + difference 3 0) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA423 + difference 0 3) (sourceB423 + difference 3 0) sourceC423) = raw3259 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw3259; decide +kernel
    rw [ha]
    exact (canonical3259 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA423 + difference 0 4) (sourceB423 + difference 4 0) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA423 + difference 0 4) (sourceB423 + difference 4 0) sourceC423) = raw3260 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw3260; decide +kernel
    rw [ha]
    exact (canonical3260 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA423 + difference 0 5) (sourceB423 + difference 5 0) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA423 + difference 0 5) (sourceB423 + difference 5 0) sourceC423) = raw7866 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7866; decide +kernel
    rw [ha]
    exact (canonical7866 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA423 + difference 1 0) (sourceB423 + difference 0 1) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA423 + difference 1 0) (sourceB423 + difference 0 1) sourceC423) = raw7867 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7867; decide +kernel
    rw [ha]
    exact (canonical7867 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA423 + difference 1 2) (sourceB423 + difference 2 1) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA423 + difference 1 2) (sourceB423 + difference 2 1) sourceC423) = raw7868 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7868; decide +kernel
    rw [ha]
    exact (canonical7868 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA423 + difference 1 3) (sourceB423 + difference 3 1) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA423 + difference 1 3) (sourceB423 + difference 3 1) sourceC423) = raw7869 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7869; decide +kernel
    rw [ha]
    exact (canonical7869 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA423 + difference 1 4) (sourceB423 + difference 4 1) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA423 + difference 1 4) (sourceB423 + difference 4 1) sourceC423) = raw7870 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7870; decide +kernel
    rw [ha]
    exact (canonical7870 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA423 + difference 1 5) (sourceB423 + difference 5 1) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA423 + difference 1 5) (sourceB423 + difference 5 1) sourceC423) = raw3236 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw3236; decide +kernel
    rw [ha]
    exact (canonical3236 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA423 + difference 2 0) (sourceB423 + difference 0 2) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA423 + difference 2 0) (sourceB423 + difference 0 2) sourceC423) = raw7871 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7871; decide +kernel
    rw [ha]
    exact (canonical7871 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA423 + difference 2 1) (sourceB423 + difference 1 2) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA423 + difference 2 1) (sourceB423 + difference 1 2) sourceC423) = raw7872 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7872; decide +kernel
    rw [ha]
    exact (canonical7872 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA423 + difference 2 3) (sourceB423 + difference 3 2) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA423 + difference 2 3) (sourceB423 + difference 3 2) sourceC423) = raw7873 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7873; decide +kernel
    rw [ha]
    exact (canonical7873 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA423 + difference 2 4) (sourceB423 + difference 4 2) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA423 + difference 2 4) (sourceB423 + difference 4 2) sourceC423) = raw7874 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7874; decide +kernel
    rw [ha]
    exact (canonical7874 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA423 + difference 2 5) (sourceB423 + difference 5 2) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA423 + difference 2 5) (sourceB423 + difference 5 2) sourceC423) = raw3241 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw3241; decide +kernel
    rw [ha]
    exact (canonical3241 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA423 + difference 3 0) (sourceB423 + difference 0 3) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA423 + difference 3 0) (sourceB423 + difference 0 3) sourceC423) = raw7875 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7875; decide +kernel
    rw [ha]
    exact (canonical7875 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA423 + difference 3 1) (sourceB423 + difference 1 3) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA423 + difference 3 1) (sourceB423 + difference 1 3) sourceC423) = raw7876 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7876; decide +kernel
    rw [ha]
    exact (canonical7876 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA423 + difference 3 2) (sourceB423 + difference 2 3) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA423 + difference 3 2) (sourceB423 + difference 2 3) sourceC423) = raw7877 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7877; decide +kernel
    rw [ha]
    exact (canonical7877 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA423 + difference 3 4) (sourceB423 + difference 4 3) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA423 + difference 3 4) (sourceB423 + difference 4 3) sourceC423) = raw7878 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7878; decide +kernel
    rw [ha]
    exact (canonical7878 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA423 + difference 3 5) (sourceB423 + difference 5 3) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA423 + difference 3 5) (sourceB423 + difference 5 3) sourceC423) = raw3246 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw3246; decide +kernel
    rw [ha]
    exact (canonical3246 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA423 + difference 4 0) (sourceB423 + difference 0 4) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA423 + difference 4 0) (sourceB423 + difference 0 4) sourceC423) = raw7879 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7879; decide +kernel
    rw [ha]
    exact (canonical7879 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA423 + difference 4 1) (sourceB423 + difference 1 4) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA423 + difference 4 1) (sourceB423 + difference 1 4) sourceC423) = raw7880 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7880; decide +kernel
    rw [ha]
    exact (canonical7880 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA423 + difference 4 2) (sourceB423 + difference 2 4) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA423 + difference 4 2) (sourceB423 + difference 2 4) sourceC423) = raw7881 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7881; decide +kernel
    rw [ha]
    exact (canonical7881 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA423 + difference 4 3) (sourceB423 + difference 3 4) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA423 + difference 4 3) (sourceB423 + difference 3 4) sourceC423) = raw7882 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7882; decide +kernel
    rw [ha]
    exact (canonical7882 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA423 + difference 4 5) (sourceB423 + difference 5 4) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA423 + difference 4 5) (sourceB423 + difference 5 4) sourceC423) = raw3251 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw3251; decide +kernel
    rw [ha]
    exact (canonical3251 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA423 + difference 5 0) (sourceB423 + difference 0 5) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA423 + difference 5 0) (sourceB423 + difference 0 5) sourceC423) = raw7883 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7883; decide +kernel
    rw [ha]
    exact (canonical7883 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA423 + difference 5 1) (sourceB423 + difference 1 5) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA423 + difference 5 1) (sourceB423 + difference 1 5) sourceC423) = raw7884 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7884; decide +kernel
    rw [ha]
    exact (canonical7884 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA423 + difference 5 2) (sourceB423 + difference 2 5) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA423 + difference 5 2) (sourceB423 + difference 2 5) sourceC423) = raw7885 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7885; decide +kernel
    rw [ha]
    exact (canonical7885 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA423 + difference 5 3) (sourceB423 + difference 3 5) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA423 + difference 5 3) (sourceB423 + difference 3 5) sourceC423) = raw7886 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7886; decide +kernel
    rw [ha]
    exact (canonical7886 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA423 + difference 5 4) (sourceB423 + difference 4 5) sourceC423) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA423 + difference 5 4) (sourceB423 + difference 4 5) sourceC423) = raw7887 := by
      apply Matrix.ext; unfold tripleCharges sourceA423 sourceB423 sourceC423 difference raw7887; decide +kernel
    rw [ha]
    exact (canonical7887 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA423 sourceB423 sourceC423
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm423, Integer.Sparse.eval]
  linarith only [hs]

def sourceA424 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB424 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC424 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceForm424 : Integer.Sparse Master := [(Sum.inr 1041, 2), (Sum.inr 1043, 1), (Sum.inr 1050, 1), (Sum.inr 1083, 1), (Sum.inr 2480, 2), (Sum.inr 2482, 2), (Sum.inr 2489, 2), (Sum.inr 2512, 2), (Sum.inr 2595, 2), (Sum.inr 2598, 1), (Sum.inr 2605, 1), (Sum.inr 2723, 2), (Sum.inr 2726, 1), (Sum.inr 2743, 1), (Sum.inr 2766, 2), (Sum.inr 2767, 1), (Sum.inr 2784, 1), (Sum.inr 3981, 2), (Sum.inr 4000, 1), (Sum.inr 4014, 1), (Sum.inr 4018, 1)]

theorem sourceEq424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm424 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA424 + difference 0 1) (sourceB424 + difference 1 0) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA424 + difference 0 1) (sourceB424 + difference 1 0) sourceC424) = raw7888 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7888; decide +kernel
    rw [ha]
    exact (canonical7888 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA424 + difference 0 2) (sourceB424 + difference 2 0) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA424 + difference 0 2) (sourceB424 + difference 2 0) sourceC424) = raw7889 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7889; decide +kernel
    rw [ha]
    exact (canonical7889 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA424 + difference 0 3) (sourceB424 + difference 3 0) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4000) := by
    have ha : (tripleCharges (sourceA424 + difference 0 3) (sourceB424 + difference 3 0) sourceC424) = raw7890 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7890; decide +kernel
    rw [ha]
    exact (canonical7890 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA424 + difference 0 4) (sourceB424 + difference 4 0) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4014) := by
    have ha : (tripleCharges (sourceA424 + difference 0 4) (sourceB424 + difference 4 0) sourceC424) = raw7891 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7891; decide +kernel
    rw [ha]
    exact (canonical7891 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA424 + difference 0 5) (sourceB424 + difference 5 0) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4018) := by
    have ha : (tripleCharges (sourceA424 + difference 0 5) (sourceB424 + difference 5 0) sourceC424) = raw7892 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7892; decide +kernel
    rw [ha]
    exact (canonical7892 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA424 + difference 1 0) (sourceB424 + difference 0 1) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA424 + difference 1 0) (sourceB424 + difference 0 1) sourceC424) = raw7893 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7893; decide +kernel
    rw [ha]
    exact (canonical7893 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA424 + difference 1 2) (sourceB424 + difference 2 1) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA424 + difference 1 2) (sourceB424 + difference 2 1) sourceC424) = raw7894 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7894; decide +kernel
    rw [ha]
    exact (canonical7894 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA424 + difference 1 3) (sourceB424 + difference 3 1) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA424 + difference 1 3) (sourceB424 + difference 3 1) sourceC424) = raw7895 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7895; decide +kernel
    rw [ha]
    exact (canonical7895 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA424 + difference 1 4) (sourceB424 + difference 4 1) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA424 + difference 1 4) (sourceB424 + difference 4 1) sourceC424) = raw7896 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7896; decide +kernel
    rw [ha]
    exact (canonical7896 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA424 + difference 1 5) (sourceB424 + difference 5 1) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA424 + difference 1 5) (sourceB424 + difference 5 1) sourceC424) = raw7897 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7897; decide +kernel
    rw [ha]
    exact (canonical7897 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA424 + difference 2 0) (sourceB424 + difference 0 2) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA424 + difference 2 0) (sourceB424 + difference 0 2) sourceC424) = raw7898 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7898; decide +kernel
    rw [ha]
    exact (canonical7898 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA424 + difference 2 1) (sourceB424 + difference 1 2) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA424 + difference 2 1) (sourceB424 + difference 1 2) sourceC424) = raw7899 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7899; decide +kernel
    rw [ha]
    exact (canonical7899 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA424 + difference 2 3) (sourceB424 + difference 3 2) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA424 + difference 2 3) (sourceB424 + difference 3 2) sourceC424) = raw7900 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7900; decide +kernel
    rw [ha]
    exact (canonical7900 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA424 + difference 2 4) (sourceB424 + difference 4 2) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA424 + difference 2 4) (sourceB424 + difference 4 2) sourceC424) = raw7901 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7901; decide +kernel
    rw [ha]
    exact (canonical7901 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA424 + difference 2 5) (sourceB424 + difference 5 2) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA424 + difference 2 5) (sourceB424 + difference 5 2) sourceC424) = raw7902 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7902; decide +kernel
    rw [ha]
    exact (canonical7902 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA424 + difference 3 0) (sourceB424 + difference 0 3) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA424 + difference 3 0) (sourceB424 + difference 0 3) sourceC424) = raw7903 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7903; decide +kernel
    rw [ha]
    exact (canonical7903 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA424 + difference 3 1) (sourceB424 + difference 1 3) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA424 + difference 3 1) (sourceB424 + difference 1 3) sourceC424) = raw7904 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7904; decide +kernel
    rw [ha]
    exact (canonical7904 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA424 + difference 3 2) (sourceB424 + difference 2 3) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA424 + difference 3 2) (sourceB424 + difference 2 3) sourceC424) = raw7905 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7905; decide +kernel
    rw [ha]
    exact (canonical7905 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA424 + difference 3 4) (sourceB424 + difference 4 3) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA424 + difference 3 4) (sourceB424 + difference 4 3) sourceC424) = raw7906 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7906; decide +kernel
    rw [ha]
    exact (canonical7906 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA424 + difference 3 5) (sourceB424 + difference 5 3) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA424 + difference 3 5) (sourceB424 + difference 5 3) sourceC424) = raw7907 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7907; decide +kernel
    rw [ha]
    exact (canonical7907 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA424 + difference 4 0) (sourceB424 + difference 0 4) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA424 + difference 4 0) (sourceB424 + difference 0 4) sourceC424) = raw7908 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7908; decide +kernel
    rw [ha]
    exact (canonical7908 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA424 + difference 4 1) (sourceB424 + difference 1 4) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA424 + difference 4 1) (sourceB424 + difference 1 4) sourceC424) = raw7909 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7909; decide +kernel
    rw [ha]
    exact (canonical7909 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA424 + difference 4 2) (sourceB424 + difference 2 4) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA424 + difference 4 2) (sourceB424 + difference 2 4) sourceC424) = raw7910 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7910; decide +kernel
    rw [ha]
    exact (canonical7910 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA424 + difference 4 3) (sourceB424 + difference 3 4) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2605) := by
    have ha : (tripleCharges (sourceA424 + difference 4 3) (sourceB424 + difference 3 4) sourceC424) = raw7911 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7911; decide +kernel
    rw [ha]
    exact (canonical7911 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA424 + difference 4 5) (sourceB424 + difference 5 4) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA424 + difference 4 5) (sourceB424 + difference 5 4) sourceC424) = raw7912 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7912; decide +kernel
    rw [ha]
    exact (canonical7912 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA424 + difference 5 0) (sourceB424 + difference 0 5) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA424 + difference 5 0) (sourceB424 + difference 0 5) sourceC424) = raw7913 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7913; decide +kernel
    rw [ha]
    exact (canonical7913 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA424 + difference 5 1) (sourceB424 + difference 1 5) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA424 + difference 5 1) (sourceB424 + difference 1 5) sourceC424) = raw7914 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7914; decide +kernel
    rw [ha]
    exact (canonical7914 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA424 + difference 5 2) (sourceB424 + difference 2 5) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA424 + difference 5 2) (sourceB424 + difference 2 5) sourceC424) = raw7915 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7915; decide +kernel
    rw [ha]
    exact (canonical7915 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA424 + difference 5 3) (sourceB424 + difference 3 5) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2598) := by
    have ha : (tripleCharges (sourceA424 + difference 5 3) (sourceB424 + difference 3 5) sourceC424) = raw7916 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7916; decide +kernel
    rw [ha]
    exact (canonical7916 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA424 + difference 5 4) (sourceB424 + difference 4 5) sourceC424) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA424 + difference 5 4) (sourceB424 + difference 4 5) sourceC424) = raw7917 := by
      apply Matrix.ext; unfold tripleCharges sourceA424 sourceB424 sourceC424 difference raw7917; decide +kernel
    rw [ha]
    exact (canonical7917 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA424 sourceB424 sourceC424
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm424, Integer.Sparse.eval]
  linarith only [hs]

def sourceA425 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB425 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC425 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm425 : Integer.Sparse Master := [(Sum.inr 4888, 2), (Sum.inr 4894, 1), (Sum.inr 4895, 1), (Sum.inr 4896, 1), (Sum.inr 5250, 2), (Sum.inr 5258, 2), (Sum.inr 5259, 4), (Sum.inr 5266, 2), (Sum.inr 5274, 1), (Sum.inr 5275, 1), (Sum.inr 5282, 2), (Sum.inr 5284, 2), (Sum.inr 5291, 1), (Sum.inr 5293, 2), (Sum.inr 5294, 1), (Sum.inr 5300, 1), (Sum.inr 5302, 1), (Sum.inr 5308, 1), (Sum.inr 5309, 2)]

theorem sourceEq425 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm425 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA425 + difference 0 1) (sourceB425 + difference 1 0) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA425 + difference 0 1) (sourceB425 + difference 1 0) sourceC425) = raw6702 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw6702; decide +kernel
    rw [ha]
    exact (canonical6702 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA425 + difference 0 2) (sourceB425 + difference 2 0) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA425 + difference 0 2) (sourceB425 + difference 2 0) sourceC425) = raw7918 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7918; decide +kernel
    rw [ha]
    exact (canonical7918 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA425 + difference 0 3) (sourceB425 + difference 3 0) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA425 + difference 0 3) (sourceB425 + difference 3 0) sourceC425) = raw7919 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7919; decide +kernel
    rw [ha]
    exact (canonical7919 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA425 + difference 0 4) (sourceB425 + difference 4 0) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA425 + difference 0 4) (sourceB425 + difference 4 0) sourceC425) = raw7920 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7920; decide +kernel
    rw [ha]
    exact (canonical7920 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA425 + difference 0 5) (sourceB425 + difference 5 0) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA425 + difference 0 5) (sourceB425 + difference 5 0) sourceC425) = raw7921 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7921; decide +kernel
    rw [ha]
    exact (canonical7921 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA425 + difference 1 0) (sourceB425 + difference 0 1) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA425 + difference 1 0) (sourceB425 + difference 0 1) sourceC425) = raw5685 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw5685; decide +kernel
    rw [ha]
    exact (canonical5685 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA425 + difference 1 2) (sourceB425 + difference 2 1) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA425 + difference 1 2) (sourceB425 + difference 2 1) sourceC425) = raw7922 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7922; decide +kernel
    rw [ha]
    exact (canonical7922 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA425 + difference 1 3) (sourceB425 + difference 3 1) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA425 + difference 1 3) (sourceB425 + difference 3 1) sourceC425) = raw7923 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7923; decide +kernel
    rw [ha]
    exact (canonical7923 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA425 + difference 1 4) (sourceB425 + difference 4 1) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA425 + difference 1 4) (sourceB425 + difference 4 1) sourceC425) = raw7924 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7924; decide +kernel
    rw [ha]
    exact (canonical7924 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA425 + difference 1 5) (sourceB425 + difference 5 1) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA425 + difference 1 5) (sourceB425 + difference 5 1) sourceC425) = raw5659 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw5659; decide +kernel
    rw [ha]
    exact (canonical5659 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA425 + difference 2 0) (sourceB425 + difference 0 2) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA425 + difference 2 0) (sourceB425 + difference 0 2) sourceC425) = raw5684 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw5684; decide +kernel
    rw [ha]
    exact (canonical5684 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA425 + difference 2 1) (sourceB425 + difference 1 2) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA425 + difference 2 1) (sourceB425 + difference 1 2) sourceC425) = raw6712 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw6712; decide +kernel
    rw [ha]
    exact (canonical6712 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA425 + difference 2 3) (sourceB425 + difference 3 2) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA425 + difference 2 3) (sourceB425 + difference 3 2) sourceC425) = raw7225 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7225; decide +kernel
    rw [ha]
    exact (canonical7225 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA425 + difference 2 4) (sourceB425 + difference 4 2) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA425 + difference 2 4) (sourceB425 + difference 4 2) sourceC425) = raw7226 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7226; decide +kernel
    rw [ha]
    exact (canonical7226 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA425 + difference 2 5) (sourceB425 + difference 5 2) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA425 + difference 2 5) (sourceB425 + difference 5 2) sourceC425) = raw5658 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw5658; decide +kernel
    rw [ha]
    exact (canonical5658 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA425 + difference 3 0) (sourceB425 + difference 0 3) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA425 + difference 3 0) (sourceB425 + difference 0 3) sourceC425) = raw6705 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw6705; decide +kernel
    rw [ha]
    exact (canonical6705 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA425 + difference 3 1) (sourceB425 + difference 1 3) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA425 + difference 3 1) (sourceB425 + difference 1 3) sourceC425) = raw7063 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7063; decide +kernel
    rw [ha]
    exact (canonical7063 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA425 + difference 3 2) (sourceB425 + difference 2 3) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA425 + difference 3 2) (sourceB425 + difference 2 3) sourceC425) = raw6706 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw6706; decide +kernel
    rw [ha]
    exact (canonical6706 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA425 + difference 3 4) (sourceB425 + difference 4 3) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA425 + difference 3 4) (sourceB425 + difference 4 3) sourceC425) = raw6708 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw6708; decide +kernel
    rw [ha]
    exact (canonical6708 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA425 + difference 3 5) (sourceB425 + difference 5 3) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA425 + difference 3 5) (sourceB425 + difference 5 3) sourceC425) = raw6709 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw6709; decide +kernel
    rw [ha]
    exact (canonical6709 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA425 + difference 4 0) (sourceB425 + difference 0 4) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA425 + difference 4 0) (sourceB425 + difference 0 4) sourceC425) = raw7925 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7925; decide +kernel
    rw [ha]
    exact (canonical7925 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA425 + difference 4 1) (sourceB425 + difference 1 4) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA425 + difference 4 1) (sourceB425 + difference 1 4) sourceC425) = raw6390 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw6390; decide +kernel
    rw [ha]
    exact (canonical6390 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA425 + difference 4 2) (sourceB425 + difference 2 4) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA425 + difference 4 2) (sourceB425 + difference 2 4) sourceC425) = raw7926 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7926; decide +kernel
    rw [ha]
    exact (canonical7926 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA425 + difference 4 3) (sourceB425 + difference 3 4) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA425 + difference 4 3) (sourceB425 + difference 3 4) sourceC425) = raw7659 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7659; decide +kernel
    rw [ha]
    exact (canonical7659 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA425 + difference 4 5) (sourceB425 + difference 5 4) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA425 + difference 4 5) (sourceB425 + difference 5 4) sourceC425) = raw6375 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw6375; decide +kernel
    rw [ha]
    exact (canonical6375 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA425 + difference 5 0) (sourceB425 + difference 0 5) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA425 + difference 5 0) (sourceB425 + difference 0 5) sourceC425) = raw7927 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7927; decide +kernel
    rw [ha]
    exact (canonical7927 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA425 + difference 5 1) (sourceB425 + difference 1 5) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA425 + difference 5 1) (sourceB425 + difference 1 5) sourceC425) = raw6726 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw6726; decide +kernel
    rw [ha]
    exact (canonical6726 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA425 + difference 5 2) (sourceB425 + difference 2 5) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA425 + difference 5 2) (sourceB425 + difference 2 5) sourceC425) = raw7928 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7928; decide +kernel
    rw [ha]
    exact (canonical7928 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA425 + difference 5 3) (sourceB425 + difference 3 5) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA425 + difference 5 3) (sourceB425 + difference 3 5) sourceC425) = raw7929 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7929; decide +kernel
    rw [ha]
    exact (canonical7929 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA425 + difference 5 4) (sourceB425 + difference 4 5) sourceC425) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA425 + difference 5 4) (sourceB425 + difference 4 5) sourceC425) = raw7930 := by
      apply Matrix.ext; unfold tripleCharges sourceA425 sourceB425 sourceC425 difference raw7930; decide +kernel
    rw [ha]
    exact (canonical7930 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA425 sourceB425 sourceC425
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm425, Integer.Sparse.eval]
  linarith only [hs]

def sourceA426 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB426 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC426 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm426 : Integer.Sparse Master := [(Sum.inr 2244, 2), (Sum.inr 2264, 1), (Sum.inr 2265, 1), (Sum.inr 2278, 1), (Sum.inr 2709, 2), (Sum.inr 2722, 2), (Sum.inr 2723, 2), (Sum.inr 2731, 2), (Sum.inr 2751, 2), (Sum.inr 2753, 2), (Sum.inr 2765, 1), (Sum.inr 2767, 2), (Sum.inr 2768, 1), (Sum.inr 2774, 1), (Sum.inr 2776, 1), (Sum.inr 2786, 1), (Sum.inr 2787, 1), (Sum.inr 3088, 2), (Sum.inr 3110, 1), (Sum.inr 3112, 1), (Sum.inr 3123, 1)]

theorem sourceEq426 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm426 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA426 + difference 0 1) (sourceB426 + difference 1 0) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA426 + difference 0 1) (sourceB426 + difference 1 0) sourceC426) = raw6730 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw6730; decide +kernel
    rw [ha]
    exact (canonical6730 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA426 + difference 0 2) (sourceB426 + difference 2 0) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA426 + difference 0 2) (sourceB426 + difference 2 0) sourceC426) = raw7931 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7931; decide +kernel
    rw [ha]
    exact (canonical7931 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA426 + difference 0 3) (sourceB426 + difference 3 0) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3123) := by
    have ha : (tripleCharges (sourceA426 + difference 0 3) (sourceB426 + difference 3 0) sourceC426) = raw7932 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7932; decide +kernel
    rw [ha]
    exact (canonical7932 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA426 + difference 0 4) (sourceB426 + difference 4 0) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA426 + difference 0 4) (sourceB426 + difference 4 0) sourceC426) = raw7933 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7933; decide +kernel
    rw [ha]
    exact (canonical7933 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA426 + difference 0 5) (sourceB426 + difference 5 0) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA426 + difference 0 5) (sourceB426 + difference 5 0) sourceC426) = raw7934 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7934; decide +kernel
    rw [ha]
    exact (canonical7934 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA426 + difference 1 0) (sourceB426 + difference 0 1) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA426 + difference 1 0) (sourceB426 + difference 0 1) sourceC426) = raw5715 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw5715; decide +kernel
    rw [ha]
    exact (canonical5715 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA426 + difference 1 2) (sourceB426 + difference 2 1) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA426 + difference 1 2) (sourceB426 + difference 2 1) sourceC426) = raw7935 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7935; decide +kernel
    rw [ha]
    exact (canonical7935 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA426 + difference 1 3) (sourceB426 + difference 3 1) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA426 + difference 1 3) (sourceB426 + difference 3 1) sourceC426) = raw7936 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7936; decide +kernel
    rw [ha]
    exact (canonical7936 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA426 + difference 1 4) (sourceB426 + difference 4 1) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA426 + difference 1 4) (sourceB426 + difference 4 1) sourceC426) = raw7937 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7937; decide +kernel
    rw [ha]
    exact (canonical7937 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA426 + difference 1 5) (sourceB426 + difference 5 1) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA426 + difference 1 5) (sourceB426 + difference 5 1) sourceC426) = raw5689 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw5689; decide +kernel
    rw [ha]
    exact (canonical5689 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA426 + difference 2 0) (sourceB426 + difference 0 2) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA426 + difference 2 0) (sourceB426 + difference 0 2) sourceC426) = raw5714 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw5714; decide +kernel
    rw [ha]
    exact (canonical5714 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA426 + difference 2 1) (sourceB426 + difference 1 2) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA426 + difference 2 1) (sourceB426 + difference 1 2) sourceC426) = raw6740 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw6740; decide +kernel
    rw [ha]
    exact (canonical6740 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA426 + difference 2 3) (sourceB426 + difference 3 2) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA426 + difference 2 3) (sourceB426 + difference 3 2) sourceC426) = raw7243 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7243; decide +kernel
    rw [ha]
    exact (canonical7243 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA426 + difference 2 4) (sourceB426 + difference 4 2) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA426 + difference 2 4) (sourceB426 + difference 4 2) sourceC426) = raw7244 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7244; decide +kernel
    rw [ha]
    exact (canonical7244 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA426 + difference 2 5) (sourceB426 + difference 5 2) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA426 + difference 2 5) (sourceB426 + difference 5 2) sourceC426) = raw5688 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw5688; decide +kernel
    rw [ha]
    exact (canonical5688 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA426 + difference 3 0) (sourceB426 + difference 0 3) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA426 + difference 3 0) (sourceB426 + difference 0 3) sourceC426) = raw6733 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw6733; decide +kernel
    rw [ha]
    exact (canonical6733 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA426 + difference 3 1) (sourceB426 + difference 1 3) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA426 + difference 3 1) (sourceB426 + difference 1 3) sourceC426) = raw7077 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7077; decide +kernel
    rw [ha]
    exact (canonical7077 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA426 + difference 3 2) (sourceB426 + difference 2 3) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA426 + difference 3 2) (sourceB426 + difference 2 3) sourceC426) = raw6734 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw6734; decide +kernel
    rw [ha]
    exact (canonical6734 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA426 + difference 3 4) (sourceB426 + difference 4 3) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA426 + difference 3 4) (sourceB426 + difference 4 3) sourceC426) = raw6736 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw6736; decide +kernel
    rw [ha]
    exact (canonical6736 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA426 + difference 3 5) (sourceB426 + difference 5 3) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA426 + difference 3 5) (sourceB426 + difference 5 3) sourceC426) = raw6737 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw6737; decide +kernel
    rw [ha]
    exact (canonical6737 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA426 + difference 4 0) (sourceB426 + difference 0 4) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA426 + difference 4 0) (sourceB426 + difference 0 4) sourceC426) = raw7938 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7938; decide +kernel
    rw [ha]
    exact (canonical7938 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA426 + difference 4 1) (sourceB426 + difference 1 4) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA426 + difference 4 1) (sourceB426 + difference 1 4) sourceC426) = raw6412 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw6412; decide +kernel
    rw [ha]
    exact (canonical6412 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA426 + difference 4 2) (sourceB426 + difference 2 4) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA426 + difference 4 2) (sourceB426 + difference 2 4) sourceC426) = raw7939 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7939; decide +kernel
    rw [ha]
    exact (canonical7939 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA426 + difference 4 3) (sourceB426 + difference 3 4) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2787) := by
    have ha : (tripleCharges (sourceA426 + difference 4 3) (sourceB426 + difference 3 4) sourceC426) = raw7675 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7675; decide +kernel
    rw [ha]
    exact (canonical7675 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA426 + difference 4 5) (sourceB426 + difference 5 4) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA426 + difference 4 5) (sourceB426 + difference 5 4) sourceC426) = raw6397 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw6397; decide +kernel
    rw [ha]
    exact (canonical6397 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA426 + difference 5 0) (sourceB426 + difference 0 5) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA426 + difference 5 0) (sourceB426 + difference 0 5) sourceC426) = raw7940 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7940; decide +kernel
    rw [ha]
    exact (canonical7940 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA426 + difference 5 1) (sourceB426 + difference 1 5) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA426 + difference 5 1) (sourceB426 + difference 1 5) sourceC426) = raw6754 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw6754; decide +kernel
    rw [ha]
    exact (canonical6754 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA426 + difference 5 2) (sourceB426 + difference 2 5) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA426 + difference 5 2) (sourceB426 + difference 2 5) sourceC426) = raw7941 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7941; decide +kernel
    rw [ha]
    exact (canonical7941 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA426 + difference 5 3) (sourceB426 + difference 3 5) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2786) := by
    have ha : (tripleCharges (sourceA426 + difference 5 3) (sourceB426 + difference 3 5) sourceC426) = raw7942 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7942; decide +kernel
    rw [ha]
    exact (canonical7942 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA426 + difference 5 4) (sourceB426 + difference 4 5) sourceC426) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA426 + difference 5 4) (sourceB426 + difference 4 5) sourceC426) = raw7943 := by
      apply Matrix.ext; unfold tripleCharges sourceA426 sourceB426 sourceC426 difference raw7943; decide +kernel
    rw [ha]
    exact (canonical7943 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA426 sourceB426 sourceC426
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm426, Integer.Sparse.eval]
  linarith only [hs]

def sourceA427 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB427 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC427 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm427 : Integer.Sparse Master := [(Sum.inr 2723, 2), (Sum.inr 2742, 1), (Sum.inr 2743, 1), (Sum.inr 2787, 1), (Sum.inr 3039, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1), (Sum.inr 3065, 2), (Sum.inr 3077, 2), (Sum.inr 3078, 2), (Sum.inr 3088, 2), (Sum.inr 3089, 2), (Sum.inr 3101, 1), (Sum.inr 3102, 2), (Sum.inr 3103, 1), (Sum.inr 3123, 1), (Sum.inr 3124, 1), (Sum.inr 3225, 1), (Sum.inr 3227, 2), (Sum.inr 3229, 1), (Sum.inr 3230, 1)]

theorem sourceEq427 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm427 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA427 + difference 0 1) (sourceB427 + difference 1 0) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA427 + difference 0 1) (sourceB427 + difference 1 0) sourceC427) = raw6758 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw6758; decide +kernel
    rw [ha]
    exact (canonical6758 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA427 + difference 0 2) (sourceB427 + difference 2 0) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA427 + difference 0 2) (sourceB427 + difference 2 0) sourceC427) = raw7944 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7944; decide +kernel
    rw [ha]
    exact (canonical7944 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA427 + difference 0 3) (sourceB427 + difference 3 0) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2787) := by
    have ha : (tripleCharges (sourceA427 + difference 0 3) (sourceB427 + difference 3 0) sourceC427) = raw7945 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7945; decide +kernel
    rw [ha]
    exact (canonical7945 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA427 + difference 0 4) (sourceB427 + difference 4 0) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA427 + difference 0 4) (sourceB427 + difference 4 0) sourceC427) = raw7946 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7946; decide +kernel
    rw [ha]
    exact (canonical7946 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA427 + difference 0 5) (sourceB427 + difference 5 0) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA427 + difference 0 5) (sourceB427 + difference 5 0) sourceC427) = raw7947 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7947; decide +kernel
    rw [ha]
    exact (canonical7947 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA427 + difference 1 0) (sourceB427 + difference 0 1) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA427 + difference 1 0) (sourceB427 + difference 0 1) sourceC427) = raw5745 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw5745; decide +kernel
    rw [ha]
    exact (canonical5745 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA427 + difference 1 2) (sourceB427 + difference 2 1) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA427 + difference 1 2) (sourceB427 + difference 2 1) sourceC427) = raw7948 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7948; decide +kernel
    rw [ha]
    exact (canonical7948 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA427 + difference 1 3) (sourceB427 + difference 3 1) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA427 + difference 1 3) (sourceB427 + difference 3 1) sourceC427) = raw7949 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7949; decide +kernel
    rw [ha]
    exact (canonical7949 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA427 + difference 1 4) (sourceB427 + difference 4 1) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA427 + difference 1 4) (sourceB427 + difference 4 1) sourceC427) = raw7950 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7950; decide +kernel
    rw [ha]
    exact (canonical7950 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA427 + difference 1 5) (sourceB427 + difference 5 1) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA427 + difference 1 5) (sourceB427 + difference 5 1) sourceC427) = raw5719 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw5719; decide +kernel
    rw [ha]
    exact (canonical5719 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA427 + difference 2 0) (sourceB427 + difference 0 2) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA427 + difference 2 0) (sourceB427 + difference 0 2) sourceC427) = raw5744 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw5744; decide +kernel
    rw [ha]
    exact (canonical5744 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA427 + difference 2 1) (sourceB427 + difference 1 2) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA427 + difference 2 1) (sourceB427 + difference 1 2) sourceC427) = raw6768 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw6768; decide +kernel
    rw [ha]
    exact (canonical6768 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA427 + difference 2 3) (sourceB427 + difference 3 2) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA427 + difference 2 3) (sourceB427 + difference 3 2) sourceC427) = raw7261 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7261; decide +kernel
    rw [ha]
    exact (canonical7261 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA427 + difference 2 4) (sourceB427 + difference 4 2) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA427 + difference 2 4) (sourceB427 + difference 4 2) sourceC427) = raw7262 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7262; decide +kernel
    rw [ha]
    exact (canonical7262 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA427 + difference 2 5) (sourceB427 + difference 5 2) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA427 + difference 2 5) (sourceB427 + difference 5 2) sourceC427) = raw5718 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw5718; decide +kernel
    rw [ha]
    exact (canonical5718 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA427 + difference 3 0) (sourceB427 + difference 0 3) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA427 + difference 3 0) (sourceB427 + difference 0 3) sourceC427) = raw6761 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw6761; decide +kernel
    rw [ha]
    exact (canonical6761 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA427 + difference 3 1) (sourceB427 + difference 1 3) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA427 + difference 3 1) (sourceB427 + difference 1 3) sourceC427) = raw7091 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7091; decide +kernel
    rw [ha]
    exact (canonical7091 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA427 + difference 3 2) (sourceB427 + difference 2 3) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA427 + difference 3 2) (sourceB427 + difference 2 3) sourceC427) = raw6762 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw6762; decide +kernel
    rw [ha]
    exact (canonical6762 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA427 + difference 3 4) (sourceB427 + difference 4 3) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA427 + difference 3 4) (sourceB427 + difference 4 3) sourceC427) = raw6764 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw6764; decide +kernel
    rw [ha]
    exact (canonical6764 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA427 + difference 3 5) (sourceB427 + difference 5 3) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA427 + difference 3 5) (sourceB427 + difference 5 3) sourceC427) = raw6765 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw6765; decide +kernel
    rw [ha]
    exact (canonical6765 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA427 + difference 4 0) (sourceB427 + difference 0 4) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA427 + difference 4 0) (sourceB427 + difference 0 4) sourceC427) = raw7951 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7951; decide +kernel
    rw [ha]
    exact (canonical7951 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA427 + difference 4 1) (sourceB427 + difference 1 4) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA427 + difference 4 1) (sourceB427 + difference 1 4) sourceC427) = raw6434 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw6434; decide +kernel
    rw [ha]
    exact (canonical6434 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA427 + difference 4 2) (sourceB427 + difference 2 4) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA427 + difference 4 2) (sourceB427 + difference 2 4) sourceC427) = raw7952 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7952; decide +kernel
    rw [ha]
    exact (canonical7952 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA427 + difference 4 3) (sourceB427 + difference 3 4) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3123) := by
    have ha : (tripleCharges (sourceA427 + difference 4 3) (sourceB427 + difference 3 4) sourceC427) = raw7691 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7691; decide +kernel
    rw [ha]
    exact (canonical7691 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA427 + difference 4 5) (sourceB427 + difference 5 4) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA427 + difference 4 5) (sourceB427 + difference 5 4) sourceC427) = raw6419 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw6419; decide +kernel
    rw [ha]
    exact (canonical6419 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA427 + difference 5 0) (sourceB427 + difference 0 5) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA427 + difference 5 0) (sourceB427 + difference 0 5) sourceC427) = raw7953 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7953; decide +kernel
    rw [ha]
    exact (canonical7953 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA427 + difference 5 1) (sourceB427 + difference 1 5) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA427 + difference 5 1) (sourceB427 + difference 1 5) sourceC427) = raw6782 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw6782; decide +kernel
    rw [ha]
    exact (canonical6782 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA427 + difference 5 2) (sourceB427 + difference 2 5) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA427 + difference 5 2) (sourceB427 + difference 2 5) sourceC427) = raw7954 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7954; decide +kernel
    rw [ha]
    exact (canonical7954 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA427 + difference 5 3) (sourceB427 + difference 3 5) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA427 + difference 5 3) (sourceB427 + difference 3 5) sourceC427) = raw7955 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7955; decide +kernel
    rw [ha]
    exact (canonical7955 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA427 + difference 5 4) (sourceB427 + difference 4 5) sourceC427) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA427 + difference 5 4) (sourceB427 + difference 4 5) sourceC427) = raw7956 := by
      apply Matrix.ext; unfold tripleCharges sourceA427 sourceB427 sourceC427 difference raw7956; decide +kernel
    rw [ha]
    exact (canonical7956 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA427 sourceB427 sourceC427
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm427, Integer.Sparse.eval]
  linarith only [hs]

def sourceA428 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB428 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC428 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm428 : Integer.Sparse Master := [(Sum.inr 3544, 2), (Sum.inr 3547, 1), (Sum.inr 3548, 1), (Sum.inr 3627, 1), (Sum.inr 3635, 1), (Sum.inr 4084, -1)]

theorem sourceEq428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm428 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA428 + difference 0 0) (sourceB428 + difference 0 0) sourceC428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA428 + difference 0 0) (sourceB428 + difference 0 0) sourceC428) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA428 sourceB428 sourceC428 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA428 + difference 0 1) (sourceB428 + difference 1 0) sourceC428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA428 + difference 0 1) (sourceB428 + difference 1 0) sourceC428) = raw6787 := by
      apply Matrix.ext; unfold tripleCharges sourceA428 sourceB428 sourceC428 difference raw6787; decide +kernel
    rw [ha]
    exact (canonical6787 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA428 + difference 0 2) (sourceB428 + difference 2 0) sourceC428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA428 + difference 0 2) (sourceB428 + difference 2 0) sourceC428) = raw7957 := by
      apply Matrix.ext; unfold tripleCharges sourceA428 sourceB428 sourceC428 difference raw7957; decide +kernel
    rw [ha]
    exact (canonical7957 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA428 + difference 0 3) (sourceB428 + difference 3 0) sourceC428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3635) := by
    have ha : (tripleCharges (sourceA428 + difference 0 3) (sourceB428 + difference 3 0) sourceC428) = raw7958 := by
      apply Matrix.ext; unfold tripleCharges sourceA428 sourceB428 sourceC428 difference raw7958; decide +kernel
    rw [ha]
    exact (canonical7958 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA428 + difference 0 4) (sourceB428 + difference 4 0) sourceC428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA428 + difference 0 4) (sourceB428 + difference 4 0) sourceC428) = raw7959 := by
      apply Matrix.ext; unfold tripleCharges sourceA428 sourceB428 sourceC428 difference raw7959; decide +kernel
    rw [ha]
    exact (canonical7959 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA428 + difference 0 5) (sourceB428 + difference 5 0) sourceC428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA428 + difference 0 5) (sourceB428 + difference 5 0) sourceC428) = raw7960 := by
      apply Matrix.ext; unfold tripleCharges sourceA428 sourceB428 sourceC428 difference raw7960; decide +kernel
    rw [ha]
    exact (canonical7960 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA428 + sourceB428) sourceC428) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA428 + sourceB428) sourceC428) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA428 sourceB428 sourceC428 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA428 sourceB428 sourceC428
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm428, Integer.Sparse.eval]
  linarith only [hs]

def sourceA429 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB429 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC429 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm429 : Integer.Sparse Master := [(Sum.inr 2262, 2), (Sum.inr 2264, 1), (Sum.inr 2266, 1), (Sum.inr 2291, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

theorem sourceEq429 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm429 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA429 + difference 0 0) (sourceB429 + difference 0 0) sourceC429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA429 + difference 0 0) (sourceB429 + difference 0 0) sourceC429) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA429 sourceB429 sourceC429 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA429 + difference 1 0) (sourceB429 + difference 0 1) sourceC429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA429 + difference 1 0) (sourceB429 + difference 0 1) sourceC429) = raw5769 := by
      apply Matrix.ext; unfold tripleCharges sourceA429 sourceB429 sourceC429 difference raw5769; decide +kernel
    rw [ha]
    exact (canonical5769 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA429 + difference 2 0) (sourceB429 + difference 0 2) sourceC429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA429 + difference 2 0) (sourceB429 + difference 0 2) sourceC429) = raw5768 := by
      apply Matrix.ext; unfold tripleCharges sourceA429 sourceB429 sourceC429 difference raw5768; decide +kernel
    rw [ha]
    exact (canonical5768 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA429 + difference 3 0) (sourceB429 + difference 0 3) sourceC429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA429 + difference 3 0) (sourceB429 + difference 0 3) sourceC429) = raw6790 := by
      apply Matrix.ext; unfold tripleCharges sourceA429 sourceB429 sourceC429 difference raw6790; decide +kernel
    rw [ha]
    exact (canonical6790 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA429 + difference 4 0) (sourceB429 + difference 0 4) sourceC429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA429 + difference 4 0) (sourceB429 + difference 0 4) sourceC429) = raw7961 := by
      apply Matrix.ext; unfold tripleCharges sourceA429 sourceB429 sourceC429 difference raw7961; decide +kernel
    rw [ha]
    exact (canonical7961 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA429 + difference 5 0) (sourceB429 + difference 0 5) sourceC429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA429 + difference 5 0) (sourceB429 + difference 0 5) sourceC429) = raw7962 := by
      apply Matrix.ext; unfold tripleCharges sourceA429 sourceB429 sourceC429 difference raw7962; decide +kernel
    rw [ha]
    exact (canonical7962 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA429 + sourceB429) sourceC429) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA429 + sourceB429) sourceC429) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA429 sourceB429 sourceC429 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA429 sourceB429 sourceC429
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm429, Integer.Sparse.eval]
  linarith only [hs]

def sourceA430 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB430 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC430 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm430 : Integer.Sparse Master := [(Sum.inr 3627, 3), (Sum.inr 3629, 1), (Sum.inr 3635, 2), (Sum.inr 4084, -1)]

theorem sourceEq430 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm430 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA430 + difference 0 3) (sourceB430 + difference 3 0) sourceC430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3635) := by
    have ha : (tripleCharges (sourceA430 + difference 0 3) (sourceB430 + difference 3 0) sourceC430) = raw7958 := by
      apply Matrix.ext; unfold tripleCharges sourceA430 sourceB430 sourceC430 difference raw7958; decide +kernel
    rw [ha]
    exact (canonical7958 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA430 + difference 1 3) (sourceB430 + difference 3 1) sourceC430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA430 + difference 1 3) (sourceB430 + difference 3 1) sourceC430) = raw7963 := by
      apply Matrix.ext; unfold tripleCharges sourceA430 sourceB430 sourceC430 difference raw7963; decide +kernel
    rw [ha]
    exact (canonical7963 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA430 + difference 2 3) (sourceB430 + difference 3 2) sourceC430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA430 + difference 2 3) (sourceB430 + difference 3 2) sourceC430) = raw7282 := by
      apply Matrix.ext; unfold tripleCharges sourceA430 sourceB430 sourceC430 difference raw7282; decide +kernel
    rw [ha]
    exact (canonical7282 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA430 + difference 3 3) (sourceB430 + difference 3 3) sourceC430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA430 + difference 3 3) (sourceB430 + difference 3 3) sourceC430) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA430 sourceB430 sourceC430 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA430 + difference 4 3) (sourceB430 + difference 3 4) sourceC430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3635) := by
    have ha : (tripleCharges (sourceA430 + difference 4 3) (sourceB430 + difference 3 4) sourceC430) = raw7697 := by
      apply Matrix.ext; unfold tripleCharges sourceA430 sourceB430 sourceC430 difference raw7697; decide +kernel
    rw [ha]
    exact (canonical7697 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA430 + difference 5 3) (sourceB430 + difference 3 5) sourceC430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3629) := by
    have ha : (tripleCharges (sourceA430 + difference 5 3) (sourceB430 + difference 3 5) sourceC430) = raw7964 := by
      apply Matrix.ext; unfold tripleCharges sourceA430 sourceB430 sourceC430 difference raw7964; decide +kernel
    rw [ha]
    exact (canonical7964 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA430 + sourceB430) sourceC430) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA430 + sourceB430) sourceC430) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA430 sourceB430 sourceC430 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA430 sourceB430 sourceC430
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm430, Integer.Sparse.eval]
  linarith only [hs]

def sourceA431 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB431 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC431 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm431 : Integer.Sparse Master := [(Sum.inr 3548, 1), (Sum.inr 3580, 2), (Sum.inr 3582, 1), (Sum.inr 3584, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

theorem sourceEq431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm431 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA431 + difference 0 4) (sourceB431 + difference 4 0) sourceC431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA431 + difference 0 4) (sourceB431 + difference 4 0) sourceC431) = raw7959 := by
      apply Matrix.ext; unfold tripleCharges sourceA431 sourceB431 sourceC431 difference raw7959; decide +kernel
    rw [ha]
    exact (canonical7959 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA431 + difference 1 4) (sourceB431 + difference 4 1) sourceC431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA431 + difference 1 4) (sourceB431 + difference 4 1) sourceC431) = raw7965 := by
      apply Matrix.ext; unfold tripleCharges sourceA431 sourceB431 sourceC431 difference raw7965; decide +kernel
    rw [ha]
    exact (canonical7965 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA431 + difference 2 4) (sourceB431 + difference 4 2) sourceC431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA431 + difference 2 4) (sourceB431 + difference 4 2) sourceC431) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA431 sourceB431 sourceC431 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA431 + difference 3 4) (sourceB431 + difference 4 3) sourceC431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA431 + difference 3 4) (sourceB431 + difference 4 3) sourceC431) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA431 sourceB431 sourceC431 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA431 + difference 4 4) (sourceB431 + difference 4 4) sourceC431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA431 + difference 4 4) (sourceB431 + difference 4 4) sourceC431) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA431 sourceB431 sourceC431 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA431 + difference 5 4) (sourceB431 + difference 4 5) sourceC431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA431 + difference 5 4) (sourceB431 + difference 4 5) sourceC431) = raw7966 := by
      apply Matrix.ext; unfold tripleCharges sourceA431 sourceB431 sourceC431 difference raw7966; decide +kernel
    rw [ha]
    exact (canonical7966 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA431 + sourceB431) sourceC431) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA431 + sourceB431) sourceC431) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA431 sourceB431 sourceC431 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA431 sourceB431 sourceC431
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm431, Integer.Sparse.eval]
  linarith only [hs]

def sourceA432 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB432 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC432 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm432 : Integer.Sparse Master := [(Sum.inr 2264, 1), (Sum.inr 3533, 2), (Sum.inr 3582, 1), (Sum.inr 3627, 1), (Sum.inr 3629, 1), (Sum.inr 4084, -1)]

theorem sourceEq432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm432 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA432 + difference 5 0) (sourceB432 + difference 0 5) sourceC432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA432 + difference 5 0) (sourceB432 + difference 0 5) sourceC432) = raw7962 := by
      apply Matrix.ext; unfold tripleCharges sourceA432 sourceB432 sourceC432 difference raw7962; decide +kernel
    rw [ha]
    exact (canonical7962 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA432 + difference 5 1) (sourceB432 + difference 1 5) sourceC432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA432 + difference 5 1) (sourceB432 + difference 1 5) sourceC432) = raw6811 := by
      apply Matrix.ext; unfold tripleCharges sourceA432 sourceB432 sourceC432 difference raw6811; decide +kernel
    rw [ha]
    exact (canonical6811 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA432 + difference 5 2) (sourceB432 + difference 2 5) sourceC432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA432 + difference 5 2) (sourceB432 + difference 2 5) sourceC432) = raw7967 := by
      apply Matrix.ext; unfold tripleCharges sourceA432 sourceB432 sourceC432 difference raw7967; decide +kernel
    rw [ha]
    exact (canonical7967 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA432 + difference 5 3) (sourceB432 + difference 3 5) sourceC432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3629) := by
    have ha : (tripleCharges (sourceA432 + difference 5 3) (sourceB432 + difference 3 5) sourceC432) = raw7964 := by
      apply Matrix.ext; unfold tripleCharges sourceA432 sourceB432 sourceC432 difference raw7964; decide +kernel
    rw [ha]
    exact (canonical7964 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA432 + difference 5 4) (sourceB432 + difference 4 5) sourceC432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA432 + difference 5 4) (sourceB432 + difference 4 5) sourceC432) = raw7966 := by
      apply Matrix.ext; unfold tripleCharges sourceA432 sourceB432 sourceC432 difference raw7966; decide +kernel
    rw [ha]
    exact (canonical7966 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA432 + difference 5 5) (sourceB432 + difference 5 5) sourceC432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA432 + difference 5 5) (sourceB432 + difference 5 5) sourceC432) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA432 sourceB432 sourceC432 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA432 + sourceB432) sourceC432) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA432 + sourceB432) sourceC432) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA432 sourceB432 sourceC432 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA432 sourceB432 sourceC432
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm432, Integer.Sparse.eval]
  linarith only [hs]

def sourceA433 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB433 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC433 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm433 : Integer.Sparse Master := [(Sum.inr 4602, 2), (Sum.inr 4605, 1), (Sum.inr 4612, 1), (Sum.inr 4623, 1), (Sum.inr 4807, 2), (Sum.inr 4843, 1), (Sum.inr 4890, 1), (Sum.inr 5149, 2), (Sum.inr 5152, 2), (Sum.inr 5172, 2), (Sum.inr 5204, 2), (Sum.inr 5207, 1), (Sum.inr 5284, 2), (Sum.inr 5292, 2), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5307, 1), (Sum.inr 5435, 2), (Sum.inr 5443, 1), (Sum.inr 5453, 1), (Sum.inr 5454, 1)]

theorem sourceEq433 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm433 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA433 + difference 0 1) (sourceB433 + difference 1 0) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA433 + difference 0 1) (sourceB433 + difference 1 0) sourceC433) = raw2682 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw2682; decide +kernel
    rw [ha]
    exact (canonical2682 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA433 + difference 0 2) (sourceB433 + difference 2 0) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA433 + difference 0 2) (sourceB433 + difference 2 0) sourceC433) = raw2683 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw2683; decide +kernel
    rw [ha]
    exact (canonical2683 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA433 + difference 0 3) (sourceB433 + difference 3 0) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA433 + difference 0 3) (sourceB433 + difference 3 0) sourceC433) = raw2684 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw2684; decide +kernel
    rw [ha]
    exact (canonical2684 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA433 + difference 0 4) (sourceB433 + difference 4 0) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA433 + difference 0 4) (sourceB433 + difference 4 0) sourceC433) = raw4604 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw4604; decide +kernel
    rw [ha]
    exact (canonical4604 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA433 + difference 0 5) (sourceB433 + difference 5 0) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA433 + difference 0 5) (sourceB433 + difference 5 0) sourceC433) = raw2685 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw2685; decide +kernel
    rw [ha]
    exact (canonical2685 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA433 + difference 1 0) (sourceB433 + difference 0 1) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA433 + difference 1 0) (sourceB433 + difference 0 1) sourceC433) = raw7968 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7968; decide +kernel
    rw [ha]
    exact (canonical7968 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA433 + difference 1 2) (sourceB433 + difference 2 1) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA433 + difference 1 2) (sourceB433 + difference 2 1) sourceC433) = raw7969 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7969; decide +kernel
    rw [ha]
    exact (canonical7969 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA433 + difference 1 3) (sourceB433 + difference 3 1) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA433 + difference 1 3) (sourceB433 + difference 3 1) sourceC433) = raw7970 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7970; decide +kernel
    rw [ha]
    exact (canonical7970 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA433 + difference 1 4) (sourceB433 + difference 4 1) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA433 + difference 1 4) (sourceB433 + difference 4 1) sourceC433) = raw2666 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw2666; decide +kernel
    rw [ha]
    exact (canonical2666 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA433 + difference 1 5) (sourceB433 + difference 5 1) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA433 + difference 1 5) (sourceB433 + difference 5 1) sourceC433) = raw7971 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7971; decide +kernel
    rw [ha]
    exact (canonical7971 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA433 + difference 2 0) (sourceB433 + difference 0 2) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA433 + difference 2 0) (sourceB433 + difference 0 2) sourceC433) = raw7972 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7972; decide +kernel
    rw [ha]
    exact (canonical7972 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA433 + difference 2 1) (sourceB433 + difference 1 2) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA433 + difference 2 1) (sourceB433 + difference 1 2) sourceC433) = raw7973 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7973; decide +kernel
    rw [ha]
    exact (canonical7973 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA433 + difference 2 3) (sourceB433 + difference 3 2) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA433 + difference 2 3) (sourceB433 + difference 3 2) sourceC433) = raw7974 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7974; decide +kernel
    rw [ha]
    exact (canonical7974 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA433 + difference 2 4) (sourceB433 + difference 4 2) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA433 + difference 2 4) (sourceB433 + difference 4 2) sourceC433) = raw2671 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw2671; decide +kernel
    rw [ha]
    exact (canonical2671 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA433 + difference 2 5) (sourceB433 + difference 5 2) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA433 + difference 2 5) (sourceB433 + difference 5 2) sourceC433) = raw7975 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7975; decide +kernel
    rw [ha]
    exact (canonical7975 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA433 + difference 3 0) (sourceB433 + difference 0 3) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA433 + difference 3 0) (sourceB433 + difference 0 3) sourceC433) = raw7976 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7976; decide +kernel
    rw [ha]
    exact (canonical7976 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA433 + difference 3 1) (sourceB433 + difference 1 3) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA433 + difference 3 1) (sourceB433 + difference 1 3) sourceC433) = raw7977 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7977; decide +kernel
    rw [ha]
    exact (canonical7977 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA433 + difference 3 2) (sourceB433 + difference 2 3) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA433 + difference 3 2) (sourceB433 + difference 2 3) sourceC433) = raw7978 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7978; decide +kernel
    rw [ha]
    exact (canonical7978 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA433 + difference 3 4) (sourceB433 + difference 4 3) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA433 + difference 3 4) (sourceB433 + difference 4 3) sourceC433) = raw2676 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw2676; decide +kernel
    rw [ha]
    exact (canonical2676 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA433 + difference 3 5) (sourceB433 + difference 5 3) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA433 + difference 3 5) (sourceB433 + difference 5 3) sourceC433) = raw7979 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7979; decide +kernel
    rw [ha]
    exact (canonical7979 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA433 + difference 4 0) (sourceB433 + difference 0 4) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA433 + difference 4 0) (sourceB433 + difference 0 4) sourceC433) = raw7980 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7980; decide +kernel
    rw [ha]
    exact (canonical7980 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA433 + difference 4 1) (sourceB433 + difference 1 4) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA433 + difference 4 1) (sourceB433 + difference 1 4) sourceC433) = raw7981 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7981; decide +kernel
    rw [ha]
    exact (canonical7981 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA433 + difference 4 2) (sourceB433 + difference 2 4) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA433 + difference 4 2) (sourceB433 + difference 2 4) sourceC433) = raw7982 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7982; decide +kernel
    rw [ha]
    exact (canonical7982 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA433 + difference 4 3) (sourceB433 + difference 3 4) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA433 + difference 4 3) (sourceB433 + difference 3 4) sourceC433) = raw7983 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7983; decide +kernel
    rw [ha]
    exact (canonical7983 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA433 + difference 4 5) (sourceB433 + difference 5 4) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA433 + difference 4 5) (sourceB433 + difference 5 4) sourceC433) = raw7984 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw7984; decide +kernel
    rw [ha]
    exact (canonical7984 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA433 + difference 5 0) (sourceB433 + difference 0 5) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA433 + difference 5 0) (sourceB433 + difference 0 5) sourceC433) = raw4617 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw4617; decide +kernel
    rw [ha]
    exact (canonical4617 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA433 + difference 5 1) (sourceB433 + difference 1 5) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA433 + difference 5 1) (sourceB433 + difference 1 5) sourceC433) = raw4618 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw4618; decide +kernel
    rw [ha]
    exact (canonical4618 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA433 + difference 5 2) (sourceB433 + difference 2 5) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA433 + difference 5 2) (sourceB433 + difference 2 5) sourceC433) = raw4619 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw4619; decide +kernel
    rw [ha]
    exact (canonical4619 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA433 + difference 5 3) (sourceB433 + difference 3 5) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA433 + difference 5 3) (sourceB433 + difference 3 5) sourceC433) = raw4620 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw4620; decide +kernel
    rw [ha]
    exact (canonical4620 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA433 + difference 5 4) (sourceB433 + difference 4 5) sourceC433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA433 + difference 5 4) (sourceB433 + difference 4 5) sourceC433) = raw2686 := by
      apply Matrix.ext; unfold tripleCharges sourceA433 sourceB433 sourceC433 difference raw2686; decide +kernel
    rw [ha]
    exact (canonical2686 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA433 sourceB433 sourceC433
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm433, Integer.Sparse.eval]
  linarith only [hs]

def sourceA434 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB434 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC434 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm434 : Integer.Sparse Master := [(Sum.inr 1236, 2), (Sum.inr 1239, 1), (Sum.inr 1246, 1), (Sum.inr 1300, 1), (Sum.inr 2025, 2), (Sum.inr 2062, 1), (Sum.inr 2247, 1), (Sum.inr 2881, 2), (Sum.inr 2889, 1), (Sum.inr 2924, 2), (Sum.inr 2931, 2), (Sum.inr 2959, 2), (Sum.inr 3077, 2), (Sum.inr 3100, 2), (Sum.inr 3101, 1), (Sum.inr 3102, 1), (Sum.inr 3122, 1), (Sum.inr 3853, 2), (Sum.inr 3862, 1), (Sum.inr 3912, 1), (Sum.inr 4040, 1)]

theorem sourceEq434 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm434 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA434 + difference 0 1) (sourceB434 + difference 1 0) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA434 + difference 0 1) (sourceB434 + difference 1 0) sourceC434) = raw2712 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw2712; decide +kernel
    rw [ha]
    exact (canonical2712 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA434 + difference 0 2) (sourceB434 + difference 2 0) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA434 + difference 0 2) (sourceB434 + difference 2 0) sourceC434) = raw2713 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw2713; decide +kernel
    rw [ha]
    exact (canonical2713 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA434 + difference 0 3) (sourceB434 + difference 3 0) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA434 + difference 0 3) (sourceB434 + difference 3 0) sourceC434) = raw2714 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw2714; decide +kernel
    rw [ha]
    exact (canonical2714 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA434 + difference 0 4) (sourceB434 + difference 4 0) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3912) := by
    have ha : (tripleCharges (sourceA434 + difference 0 4) (sourceB434 + difference 4 0) sourceC434) = raw4626 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw4626; decide +kernel
    rw [ha]
    exact (canonical4626 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA434 + difference 0 5) (sourceB434 + difference 5 0) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4040) := by
    have ha : (tripleCharges (sourceA434 + difference 0 5) (sourceB434 + difference 5 0) sourceC434) = raw2715 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw2715; decide +kernel
    rw [ha]
    exact (canonical2715 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA434 + difference 1 0) (sourceB434 + difference 0 1) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA434 + difference 1 0) (sourceB434 + difference 0 1) sourceC434) = raw7985 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw7985; decide +kernel
    rw [ha]
    exact (canonical7985 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA434 + difference 1 2) (sourceB434 + difference 2 1) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA434 + difference 1 2) (sourceB434 + difference 2 1) sourceC434) = raw7986 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw7986; decide +kernel
    rw [ha]
    exact (canonical7986 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA434 + difference 1 3) (sourceB434 + difference 3 1) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA434 + difference 1 3) (sourceB434 + difference 3 1) sourceC434) = raw7987 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw7987; decide +kernel
    rw [ha]
    exact (canonical7987 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA434 + difference 1 4) (sourceB434 + difference 4 1) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA434 + difference 1 4) (sourceB434 + difference 4 1) sourceC434) = raw2696 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw2696; decide +kernel
    rw [ha]
    exact (canonical2696 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA434 + difference 1 5) (sourceB434 + difference 5 1) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA434 + difference 1 5) (sourceB434 + difference 5 1) sourceC434) = raw7988 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw7988; decide +kernel
    rw [ha]
    exact (canonical7988 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA434 + difference 2 0) (sourceB434 + difference 0 2) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA434 + difference 2 0) (sourceB434 + difference 0 2) sourceC434) = raw7989 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw7989; decide +kernel
    rw [ha]
    exact (canonical7989 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA434 + difference 2 1) (sourceB434 + difference 1 2) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA434 + difference 2 1) (sourceB434 + difference 1 2) sourceC434) = raw7990 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw7990; decide +kernel
    rw [ha]
    exact (canonical7990 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA434 + difference 2 3) (sourceB434 + difference 3 2) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA434 + difference 2 3) (sourceB434 + difference 3 2) sourceC434) = raw7991 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw7991; decide +kernel
    rw [ha]
    exact (canonical7991 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA434 + difference 2 4) (sourceB434 + difference 4 2) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA434 + difference 2 4) (sourceB434 + difference 4 2) sourceC434) = raw2701 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw2701; decide +kernel
    rw [ha]
    exact (canonical2701 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA434 + difference 2 5) (sourceB434 + difference 5 2) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA434 + difference 2 5) (sourceB434 + difference 5 2) sourceC434) = raw7992 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw7992; decide +kernel
    rw [ha]
    exact (canonical7992 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA434 + difference 3 0) (sourceB434 + difference 0 3) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1300) := by
    have ha : (tripleCharges (sourceA434 + difference 3 0) (sourceB434 + difference 0 3) sourceC434) = raw7993 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw7993; decide +kernel
    rw [ha]
    exact (canonical7993 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA434 + difference 3 1) (sourceB434 + difference 1 3) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2959) := by
    have ha : (tripleCharges (sourceA434 + difference 3 1) (sourceB434 + difference 1 3) sourceC434) = raw7994 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw7994; decide +kernel
    rw [ha]
    exact (canonical7994 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA434 + difference 3 2) (sourceB434 + difference 2 3) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2959) := by
    have ha : (tripleCharges (sourceA434 + difference 3 2) (sourceB434 + difference 2 3) sourceC434) = raw7995 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw7995; decide +kernel
    rw [ha]
    exact (canonical7995 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA434 + difference 3 4) (sourceB434 + difference 4 3) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA434 + difference 3 4) (sourceB434 + difference 4 3) sourceC434) = raw2706 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw2706; decide +kernel
    rw [ha]
    exact (canonical2706 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA434 + difference 3 5) (sourceB434 + difference 5 3) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3122) := by
    have ha : (tripleCharges (sourceA434 + difference 3 5) (sourceB434 + difference 5 3) sourceC434) = raw7996 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw7996; decide +kernel
    rw [ha]
    exact (canonical7996 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA434 + difference 4 0) (sourceB434 + difference 0 4) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA434 + difference 4 0) (sourceB434 + difference 0 4) sourceC434) = raw7997 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw7997; decide +kernel
    rw [ha]
    exact (canonical7997 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA434 + difference 4 1) (sourceB434 + difference 1 4) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA434 + difference 4 1) (sourceB434 + difference 1 4) sourceC434) = raw7998 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw7998; decide +kernel
    rw [ha]
    exact (canonical7998 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA434 + difference 4 2) (sourceB434 + difference 2 4) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA434 + difference 4 2) (sourceB434 + difference 2 4) sourceC434) = raw7999 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw7999; decide +kernel
    rw [ha]
    exact (canonical7999 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA434 + difference 4 3) (sourceB434 + difference 3 4) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA434 + difference 4 3) (sourceB434 + difference 3 4) sourceC434) = raw8000 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw8000; decide +kernel
    rw [ha]
    exact (canonical8000 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA434 + difference 4 5) (sourceB434 + difference 5 4) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA434 + difference 4 5) (sourceB434 + difference 5 4) sourceC434) = raw8001 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw8001; decide +kernel
    rw [ha]
    exact (canonical8001 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA434 + difference 5 0) (sourceB434 + difference 0 5) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA434 + difference 5 0) (sourceB434 + difference 0 5) sourceC434) = raw4639 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw4639; decide +kernel
    rw [ha]
    exact (canonical4639 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA434 + difference 5 1) (sourceB434 + difference 1 5) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA434 + difference 5 1) (sourceB434 + difference 1 5) sourceC434) = raw4640 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw4640; decide +kernel
    rw [ha]
    exact (canonical4640 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA434 + difference 5 2) (sourceB434 + difference 2 5) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA434 + difference 5 2) (sourceB434 + difference 2 5) sourceC434) = raw4641 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw4641; decide +kernel
    rw [ha]
    exact (canonical4641 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA434 + difference 5 3) (sourceB434 + difference 3 5) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA434 + difference 5 3) (sourceB434 + difference 3 5) sourceC434) = raw4642 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw4642; decide +kernel
    rw [ha]
    exact (canonical4642 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA434 + difference 5 4) (sourceB434 + difference 4 5) sourceC434) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA434 + difference 5 4) (sourceB434 + difference 4 5) sourceC434) = raw2716 := by
      apply Matrix.ext; unfold tripleCharges sourceA434 sourceB434 sourceC434 difference raw2716; decide +kernel
    rw [ha]
    exact (canonical2716 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA434 sourceB434 sourceC434
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm434, Integer.Sparse.eval]
  linarith only [hs]

def sourceA435 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB435 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC435 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceForm435 : Integer.Sparse Master := [(Sum.inr 4461, 2), (Sum.inr 4463, 1), (Sum.inr 4466, 1), (Sum.inr 4503, 1), (Sum.inr 5076, 2), (Sum.inr 5078, 2), (Sum.inr 5080, 2), (Sum.inr 5105, 2), (Sum.inr 5172, 2), (Sum.inr 5174, 1), (Sum.inr 5176, 1), (Sum.inr 5290, 2), (Sum.inr 5291, 1), (Sum.inr 5294, 2), (Sum.inr 5296, 1), (Sum.inr 5304, 1), (Sum.inr 5310, 1), (Sum.inr 5434, 2), (Sum.inr 5442, 1), (Sum.inr 5455, 1), (Sum.inr 5492, 1)]

theorem sourceEq435 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm435 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA435 + difference 0 1) (sourceB435 + difference 1 0) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA435 + difference 0 1) (sourceB435 + difference 1 0) sourceC435) = raw8002 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8002; decide +kernel
    rw [ha]
    exact (canonical8002 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA435 + difference 0 2) (sourceB435 + difference 2 0) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA435 + difference 0 2) (sourceB435 + difference 2 0) sourceC435) = raw8003 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8003; decide +kernel
    rw [ha]
    exact (canonical8003 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA435 + difference 0 3) (sourceB435 + difference 3 0) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA435 + difference 0 3) (sourceB435 + difference 3 0) sourceC435) = raw8004 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8004; decide +kernel
    rw [ha]
    exact (canonical8004 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA435 + difference 0 4) (sourceB435 + difference 4 0) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA435 + difference 0 4) (sourceB435 + difference 4 0) sourceC435) = raw8005 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8005; decide +kernel
    rw [ha]
    exact (canonical8005 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA435 + difference 0 5) (sourceB435 + difference 5 0) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA435 + difference 0 5) (sourceB435 + difference 5 0) sourceC435) = raw8006 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8006; decide +kernel
    rw [ha]
    exact (canonical8006 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA435 + difference 1 0) (sourceB435 + difference 0 1) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA435 + difference 1 0) (sourceB435 + difference 0 1) sourceC435) = raw8007 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8007; decide +kernel
    rw [ha]
    exact (canonical8007 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA435 + difference 1 2) (sourceB435 + difference 2 1) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA435 + difference 1 2) (sourceB435 + difference 2 1) sourceC435) = raw8008 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8008; decide +kernel
    rw [ha]
    exact (canonical8008 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA435 + difference 1 3) (sourceB435 + difference 3 1) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA435 + difference 1 3) (sourceB435 + difference 3 1) sourceC435) = raw8009 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8009; decide +kernel
    rw [ha]
    exact (canonical8009 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA435 + difference 1 4) (sourceB435 + difference 4 1) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA435 + difference 1 4) (sourceB435 + difference 4 1) sourceC435) = raw8010 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8010; decide +kernel
    rw [ha]
    exact (canonical8010 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA435 + difference 1 5) (sourceB435 + difference 5 1) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA435 + difference 1 5) (sourceB435 + difference 5 1) sourceC435) = raw8011 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8011; decide +kernel
    rw [ha]
    exact (canonical8011 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA435 + difference 2 0) (sourceB435 + difference 0 2) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA435 + difference 2 0) (sourceB435 + difference 0 2) sourceC435) = raw8012 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8012; decide +kernel
    rw [ha]
    exact (canonical8012 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA435 + difference 2 1) (sourceB435 + difference 1 2) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA435 + difference 2 1) (sourceB435 + difference 1 2) sourceC435) = raw8013 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8013; decide +kernel
    rw [ha]
    exact (canonical8013 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA435 + difference 2 3) (sourceB435 + difference 3 2) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA435 + difference 2 3) (sourceB435 + difference 3 2) sourceC435) = raw8014 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8014; decide +kernel
    rw [ha]
    exact (canonical8014 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA435 + difference 2 4) (sourceB435 + difference 4 2) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA435 + difference 2 4) (sourceB435 + difference 4 2) sourceC435) = raw8015 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8015; decide +kernel
    rw [ha]
    exact (canonical8015 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA435 + difference 2 5) (sourceB435 + difference 5 2) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA435 + difference 2 5) (sourceB435 + difference 5 2) sourceC435) = raw8016 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8016; decide +kernel
    rw [ha]
    exact (canonical8016 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA435 + difference 3 0) (sourceB435 + difference 0 3) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA435 + difference 3 0) (sourceB435 + difference 0 3) sourceC435) = raw8017 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8017; decide +kernel
    rw [ha]
    exact (canonical8017 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA435 + difference 3 1) (sourceB435 + difference 1 3) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA435 + difference 3 1) (sourceB435 + difference 1 3) sourceC435) = raw8018 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8018; decide +kernel
    rw [ha]
    exact (canonical8018 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA435 + difference 3 2) (sourceB435 + difference 2 3) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA435 + difference 3 2) (sourceB435 + difference 2 3) sourceC435) = raw8019 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8019; decide +kernel
    rw [ha]
    exact (canonical8019 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA435 + difference 3 4) (sourceB435 + difference 4 3) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA435 + difference 3 4) (sourceB435 + difference 4 3) sourceC435) = raw8020 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8020; decide +kernel
    rw [ha]
    exact (canonical8020 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA435 + difference 3 5) (sourceB435 + difference 5 3) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA435 + difference 3 5) (sourceB435 + difference 5 3) sourceC435) = raw8021 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8021; decide +kernel
    rw [ha]
    exact (canonical8021 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA435 + difference 4 0) (sourceB435 + difference 0 4) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA435 + difference 4 0) (sourceB435 + difference 0 4) sourceC435) = raw8022 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8022; decide +kernel
    rw [ha]
    exact (canonical8022 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA435 + difference 4 1) (sourceB435 + difference 1 4) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA435 + difference 4 1) (sourceB435 + difference 1 4) sourceC435) = raw8023 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8023; decide +kernel
    rw [ha]
    exact (canonical8023 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA435 + difference 4 2) (sourceB435 + difference 2 4) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA435 + difference 4 2) (sourceB435 + difference 2 4) sourceC435) = raw8024 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8024; decide +kernel
    rw [ha]
    exact (canonical8024 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA435 + difference 4 3) (sourceB435 + difference 3 4) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA435 + difference 4 3) (sourceB435 + difference 3 4) sourceC435) = raw8025 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8025; decide +kernel
    rw [ha]
    exact (canonical8025 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA435 + difference 4 5) (sourceB435 + difference 5 4) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA435 + difference 4 5) (sourceB435 + difference 5 4) sourceC435) = raw8026 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8026; decide +kernel
    rw [ha]
    exact (canonical8026 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA435 + difference 5 0) (sourceB435 + difference 0 5) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA435 + difference 5 0) (sourceB435 + difference 0 5) sourceC435) = raw8027 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8027; decide +kernel
    rw [ha]
    exact (canonical8027 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA435 + difference 5 1) (sourceB435 + difference 1 5) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA435 + difference 5 1) (sourceB435 + difference 1 5) sourceC435) = raw8028 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8028; decide +kernel
    rw [ha]
    exact (canonical8028 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA435 + difference 5 2) (sourceB435 + difference 2 5) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA435 + difference 5 2) (sourceB435 + difference 2 5) sourceC435) = raw8029 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8029; decide +kernel
    rw [ha]
    exact (canonical8029 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA435 + difference 5 3) (sourceB435 + difference 3 5) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA435 + difference 5 3) (sourceB435 + difference 3 5) sourceC435) = raw8030 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8030; decide +kernel
    rw [ha]
    exact (canonical8030 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA435 + difference 5 4) (sourceB435 + difference 4 5) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA435 + difference 5 4) (sourceB435 + difference 4 5) sourceC435) = raw8031 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8031; decide +kernel
    rw [ha]
    exact (canonical8031 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA435 sourceB435 sourceC435
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm435, Integer.Sparse.eval]
  linarith only [hs]

def sourceA436 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB436 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC436 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceForm436 : Integer.Sparse Master := [(Sum.inr 1044, 2), (Sum.inr 1046, 1), (Sum.inr 1049, 1), (Sum.inr 1087, 1), (Sum.inr 2483, 2), (Sum.inr 2485, 2), (Sum.inr 2488, 2), (Sum.inr 2515, 2), (Sum.inr 2599, 2), (Sum.inr 2601, 1), (Sum.inr 2604, 1), (Sum.inr 2764, 2), (Sum.inr 2765, 1), (Sum.inr 2768, 2), (Sum.inr 2770, 1), (Sum.inr 2782, 1), (Sum.inr 2788, 1), (Sum.inr 3982, 2), (Sum.inr 4001, 1), (Sum.inr 4017, 1), (Sum.inr 4019, 1)]

theorem sourceEq436 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm436 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA436 + difference 0 1) (sourceB436 + difference 1 0) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA436 + difference 0 1) (sourceB436 + difference 1 0) sourceC436) = raw8032 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8032; decide +kernel
    rw [ha]
    exact (canonical8032 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA436 + difference 0 2) (sourceB436 + difference 2 0) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA436 + difference 0 2) (sourceB436 + difference 2 0) sourceC436) = raw8033 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8033; decide +kernel
    rw [ha]
    exact (canonical8033 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA436 + difference 0 3) (sourceB436 + difference 3 0) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA436 + difference 0 3) (sourceB436 + difference 3 0) sourceC436) = raw8034 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8034; decide +kernel
    rw [ha]
    exact (canonical8034 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA436 + difference 0 4) (sourceB436 + difference 4 0) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4019) := by
    have ha : (tripleCharges (sourceA436 + difference 0 4) (sourceB436 + difference 4 0) sourceC436) = raw8035 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8035; decide +kernel
    rw [ha]
    exact (canonical8035 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA436 + difference 0 5) (sourceB436 + difference 5 0) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4017) := by
    have ha : (tripleCharges (sourceA436 + difference 0 5) (sourceB436 + difference 5 0) sourceC436) = raw8036 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8036; decide +kernel
    rw [ha]
    exact (canonical8036 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA436 + difference 1 0) (sourceB436 + difference 0 1) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA436 + difference 1 0) (sourceB436 + difference 0 1) sourceC436) = raw8037 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8037; decide +kernel
    rw [ha]
    exact (canonical8037 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA436 + difference 1 2) (sourceB436 + difference 2 1) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA436 + difference 1 2) (sourceB436 + difference 2 1) sourceC436) = raw8038 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8038; decide +kernel
    rw [ha]
    exact (canonical8038 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA436 + difference 1 3) (sourceB436 + difference 3 1) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2599) := by
    have ha : (tripleCharges (sourceA436 + difference 1 3) (sourceB436 + difference 3 1) sourceC436) = raw8039 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8039; decide +kernel
    rw [ha]
    exact (canonical8039 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA436 + difference 1 4) (sourceB436 + difference 4 1) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA436 + difference 1 4) (sourceB436 + difference 4 1) sourceC436) = raw8040 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8040; decide +kernel
    rw [ha]
    exact (canonical8040 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA436 + difference 1 5) (sourceB436 + difference 5 1) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA436 + difference 1 5) (sourceB436 + difference 5 1) sourceC436) = raw8041 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8041; decide +kernel
    rw [ha]
    exact (canonical8041 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA436 + difference 2 0) (sourceB436 + difference 0 2) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA436 + difference 2 0) (sourceB436 + difference 0 2) sourceC436) = raw8042 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8042; decide +kernel
    rw [ha]
    exact (canonical8042 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA436 + difference 2 1) (sourceB436 + difference 1 2) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA436 + difference 2 1) (sourceB436 + difference 1 2) sourceC436) = raw8043 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8043; decide +kernel
    rw [ha]
    exact (canonical8043 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA436 + difference 2 3) (sourceB436 + difference 3 2) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2599) := by
    have ha : (tripleCharges (sourceA436 + difference 2 3) (sourceB436 + difference 3 2) sourceC436) = raw8044 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8044; decide +kernel
    rw [ha]
    exact (canonical8044 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA436 + difference 2 4) (sourceB436 + difference 4 2) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA436 + difference 2 4) (sourceB436 + difference 4 2) sourceC436) = raw8045 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8045; decide +kernel
    rw [ha]
    exact (canonical8045 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA436 + difference 2 5) (sourceB436 + difference 5 2) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA436 + difference 2 5) (sourceB436 + difference 5 2) sourceC436) = raw8046 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8046; decide +kernel
    rw [ha]
    exact (canonical8046 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA436 + difference 3 0) (sourceB436 + difference 0 3) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA436 + difference 3 0) (sourceB436 + difference 0 3) sourceC436) = raw8047 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8047; decide +kernel
    rw [ha]
    exact (canonical8047 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA436 + difference 3 1) (sourceB436 + difference 1 3) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA436 + difference 3 1) (sourceB436 + difference 1 3) sourceC436) = raw8048 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8048; decide +kernel
    rw [ha]
    exact (canonical8048 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA436 + difference 3 2) (sourceB436 + difference 2 3) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA436 + difference 3 2) (sourceB436 + difference 2 3) sourceC436) = raw8049 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8049; decide +kernel
    rw [ha]
    exact (canonical8049 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA436 + difference 3 4) (sourceB436 + difference 4 3) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA436 + difference 3 4) (sourceB436 + difference 4 3) sourceC436) = raw8050 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8050; decide +kernel
    rw [ha]
    exact (canonical8050 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA436 + difference 3 5) (sourceB436 + difference 5 3) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA436 + difference 3 5) (sourceB436 + difference 5 3) sourceC436) = raw8051 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8051; decide +kernel
    rw [ha]
    exact (canonical8051 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA436 + difference 4 0) (sourceB436 + difference 0 4) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA436 + difference 4 0) (sourceB436 + difference 0 4) sourceC436) = raw8052 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8052; decide +kernel
    rw [ha]
    exact (canonical8052 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA436 + difference 4 1) (sourceB436 + difference 1 4) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA436 + difference 4 1) (sourceB436 + difference 1 4) sourceC436) = raw8053 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8053; decide +kernel
    rw [ha]
    exact (canonical8053 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA436 + difference 4 2) (sourceB436 + difference 2 4) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA436 + difference 4 2) (sourceB436 + difference 2 4) sourceC436) = raw8054 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8054; decide +kernel
    rw [ha]
    exact (canonical8054 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA436 + difference 4 3) (sourceB436 + difference 3 4) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2604) := by
    have ha : (tripleCharges (sourceA436 + difference 4 3) (sourceB436 + difference 3 4) sourceC436) = raw8055 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8055; decide +kernel
    rw [ha]
    exact (canonical8055 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA436 + difference 4 5) (sourceB436 + difference 5 4) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA436 + difference 4 5) (sourceB436 + difference 5 4) sourceC436) = raw8056 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8056; decide +kernel
    rw [ha]
    exact (canonical8056 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA436 + difference 5 0) (sourceB436 + difference 0 5) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA436 + difference 5 0) (sourceB436 + difference 0 5) sourceC436) = raw8057 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8057; decide +kernel
    rw [ha]
    exact (canonical8057 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA436 + difference 5 1) (sourceB436 + difference 1 5) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA436 + difference 5 1) (sourceB436 + difference 1 5) sourceC436) = raw8058 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8058; decide +kernel
    rw [ha]
    exact (canonical8058 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA436 + difference 5 2) (sourceB436 + difference 2 5) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA436 + difference 5 2) (sourceB436 + difference 2 5) sourceC436) = raw8059 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8059; decide +kernel
    rw [ha]
    exact (canonical8059 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA436 + difference 5 3) (sourceB436 + difference 3 5) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA436 + difference 5 3) (sourceB436 + difference 3 5) sourceC436) = raw8060 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8060; decide +kernel
    rw [ha]
    exact (canonical8060 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA436 + difference 5 4) (sourceB436 + difference 4 5) sourceC436) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA436 + difference 5 4) (sourceB436 + difference 4 5) sourceC436) = raw8061 := by
      apply Matrix.ext; unfold tripleCharges sourceA436 sourceB436 sourceC436 difference raw8061; decide +kernel
    rw [ha]
    exact (canonical8061 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA436 sourceB436 sourceC436
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm436, Integer.Sparse.eval]
  linarith only [hs]

def sourceA437 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB437 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC437 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm437 : Integer.Sparse Master := [(Sum.inr 4889, 2), (Sum.inr 4895, 1), (Sum.inr 4896, 1), (Sum.inr 4898, 1), (Sum.inr 5251, 2), (Sum.inr 5258, 2), (Sum.inr 5259, 2), (Sum.inr 5260, 2), (Sum.inr 5267, 2), (Sum.inr 5270, 2), (Sum.inr 5272, 1), (Sum.inr 5274, 1), (Sum.inr 5276, 1), (Sum.inr 5284, 2), (Sum.inr 5293, 1), (Sum.inr 5294, 2), (Sum.inr 5295, 1), (Sum.inr 5302, 1), (Sum.inr 5308, 1), (Sum.inr 5309, 1), (Sum.inr 5310, 1)]

theorem sourceEq437 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm437 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA437 + difference 0 1) (sourceB437 + difference 1 0) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA437 + difference 0 1) (sourceB437 + difference 1 0) sourceC437) = raw6371 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw6371; decide +kernel
    rw [ha]
    exact (canonical6371 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA437 + difference 0 2) (sourceB437 + difference 2 0) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA437 + difference 0 2) (sourceB437 + difference 2 0) sourceC437) = raw8062 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw8062; decide +kernel
    rw [ha]
    exact (canonical8062 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA437 + difference 0 3) (sourceB437 + difference 3 0) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA437 + difference 0 3) (sourceB437 + difference 3 0) sourceC437) = raw7646 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw7646; decide +kernel
    rw [ha]
    exact (canonical7646 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA437 + difference 0 4) (sourceB437 + difference 4 0) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA437 + difference 0 4) (sourceB437 + difference 4 0) sourceC437) = raw7921 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw7921; decide +kernel
    rw [ha]
    exact (canonical7921 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA437 + difference 0 5) (sourceB437 + difference 5 0) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA437 + difference 0 5) (sourceB437 + difference 5 0) sourceC437) = raw8063 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw8063; decide +kernel
    rw [ha]
    exact (canonical8063 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA437 + difference 1 0) (sourceB437 + difference 0 1) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA437 + difference 1 0) (sourceB437 + difference 0 1) sourceC437) = raw5680 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw5680; decide +kernel
    rw [ha]
    exact (canonical5680 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA437 + difference 1 2) (sourceB437 + difference 2 1) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA437 + difference 1 2) (sourceB437 + difference 2 1) sourceC437) = raw8064 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw8064; decide +kernel
    rw [ha]
    exact (canonical8064 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA437 + difference 1 3) (sourceB437 + difference 3 1) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA437 + difference 1 3) (sourceB437 + difference 3 1) sourceC437) = raw7651 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw7651; decide +kernel
    rw [ha]
    exact (canonical7651 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA437 + difference 1 4) (sourceB437 + difference 4 1) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA437 + difference 1 4) (sourceB437 + difference 4 1) sourceC437) = raw5659 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw5659; decide +kernel
    rw [ha]
    exact (canonical5659 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA437 + difference 1 5) (sourceB437 + difference 5 1) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA437 + difference 1 5) (sourceB437 + difference 5 1) sourceC437) = raw8065 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw8065; decide +kernel
    rw [ha]
    exact (canonical8065 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA437 + difference 2 0) (sourceB437 + difference 0 2) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA437 + difference 2 0) (sourceB437 + difference 0 2) sourceC437) = raw5679 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw5679; decide +kernel
    rw [ha]
    exact (canonical5679 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA437 + difference 2 1) (sourceB437 + difference 1 2) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA437 + difference 2 1) (sourceB437 + difference 1 2) sourceC437) = raw6379 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw6379; decide +kernel
    rw [ha]
    exact (canonical6379 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA437 + difference 2 3) (sourceB437 + difference 3 2) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA437 + difference 2 3) (sourceB437 + difference 3 2) sourceC437) = raw7527 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw7527; decide +kernel
    rw [ha]
    exact (canonical7527 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA437 + difference 2 4) (sourceB437 + difference 4 2) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA437 + difference 2 4) (sourceB437 + difference 4 2) sourceC437) = raw5658 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw5658; decide +kernel
    rw [ha]
    exact (canonical5658 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA437 + difference 2 5) (sourceB437 + difference 5 2) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA437 + difference 2 5) (sourceB437 + difference 5 2) sourceC437) = raw7528 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw7528; decide +kernel
    rw [ha]
    exact (canonical7528 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA437 + difference 3 0) (sourceB437 + difference 0 3) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA437 + difference 3 0) (sourceB437 + difference 0 3) sourceC437) = raw7053 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw7053; decide +kernel
    rw [ha]
    exact (canonical7053 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA437 + difference 3 1) (sourceB437 + difference 1 3) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA437 + difference 3 1) (sourceB437 + difference 1 3) sourceC437) = raw6384 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw6384; decide +kernel
    rw [ha]
    exact (canonical6384 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA437 + difference 3 2) (sourceB437 + difference 2 3) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA437 + difference 3 2) (sourceB437 + difference 2 3) sourceC437) = raw7054 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw7054; decide +kernel
    rw [ha]
    exact (canonical7054 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA437 + difference 3 4) (sourceB437 + difference 4 3) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA437 + difference 3 4) (sourceB437 + difference 4 3) sourceC437) = raw6709 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw6709; decide +kernel
    rw [ha]
    exact (canonical6709 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA437 + difference 3 5) (sourceB437 + difference 5 3) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA437 + difference 3 5) (sourceB437 + difference 5 3) sourceC437) = raw7055 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw7055; decide +kernel
    rw [ha]
    exact (canonical7055 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA437 + difference 4 0) (sourceB437 + difference 0 4) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA437 + difference 4 0) (sourceB437 + difference 0 4) sourceC437) = raw6373 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw6373; decide +kernel
    rw [ha]
    exact (canonical6373 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA437 + difference 4 1) (sourceB437 + difference 1 4) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA437 + difference 4 1) (sourceB437 + difference 1 4) sourceC437) = raw6028 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw6028; decide +kernel
    rw [ha]
    exact (canonical6028 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA437 + difference 4 2) (sourceB437 + difference 2 4) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA437 + difference 4 2) (sourceB437 + difference 2 4) sourceC437) = raw6374 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw6374; decide +kernel
    rw [ha]
    exact (canonical6374 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA437 + difference 4 3) (sourceB437 + difference 3 4) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA437 + difference 4 3) (sourceB437 + difference 3 4) sourceC437) = raw6018 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw6018; decide +kernel
    rw [ha]
    exact (canonical6018 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA437 + difference 4 5) (sourceB437 + difference 5 4) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA437 + difference 4 5) (sourceB437 + difference 5 4) sourceC437) = raw6376 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw6376; decide +kernel
    rw [ha]
    exact (canonical6376 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA437 + difference 5 0) (sourceB437 + difference 0 5) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA437 + difference 5 0) (sourceB437 + difference 0 5) sourceC437) = raw7925 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw7925; decide +kernel
    rw [ha]
    exact (canonical7925 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA437 + difference 5 1) (sourceB437 + difference 1 5) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA437 + difference 5 1) (sourceB437 + difference 1 5) sourceC437) = raw6390 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw6390; decide +kernel
    rw [ha]
    exact (canonical6390 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA437 + difference 5 2) (sourceB437 + difference 2 5) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA437 + difference 5 2) (sourceB437 + difference 2 5) sourceC437) = raw7926 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw7926; decide +kernel
    rw [ha]
    exact (canonical7926 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA437 + difference 5 3) (sourceB437 + difference 3 5) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA437 + difference 5 3) (sourceB437 + difference 3 5) sourceC437) = raw7659 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw7659; decide +kernel
    rw [ha]
    exact (canonical7659 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA437 + difference 5 4) (sourceB437 + difference 4 5) sourceC437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA437 + difference 5 4) (sourceB437 + difference 4 5) sourceC437) = raw6707 := by
      apply Matrix.ext; unfold tripleCharges sourceA437 sourceB437 sourceC437 difference raw6707; decide +kernel
    rw [ha]
    exact (canonical6707 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA437 sourceB437 sourceC437
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm437, Integer.Sparse.eval]
  linarith only [hs]

def sourceA438 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB438 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC438 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm438 : Integer.Sparse Master := [(Sum.inr 2245, 2), (Sum.inr 2265, 1), (Sum.inr 2266, 1), (Sum.inr 2279, 1), (Sum.inr 2710, 2), (Sum.inr 2723, 2), (Sum.inr 2724, 2), (Sum.inr 2732, 2), (Sum.inr 2753, 2), (Sum.inr 2754, 2), (Sum.inr 2767, 1), (Sum.inr 2768, 2), (Sum.inr 2769, 1), (Sum.inr 2776, 1), (Sum.inr 2777, 1), (Sum.inr 2787, 1), (Sum.inr 2788, 1), (Sum.inr 3089, 2), (Sum.inr 3112, 1), (Sum.inr 3113, 1), (Sum.inr 3124, 1)]

theorem sourceEq438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm438 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA438 + difference 0 1) (sourceB438 + difference 1 0) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA438 + difference 0 1) (sourceB438 + difference 1 0) sourceC438) = raw6393 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw6393; decide +kernel
    rw [ha]
    exact (canonical6393 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA438 + difference 0 2) (sourceB438 + difference 2 0) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA438 + difference 0 2) (sourceB438 + difference 2 0) sourceC438) = raw8066 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw8066; decide +kernel
    rw [ha]
    exact (canonical8066 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA438 + difference 0 3) (sourceB438 + difference 3 0) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA438 + difference 0 3) (sourceB438 + difference 3 0) sourceC438) = raw7662 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw7662; decide +kernel
    rw [ha]
    exact (canonical7662 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA438 + difference 0 4) (sourceB438 + difference 4 0) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA438 + difference 0 4) (sourceB438 + difference 4 0) sourceC438) = raw7934 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw7934; decide +kernel
    rw [ha]
    exact (canonical7934 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA438 + difference 0 5) (sourceB438 + difference 5 0) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3113) := by
    have ha : (tripleCharges (sourceA438 + difference 0 5) (sourceB438 + difference 5 0) sourceC438) = raw8067 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw8067; decide +kernel
    rw [ha]
    exact (canonical8067 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA438 + difference 1 0) (sourceB438 + difference 0 1) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA438 + difference 1 0) (sourceB438 + difference 0 1) sourceC438) = raw5710 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw5710; decide +kernel
    rw [ha]
    exact (canonical5710 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA438 + difference 1 2) (sourceB438 + difference 2 1) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA438 + difference 1 2) (sourceB438 + difference 2 1) sourceC438) = raw8068 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw8068; decide +kernel
    rw [ha]
    exact (canonical8068 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA438 + difference 1 3) (sourceB438 + difference 3 1) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA438 + difference 1 3) (sourceB438 + difference 3 1) sourceC438) = raw7667 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw7667; decide +kernel
    rw [ha]
    exact (canonical7667 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA438 + difference 1 4) (sourceB438 + difference 4 1) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA438 + difference 1 4) (sourceB438 + difference 4 1) sourceC438) = raw5689 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw5689; decide +kernel
    rw [ha]
    exact (canonical5689 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA438 + difference 1 5) (sourceB438 + difference 5 1) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA438 + difference 1 5) (sourceB438 + difference 5 1) sourceC438) = raw8069 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw8069; decide +kernel
    rw [ha]
    exact (canonical8069 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA438 + difference 2 0) (sourceB438 + difference 0 2) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA438 + difference 2 0) (sourceB438 + difference 0 2) sourceC438) = raw5709 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw5709; decide +kernel
    rw [ha]
    exact (canonical5709 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA438 + difference 2 1) (sourceB438 + difference 1 2) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA438 + difference 2 1) (sourceB438 + difference 1 2) sourceC438) = raw6401 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw6401; decide +kernel
    rw [ha]
    exact (canonical6401 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA438 + difference 2 3) (sourceB438 + difference 3 2) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA438 + difference 2 3) (sourceB438 + difference 3 2) sourceC438) = raw7536 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw7536; decide +kernel
    rw [ha]
    exact (canonical7536 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA438 + difference 2 4) (sourceB438 + difference 4 2) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA438 + difference 2 4) (sourceB438 + difference 4 2) sourceC438) = raw5688 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw5688; decide +kernel
    rw [ha]
    exact (canonical5688 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA438 + difference 2 5) (sourceB438 + difference 5 2) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA438 + difference 2 5) (sourceB438 + difference 5 2) sourceC438) = raw7537 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw7537; decide +kernel
    rw [ha]
    exact (canonical7537 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA438 + difference 3 0) (sourceB438 + difference 0 3) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA438 + difference 3 0) (sourceB438 + difference 0 3) sourceC438) = raw7067 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw7067; decide +kernel
    rw [ha]
    exact (canonical7067 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA438 + difference 3 1) (sourceB438 + difference 1 3) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA438 + difference 3 1) (sourceB438 + difference 1 3) sourceC438) = raw6406 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw6406; decide +kernel
    rw [ha]
    exact (canonical6406 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA438 + difference 3 2) (sourceB438 + difference 2 3) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA438 + difference 3 2) (sourceB438 + difference 2 3) sourceC438) = raw7068 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw7068; decide +kernel
    rw [ha]
    exact (canonical7068 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA438 + difference 3 4) (sourceB438 + difference 4 3) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA438 + difference 3 4) (sourceB438 + difference 4 3) sourceC438) = raw6737 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw6737; decide +kernel
    rw [ha]
    exact (canonical6737 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA438 + difference 3 5) (sourceB438 + difference 5 3) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA438 + difference 3 5) (sourceB438 + difference 5 3) sourceC438) = raw7069 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw7069; decide +kernel
    rw [ha]
    exact (canonical7069 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA438 + difference 4 0) (sourceB438 + difference 0 4) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA438 + difference 4 0) (sourceB438 + difference 0 4) sourceC438) = raw6395 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw6395; decide +kernel
    rw [ha]
    exact (canonical6395 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA438 + difference 4 1) (sourceB438 + difference 1 4) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA438 + difference 4 1) (sourceB438 + difference 1 4) sourceC438) = raw6058 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw6058; decide +kernel
    rw [ha]
    exact (canonical6058 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA438 + difference 4 2) (sourceB438 + difference 2 4) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA438 + difference 4 2) (sourceB438 + difference 2 4) sourceC438) = raw6396 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw6396; decide +kernel
    rw [ha]
    exact (canonical6396 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA438 + difference 4 3) (sourceB438 + difference 3 4) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA438 + difference 4 3) (sourceB438 + difference 3 4) sourceC438) = raw6048 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw6048; decide +kernel
    rw [ha]
    exact (canonical6048 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA438 + difference 4 5) (sourceB438 + difference 5 4) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA438 + difference 4 5) (sourceB438 + difference 5 4) sourceC438) = raw6398 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw6398; decide +kernel
    rw [ha]
    exact (canonical6398 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA438 + difference 5 0) (sourceB438 + difference 0 5) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA438 + difference 5 0) (sourceB438 + difference 0 5) sourceC438) = raw7938 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw7938; decide +kernel
    rw [ha]
    exact (canonical7938 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA438 + difference 5 1) (sourceB438 + difference 1 5) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA438 + difference 5 1) (sourceB438 + difference 1 5) sourceC438) = raw6412 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw6412; decide +kernel
    rw [ha]
    exact (canonical6412 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA438 + difference 5 2) (sourceB438 + difference 2 5) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA438 + difference 5 2) (sourceB438 + difference 2 5) sourceC438) = raw7939 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw7939; decide +kernel
    rw [ha]
    exact (canonical7939 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA438 + difference 5 3) (sourceB438 + difference 3 5) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2787) := by
    have ha : (tripleCharges (sourceA438 + difference 5 3) (sourceB438 + difference 3 5) sourceC438) = raw7675 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw7675; decide +kernel
    rw [ha]
    exact (canonical7675 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA438 + difference 5 4) (sourceB438 + difference 4 5) sourceC438) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA438 + difference 5 4) (sourceB438 + difference 4 5) sourceC438) = raw6735 := by
      apply Matrix.ext; unfold tripleCharges sourceA438 sourceB438 sourceC438 difference raw6735; decide +kernel
    rw [ha]
    exact (canonical6735 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA438 sourceB438 sourceC438
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm438, Integer.Sparse.eval]
  linarith only [hs]

def sourceA439 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB439 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC439 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceForm439 : Integer.Sparse Master := [(Sum.inr 4486, 2), (Sum.inr 4488, 1), (Sum.inr 4492, 1), (Sum.inr 4500, 1), (Sum.inr 4596, 2), (Sum.inr 4611, 1), (Sum.inr 4617, 1), (Sum.inr 5091, 2), (Sum.inr 5096, 2), (Sum.inr 5103, 2), (Sum.inr 5151, 2), (Sum.inr 5173, 2), (Sum.inr 5206, 1), (Sum.inr 5276, 1), (Sum.inr 5289, 2), (Sum.inr 5291, 1), (Sum.inr 5299, 2), (Sum.inr 5300, 1), (Sum.inr 5302, 1), (Sum.inr 5304, 1), (Sum.inr 5451, 1)]

theorem sourceEq439 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm439 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA439 + difference 0 1) (sourceB439 + difference 1 0) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA439 + difference 0 1) (sourceB439 + difference 1 0) sourceC439) = raw8070 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8070; decide +kernel
    rw [ha]
    exact (canonical8070 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA439 + difference 0 2) (sourceB439 + difference 2 0) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA439 + difference 0 2) (sourceB439 + difference 2 0) sourceC439) = raw8071 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8071; decide +kernel
    rw [ha]
    exact (canonical8071 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA439 + difference 0 3) (sourceB439 + difference 3 0) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA439 + difference 0 3) (sourceB439 + difference 3 0) sourceC439) = raw8072 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8072; decide +kernel
    rw [ha]
    exact (canonical8072 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA439 + difference 0 4) (sourceB439 + difference 4 0) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA439 + difference 0 4) (sourceB439 + difference 4 0) sourceC439) = raw8073 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8073; decide +kernel
    rw [ha]
    exact (canonical8073 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA439 + difference 0 5) (sourceB439 + difference 5 0) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA439 + difference 0 5) (sourceB439 + difference 5 0) sourceC439) = raw8074 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8074; decide +kernel
    rw [ha]
    exact (canonical8074 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA439 + difference 1 0) (sourceB439 + difference 0 1) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4596) := by
    have ha : (tripleCharges (sourceA439 + difference 1 0) (sourceB439 + difference 0 1) sourceC439) = raw8075 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8075; decide +kernel
    rw [ha]
    exact (canonical8075 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA439 + difference 1 2) (sourceB439 + difference 2 1) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5091) := by
    have ha : (tripleCharges (sourceA439 + difference 1 2) (sourceB439 + difference 2 1) sourceC439) = raw8076 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8076; decide +kernel
    rw [ha]
    exact (canonical8076 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA439 + difference 1 3) (sourceB439 + difference 3 1) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5096) := by
    have ha : (tripleCharges (sourceA439 + difference 1 3) (sourceB439 + difference 3 1) sourceC439) = raw8077 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8077; decide +kernel
    rw [ha]
    exact (canonical8077 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA439 + difference 1 4) (sourceB439 + difference 4 1) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA439 + difference 1 4) (sourceB439 + difference 4 1) sourceC439) = raw8078 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8078; decide +kernel
    rw [ha]
    exact (canonical8078 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA439 + difference 1 5) (sourceB439 + difference 5 1) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA439 + difference 1 5) (sourceB439 + difference 5 1) sourceC439) = raw8079 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8079; decide +kernel
    rw [ha]
    exact (canonical8079 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA439 + difference 2 0) (sourceB439 + difference 0 2) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4596) := by
    have ha : (tripleCharges (sourceA439 + difference 2 0) (sourceB439 + difference 0 2) sourceC439) = raw8080 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8080; decide +kernel
    rw [ha]
    exact (canonical8080 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA439 + difference 2 1) (sourceB439 + difference 1 2) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5091) := by
    have ha : (tripleCharges (sourceA439 + difference 2 1) (sourceB439 + difference 1 2) sourceC439) = raw8081 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8081; decide +kernel
    rw [ha]
    exact (canonical8081 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA439 + difference 2 3) (sourceB439 + difference 3 2) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5096) := by
    have ha : (tripleCharges (sourceA439 + difference 2 3) (sourceB439 + difference 3 2) sourceC439) = raw8082 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8082; decide +kernel
    rw [ha]
    exact (canonical8082 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA439 + difference 2 4) (sourceB439 + difference 4 2) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA439 + difference 2 4) (sourceB439 + difference 4 2) sourceC439) = raw8083 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8083; decide +kernel
    rw [ha]
    exact (canonical8083 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA439 + difference 2 5) (sourceB439 + difference 5 2) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA439 + difference 2 5) (sourceB439 + difference 5 2) sourceC439) = raw8084 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8084; decide +kernel
    rw [ha]
    exact (canonical8084 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA439 + difference 3 0) (sourceB439 + difference 0 3) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA439 + difference 3 0) (sourceB439 + difference 0 3) sourceC439) = raw8085 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8085; decide +kernel
    rw [ha]
    exact (canonical8085 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA439 + difference 3 1) (sourceB439 + difference 1 3) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA439 + difference 3 1) (sourceB439 + difference 1 3) sourceC439) = raw8086 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8086; decide +kernel
    rw [ha]
    exact (canonical8086 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA439 + difference 3 2) (sourceB439 + difference 2 3) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA439 + difference 3 2) (sourceB439 + difference 2 3) sourceC439) = raw8087 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8087; decide +kernel
    rw [ha]
    exact (canonical8087 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA439 + difference 3 4) (sourceB439 + difference 4 3) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA439 + difference 3 4) (sourceB439 + difference 4 3) sourceC439) = raw8088 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8088; decide +kernel
    rw [ha]
    exact (canonical8088 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA439 + difference 3 5) (sourceB439 + difference 5 3) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA439 + difference 3 5) (sourceB439 + difference 5 3) sourceC439) = raw8089 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8089; decide +kernel
    rw [ha]
    exact (canonical8089 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA439 + difference 4 0) (sourceB439 + difference 0 4) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA439 + difference 4 0) (sourceB439 + difference 0 4) sourceC439) = raw8090 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8090; decide +kernel
    rw [ha]
    exact (canonical8090 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA439 + difference 4 1) (sourceB439 + difference 1 4) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA439 + difference 4 1) (sourceB439 + difference 1 4) sourceC439) = raw8091 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8091; decide +kernel
    rw [ha]
    exact (canonical8091 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA439 + difference 4 2) (sourceB439 + difference 2 4) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA439 + difference 4 2) (sourceB439 + difference 2 4) sourceC439) = raw8092 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8092; decide +kernel
    rw [ha]
    exact (canonical8092 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA439 + difference 4 3) (sourceB439 + difference 3 4) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA439 + difference 4 3) (sourceB439 + difference 3 4) sourceC439) = raw8093 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8093; decide +kernel
    rw [ha]
    exact (canonical8093 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA439 + difference 4 5) (sourceB439 + difference 5 4) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA439 + difference 4 5) (sourceB439 + difference 5 4) sourceC439) = raw8094 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8094; decide +kernel
    rw [ha]
    exact (canonical8094 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA439 + difference 5 0) (sourceB439 + difference 0 5) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4488) := by
    have ha : (tripleCharges (sourceA439 + difference 5 0) (sourceB439 + difference 0 5) sourceC439) = raw8095 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8095; decide +kernel
    rw [ha]
    exact (canonical8095 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA439 + difference 5 1) (sourceB439 + difference 1 5) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4486) := by
    have ha : (tripleCharges (sourceA439 + difference 5 1) (sourceB439 + difference 1 5) sourceC439) = raw8096 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8096; decide +kernel
    rw [ha]
    exact (canonical8096 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA439 + difference 5 2) (sourceB439 + difference 2 5) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4486) := by
    have ha : (tripleCharges (sourceA439 + difference 5 2) (sourceB439 + difference 2 5) sourceC439) = raw8097 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8097; decide +kernel
    rw [ha]
    exact (canonical8097 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA439 + difference 5 3) (sourceB439 + difference 3 5) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4492) := by
    have ha : (tripleCharges (sourceA439 + difference 5 3) (sourceB439 + difference 3 5) sourceC439) = raw8098 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8098; decide +kernel
    rw [ha]
    exact (canonical8098 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA439 + difference 5 4) (sourceB439 + difference 4 5) sourceC439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA439 + difference 5 4) (sourceB439 + difference 4 5) sourceC439) = raw8099 := by
      apply Matrix.ext; unfold tripleCharges sourceA439 sourceB439 sourceC439 difference raw8099; decide +kernel
    rw [ha]
    exact (canonical8099 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA439 sourceB439 sourceC439
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm439, Integer.Sparse.eval]
  linarith only [hs]

def sourceA440 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB440 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC440 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceForm440 : Integer.Sparse Master := [(Sum.inr 1229, 2), (Sum.inr 1231, 1), (Sum.inr 1245, 1), (Sum.inr 1292, 1), (Sum.inr 1639, 2), (Sum.inr 1651, 1), (Sum.inr 1716, 1), (Sum.inr 2875, 2), (Sum.inr 2888, 1), (Sum.inr 2921, 2), (Sum.inr 2930, 2), (Sum.inr 2952, 2), (Sum.inr 3024, 2), (Sum.inr 3052, 1), (Sum.inr 3097, 2), (Sum.inr 3103, 1), (Sum.inr 3119, 1), (Sum.inr 3573, 2), (Sum.inr 3584, 1), (Sum.inr 3626, 1), (Sum.inr 3987, 1)]

theorem sourceEq440 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm440 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA440 + difference 0 1) (sourceB440 + difference 1 0) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA440 + difference 0 1) (sourceB440 + difference 1 0) sourceC440) = raw8100 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8100; decide +kernel
    rw [ha]
    exact (canonical8100 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA440 + difference 0 2) (sourceB440 + difference 2 0) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA440 + difference 0 2) (sourceB440 + difference 2 0) sourceC440) = raw8101 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8101; decide +kernel
    rw [ha]
    exact (canonical8101 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA440 + difference 0 3) (sourceB440 + difference 3 0) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA440 + difference 0 3) (sourceB440 + difference 3 0) sourceC440) = raw8102 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8102; decide +kernel
    rw [ha]
    exact (canonical8102 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA440 + difference 0 4) (sourceB440 + difference 4 0) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA440 + difference 0 4) (sourceB440 + difference 4 0) sourceC440) = raw8103 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8103; decide +kernel
    rw [ha]
    exact (canonical8103 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA440 + difference 0 5) (sourceB440 + difference 5 0) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA440 + difference 0 5) (sourceB440 + difference 5 0) sourceC440) = raw8104 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8104; decide +kernel
    rw [ha]
    exact (canonical8104 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA440 + difference 1 0) (sourceB440 + difference 0 1) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1229) := by
    have ha : (tripleCharges (sourceA440 + difference 1 0) (sourceB440 + difference 0 1) sourceC440) = raw8105 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8105; decide +kernel
    rw [ha]
    exact (canonical8105 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA440 + difference 1 2) (sourceB440 + difference 2 1) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2921) := by
    have ha : (tripleCharges (sourceA440 + difference 1 2) (sourceB440 + difference 2 1) sourceC440) = raw8106 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8106; decide +kernel
    rw [ha]
    exact (canonical8106 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA440 + difference 1 3) (sourceB440 + difference 3 1) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2875) := by
    have ha : (tripleCharges (sourceA440 + difference 1 3) (sourceB440 + difference 3 1) sourceC440) = raw8107 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8107; decide +kernel
    rw [ha]
    exact (canonical8107 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA440 + difference 1 4) (sourceB440 + difference 4 1) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA440 + difference 1 4) (sourceB440 + difference 4 1) sourceC440) = raw8108 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8108; decide +kernel
    rw [ha]
    exact (canonical8108 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA440 + difference 1 5) (sourceB440 + difference 5 1) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA440 + difference 1 5) (sourceB440 + difference 5 1) sourceC440) = raw8109 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8109; decide +kernel
    rw [ha]
    exact (canonical8109 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA440 + difference 2 0) (sourceB440 + difference 0 2) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1229) := by
    have ha : (tripleCharges (sourceA440 + difference 2 0) (sourceB440 + difference 0 2) sourceC440) = raw8110 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8110; decide +kernel
    rw [ha]
    exact (canonical8110 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA440 + difference 2 1) (sourceB440 + difference 1 2) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2921) := by
    have ha : (tripleCharges (sourceA440 + difference 2 1) (sourceB440 + difference 1 2) sourceC440) = raw8111 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8111; decide +kernel
    rw [ha]
    exact (canonical8111 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA440 + difference 2 3) (sourceB440 + difference 3 2) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2875) := by
    have ha : (tripleCharges (sourceA440 + difference 2 3) (sourceB440 + difference 3 2) sourceC440) = raw8112 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8112; decide +kernel
    rw [ha]
    exact (canonical8112 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA440 + difference 2 4) (sourceB440 + difference 4 2) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA440 + difference 2 4) (sourceB440 + difference 4 2) sourceC440) = raw8113 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8113; decide +kernel
    rw [ha]
    exact (canonical8113 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA440 + difference 2 5) (sourceB440 + difference 5 2) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA440 + difference 2 5) (sourceB440 + difference 5 2) sourceC440) = raw8114 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8114; decide +kernel
    rw [ha]
    exact (canonical8114 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA440 + difference 3 0) (sourceB440 + difference 0 3) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1292) := by
    have ha : (tripleCharges (sourceA440 + difference 3 0) (sourceB440 + difference 0 3) sourceC440) = raw8115 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8115; decide +kernel
    rw [ha]
    exact (canonical8115 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA440 + difference 3 1) (sourceB440 + difference 1 3) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA440 + difference 3 1) (sourceB440 + difference 1 3) sourceC440) = raw8116 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8116; decide +kernel
    rw [ha]
    exact (canonical8116 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA440 + difference 3 2) (sourceB440 + difference 2 3) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA440 + difference 3 2) (sourceB440 + difference 2 3) sourceC440) = raw8117 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8117; decide +kernel
    rw [ha]
    exact (canonical8117 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA440 + difference 3 4) (sourceB440 + difference 4 3) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA440 + difference 3 4) (sourceB440 + difference 4 3) sourceC440) = raw8118 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8118; decide +kernel
    rw [ha]
    exact (canonical8118 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA440 + difference 3 5) (sourceB440 + difference 5 3) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA440 + difference 3 5) (sourceB440 + difference 5 3) sourceC440) = raw8119 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8119; decide +kernel
    rw [ha]
    exact (canonical8119 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA440 + difference 4 0) (sourceB440 + difference 0 4) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA440 + difference 4 0) (sourceB440 + difference 0 4) sourceC440) = raw8120 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8120; decide +kernel
    rw [ha]
    exact (canonical8120 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA440 + difference 4 1) (sourceB440 + difference 1 4) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA440 + difference 4 1) (sourceB440 + difference 1 4) sourceC440) = raw8121 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8121; decide +kernel
    rw [ha]
    exact (canonical8121 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA440 + difference 4 2) (sourceB440 + difference 2 4) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA440 + difference 4 2) (sourceB440 + difference 2 4) sourceC440) = raw8122 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8122; decide +kernel
    rw [ha]
    exact (canonical8122 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA440 + difference 4 3) (sourceB440 + difference 3 4) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2888) := by
    have ha : (tripleCharges (sourceA440 + difference 4 3) (sourceB440 + difference 3 4) sourceC440) = raw8123 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8123; decide +kernel
    rw [ha]
    exact (canonical8123 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA440 + difference 4 5) (sourceB440 + difference 5 4) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA440 + difference 4 5) (sourceB440 + difference 5 4) sourceC440) = raw8124 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8124; decide +kernel
    rw [ha]
    exact (canonical8124 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA440 + difference 5 0) (sourceB440 + difference 0 5) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1231) := by
    have ha : (tripleCharges (sourceA440 + difference 5 0) (sourceB440 + difference 0 5) sourceC440) = raw8125 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8125; decide +kernel
    rw [ha]
    exact (canonical8125 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA440 + difference 5 1) (sourceB440 + difference 1 5) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1639) := by
    have ha : (tripleCharges (sourceA440 + difference 5 1) (sourceB440 + difference 1 5) sourceC440) = raw8126 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8126; decide +kernel
    rw [ha]
    exact (canonical8126 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA440 + difference 5 2) (sourceB440 + difference 2 5) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1639) := by
    have ha : (tripleCharges (sourceA440 + difference 5 2) (sourceB440 + difference 2 5) sourceC440) = raw8127 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8127; decide +kernel
    rw [ha]
    exact (canonical8127 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA440 + difference 5 3) (sourceB440 + difference 3 5) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1651) := by
    have ha : (tripleCharges (sourceA440 + difference 5 3) (sourceB440 + difference 3 5) sourceC440) = raw8128 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8128; decide +kernel
    rw [ha]
    exact (canonical8128 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA440 + difference 5 4) (sourceB440 + difference 4 5) sourceC440) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA440 + difference 5 4) (sourceB440 + difference 4 5) sourceC440) = raw8129 := by
      apply Matrix.ext; unfold tripleCharges sourceA440 sourceB440 sourceC440 difference raw8129; decide +kernel
    rw [ha]
    exact (canonical8129 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA440 sourceB440 sourceC440
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm440, Integer.Sparse.eval]
  linarith only [hs]

def sourceA441 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB441 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC441 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceForm441 : Integer.Sparse Master := [(Sum.inr 1070, 2), (Sum.inr 1072, 1), (Sum.inr 1076, 1), (Sum.inr 1084, 1), (Sum.inr 2500, 2), (Sum.inr 2502, 2), (Sum.inr 2506, 2), (Sum.inr 2513, 2), (Sum.inr 2681, 2), (Sum.inr 2683, 1), (Sum.inr 2687, 1), (Sum.inr 2735, 2), (Sum.inr 2737, 1), (Sum.inr 2744, 1), (Sum.inr 2773, 2), (Sum.inr 2774, 1), (Sum.inr 2776, 1), (Sum.inr 3572, 2), (Sum.inr 3582, 1), (Sum.inr 3583, 1), (Sum.inr 3888, 1)]

theorem sourceEq441 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm441 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA441 + difference 0 1) (sourceB441 + difference 1 0) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA441 + difference 0 1) (sourceB441 + difference 1 0) sourceC441) = raw8130 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8130; decide +kernel
    rw [ha]
    exact (canonical8130 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA441 + difference 0 2) (sourceB441 + difference 2 0) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA441 + difference 0 2) (sourceB441 + difference 2 0) sourceC441) = raw8131 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8131; decide +kernel
    rw [ha]
    exact (canonical8131 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA441 + difference 0 3) (sourceB441 + difference 3 0) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA441 + difference 0 3) (sourceB441 + difference 3 0) sourceC441) = raw8132 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8132; decide +kernel
    rw [ha]
    exact (canonical8132 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA441 + difference 0 4) (sourceB441 + difference 4 0) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA441 + difference 0 4) (sourceB441 + difference 4 0) sourceC441) = raw8133 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8133; decide +kernel
    rw [ha]
    exact (canonical8133 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA441 + difference 0 5) (sourceB441 + difference 5 0) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA441 + difference 0 5) (sourceB441 + difference 5 0) sourceC441) = raw8134 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8134; decide +kernel
    rw [ha]
    exact (canonical8134 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA441 + difference 1 0) (sourceB441 + difference 0 1) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2502) := by
    have ha : (tripleCharges (sourceA441 + difference 1 0) (sourceB441 + difference 0 1) sourceC441) = raw8135 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8135; decide +kernel
    rw [ha]
    exact (canonical8135 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA441 + difference 1 2) (sourceB441 + difference 2 1) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2500) := by
    have ha : (tripleCharges (sourceA441 + difference 1 2) (sourceB441 + difference 2 1) sourceC441) = raw8136 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8136; decide +kernel
    rw [ha]
    exact (canonical8136 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA441 + difference 1 3) (sourceB441 + difference 3 1) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2506) := by
    have ha : (tripleCharges (sourceA441 + difference 1 3) (sourceB441 + difference 3 1) sourceC441) = raw8137 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8137; decide +kernel
    rw [ha]
    exact (canonical8137 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA441 + difference 1 4) (sourceB441 + difference 4 1) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA441 + difference 1 4) (sourceB441 + difference 4 1) sourceC441) = raw8138 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8138; decide +kernel
    rw [ha]
    exact (canonical8138 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA441 + difference 1 5) (sourceB441 + difference 5 1) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA441 + difference 1 5) (sourceB441 + difference 5 1) sourceC441) = raw8139 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8139; decide +kernel
    rw [ha]
    exact (canonical8139 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA441 + difference 2 0) (sourceB441 + difference 0 2) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2502) := by
    have ha : (tripleCharges (sourceA441 + difference 2 0) (sourceB441 + difference 0 2) sourceC441) = raw8140 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8140; decide +kernel
    rw [ha]
    exact (canonical8140 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA441 + difference 2 1) (sourceB441 + difference 1 2) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2500) := by
    have ha : (tripleCharges (sourceA441 + difference 2 1) (sourceB441 + difference 1 2) sourceC441) = raw8141 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8141; decide +kernel
    rw [ha]
    exact (canonical8141 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA441 + difference 2 3) (sourceB441 + difference 3 2) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2506) := by
    have ha : (tripleCharges (sourceA441 + difference 2 3) (sourceB441 + difference 3 2) sourceC441) = raw8142 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8142; decide +kernel
    rw [ha]
    exact (canonical8142 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA441 + difference 2 4) (sourceB441 + difference 4 2) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA441 + difference 2 4) (sourceB441 + difference 4 2) sourceC441) = raw8143 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8143; decide +kernel
    rw [ha]
    exact (canonical8143 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA441 + difference 2 5) (sourceB441 + difference 5 2) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA441 + difference 2 5) (sourceB441 + difference 5 2) sourceC441) = raw8144 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8144; decide +kernel
    rw [ha]
    exact (canonical8144 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA441 + difference 3 0) (sourceB441 + difference 0 3) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA441 + difference 3 0) (sourceB441 + difference 0 3) sourceC441) = raw8145 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8145; decide +kernel
    rw [ha]
    exact (canonical8145 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA441 + difference 3 1) (sourceB441 + difference 1 3) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA441 + difference 3 1) (sourceB441 + difference 1 3) sourceC441) = raw8146 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8146; decide +kernel
    rw [ha]
    exact (canonical8146 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA441 + difference 3 2) (sourceB441 + difference 2 3) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA441 + difference 3 2) (sourceB441 + difference 2 3) sourceC441) = raw8147 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8147; decide +kernel
    rw [ha]
    exact (canonical8147 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA441 + difference 3 4) (sourceB441 + difference 4 3) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA441 + difference 3 4) (sourceB441 + difference 4 3) sourceC441) = raw8148 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8148; decide +kernel
    rw [ha]
    exact (canonical8148 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA441 + difference 3 5) (sourceB441 + difference 5 3) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA441 + difference 3 5) (sourceB441 + difference 5 3) sourceC441) = raw8149 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8149; decide +kernel
    rw [ha]
    exact (canonical8149 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA441 + difference 4 0) (sourceB441 + difference 0 4) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA441 + difference 4 0) (sourceB441 + difference 0 4) sourceC441) = raw8150 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8150; decide +kernel
    rw [ha]
    exact (canonical8150 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA441 + difference 4 1) (sourceB441 + difference 1 4) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA441 + difference 4 1) (sourceB441 + difference 1 4) sourceC441) = raw8151 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8151; decide +kernel
    rw [ha]
    exact (canonical8151 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA441 + difference 4 2) (sourceB441 + difference 2 4) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA441 + difference 4 2) (sourceB441 + difference 2 4) sourceC441) = raw8152 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8152; decide +kernel
    rw [ha]
    exact (canonical8152 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA441 + difference 4 3) (sourceB441 + difference 3 4) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA441 + difference 4 3) (sourceB441 + difference 3 4) sourceC441) = raw8153 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8153; decide +kernel
    rw [ha]
    exact (canonical8153 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA441 + difference 4 5) (sourceB441 + difference 5 4) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA441 + difference 4 5) (sourceB441 + difference 5 4) sourceC441) = raw8154 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8154; decide +kernel
    rw [ha]
    exact (canonical8154 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA441 + difference 5 0) (sourceB441 + difference 0 5) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1072) := by
    have ha : (tripleCharges (sourceA441 + difference 5 0) (sourceB441 + difference 0 5) sourceC441) = raw8155 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8155; decide +kernel
    rw [ha]
    exact (canonical8155 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA441 + difference 5 1) (sourceB441 + difference 1 5) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1070) := by
    have ha : (tripleCharges (sourceA441 + difference 5 1) (sourceB441 + difference 1 5) sourceC441) = raw8156 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8156; decide +kernel
    rw [ha]
    exact (canonical8156 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA441 + difference 5 2) (sourceB441 + difference 2 5) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1070) := by
    have ha : (tripleCharges (sourceA441 + difference 5 2) (sourceB441 + difference 2 5) sourceC441) = raw8157 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8157; decide +kernel
    rw [ha]
    exact (canonical8157 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA441 + difference 5 3) (sourceB441 + difference 3 5) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1076) := by
    have ha : (tripleCharges (sourceA441 + difference 5 3) (sourceB441 + difference 3 5) sourceC441) = raw8158 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8158; decide +kernel
    rw [ha]
    exact (canonical8158 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA441 + difference 5 4) (sourceB441 + difference 4 5) sourceC441) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1084) := by
    have ha : (tripleCharges (sourceA441 + difference 5 4) (sourceB441 + difference 4 5) sourceC441) = raw8159 := by
      apply Matrix.ext; unfold tripleCharges sourceA441 sourceB441 sourceC441 difference raw8159; decide +kernel
    rw [ha]
    exact (canonical8159 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA441 sourceB441 sourceC441
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm441, Integer.Sparse.eval]
  linarith only [hs]

def sourceA442 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB442 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC442 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceForm442 : Integer.Sparse Master := [(Sum.inr 2769, 1), (Sum.inr 3051, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

theorem sourceEq442 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm442 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA442 + difference 0 0) (sourceB442 + difference 0 0) sourceC442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA442 + difference 0 0) (sourceB442 + difference 0 0) sourceC442) = raw8160 := by
      apply Matrix.ext; unfold tripleCharges sourceA442 sourceB442 sourceC442 difference raw8160; decide +kernel
    rw [ha]
    exact (canonical8160 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA442 + difference 0 1) (sourceB442 + difference 1 0) sourceC442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA442 + difference 0 1) (sourceB442 + difference 1 0) sourceC442) = raw8161 := by
      apply Matrix.ext; unfold tripleCharges sourceA442 sourceB442 sourceC442 difference raw8161; decide +kernel
    rw [ha]
    exact (canonical8161 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA442 + difference 0 2) (sourceB442 + difference 2 0) sourceC442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA442 + difference 0 2) (sourceB442 + difference 2 0) sourceC442) = raw8162 := by
      apply Matrix.ext; unfold tripleCharges sourceA442 sourceB442 sourceC442 difference raw8162; decide +kernel
    rw [ha]
    exact (canonical8162 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA442 + difference 0 3) (sourceB442 + difference 3 0) sourceC442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA442 + difference 0 3) (sourceB442 + difference 3 0) sourceC442) = raw8163 := by
      apply Matrix.ext; unfold tripleCharges sourceA442 sourceB442 sourceC442 difference raw8163; decide +kernel
    rw [ha]
    exact (canonical8163 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA442 + difference 0 4) (sourceB442 + difference 4 0) sourceC442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA442 + difference 0 4) (sourceB442 + difference 4 0) sourceC442) = raw8164 := by
      apply Matrix.ext; unfold tripleCharges sourceA442 sourceB442 sourceC442 difference raw8164; decide +kernel
    rw [ha]
    exact (canonical8164 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA442 + difference 0 5) (sourceB442 + difference 5 0) sourceC442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA442 + difference 0 5) (sourceB442 + difference 5 0) sourceC442) = raw8165 := by
      apply Matrix.ext; unfold tripleCharges sourceA442 sourceB442 sourceC442 difference raw8165; decide +kernel
    rw [ha]
    exact (canonical8165 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA442 + sourceB442) sourceC442) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA442 + sourceB442) sourceC442) = raw8166 := by
      apply Matrix.ext; unfold doubleCharges sourceA442 sourceB442 sourceC442 raw8166; decide +kernel
    rw [ha]
    exact (canonical8166 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA442 sourceB442 sourceC442
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm442, Integer.Sparse.eval]
  linarith only [hs]

def sourceA443 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB443 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC443 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceForm443 : Integer.Sparse Master := [(Sum.inr 1268, 2), (Sum.inr 1272, 1), (Sum.inr 1273, 1), (Sum.inr 1306, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

theorem sourceEq443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm443 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA443 + difference 0 0) (sourceB443 + difference 0 0) sourceC443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA443 + difference 0 0) (sourceB443 + difference 0 0) sourceC443) = raw8160 := by
      apply Matrix.ext; unfold tripleCharges sourceA443 sourceB443 sourceC443 difference raw8160; decide +kernel
    rw [ha]
    exact (canonical8160 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA443 + difference 1 0) (sourceB443 + difference 0 1) sourceC443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1268) := by
    have ha : (tripleCharges (sourceA443 + difference 1 0) (sourceB443 + difference 0 1) sourceC443) = raw8167 := by
      apply Matrix.ext; unfold tripleCharges sourceA443 sourceB443 sourceC443 difference raw8167; decide +kernel
    rw [ha]
    exact (canonical8167 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA443 + difference 2 0) (sourceB443 + difference 0 2) sourceC443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1268) := by
    have ha : (tripleCharges (sourceA443 + difference 2 0) (sourceB443 + difference 0 2) sourceC443) = raw8168 := by
      apply Matrix.ext; unfold tripleCharges sourceA443 sourceB443 sourceC443 difference raw8168; decide +kernel
    rw [ha]
    exact (canonical8168 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA443 + difference 3 0) (sourceB443 + difference 0 3) sourceC443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA443 + difference 3 0) (sourceB443 + difference 0 3) sourceC443) = raw8169 := by
      apply Matrix.ext; unfold tripleCharges sourceA443 sourceB443 sourceC443 difference raw8169; decide +kernel
    rw [ha]
    exact (canonical8169 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA443 + difference 4 0) (sourceB443 + difference 0 4) sourceC443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA443 + difference 4 0) (sourceB443 + difference 0 4) sourceC443) = raw8170 := by
      apply Matrix.ext; unfold tripleCharges sourceA443 sourceB443 sourceC443 difference raw8170; decide +kernel
    rw [ha]
    exact (canonical8170 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA443 + difference 5 0) (sourceB443 + difference 0 5) sourceC443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1272) := by
    have ha : (tripleCharges (sourceA443 + difference 5 0) (sourceB443 + difference 0 5) sourceC443) = raw8171 := by
      apply Matrix.ext; unfold tripleCharges sourceA443 sourceB443 sourceC443 difference raw8171; decide +kernel
    rw [ha]
    exact (canonical8171 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA443 + sourceB443) sourceC443) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA443 + sourceB443) sourceC443) = raw8166 := by
      apply Matrix.ext; unfold doubleCharges sourceA443 sourceB443 sourceC443 raw8166; decide +kernel
    rw [ha]
    exact (canonical8166 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA443 sourceB443 sourceC443
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm443, Integer.Sparse.eval]
  linarith only [hs]

def sourceA444 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB444 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC444 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceForm444 : Integer.Sparse Master := [(Sum.inr 1268, 1), (Sum.inr 2571, 1), (Sum.inr 2639, 1), (Sum.inr 2759, 1), (Sum.inr 2763, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

theorem sourceEq444 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm444 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA444 + difference 1 0) (sourceB444 + difference 0 1) sourceC444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1268) := by
    have ha : (tripleCharges (sourceA444 + difference 1 0) (sourceB444 + difference 0 1) sourceC444) = raw8167 := by
      apply Matrix.ext; unfold tripleCharges sourceA444 sourceB444 sourceC444 difference raw8167; decide +kernel
    rw [ha]
    exact (canonical8167 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA444 + difference 1 1) (sourceB444 + difference 1 1) sourceC444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA444 + difference 1 1) (sourceB444 + difference 1 1) sourceC444) = raw8160 := by
      apply Matrix.ext; unfold tripleCharges sourceA444 sourceB444 sourceC444 difference raw8160; decide +kernel
    rw [ha]
    exact (canonical8160 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA444 + difference 1 2) (sourceB444 + difference 2 1) sourceC444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2571) := by
    have ha : (tripleCharges (sourceA444 + difference 1 2) (sourceB444 + difference 2 1) sourceC444) = raw8172 := by
      apply Matrix.ext; unfold tripleCharges sourceA444 sourceB444 sourceC444 difference raw8172; decide +kernel
    rw [ha]
    exact (canonical8172 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA444 + difference 1 3) (sourceB444 + difference 3 1) sourceC444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2639) := by
    have ha : (tripleCharges (sourceA444 + difference 1 3) (sourceB444 + difference 3 1) sourceC444) = raw8173 := by
      apply Matrix.ext; unfold tripleCharges sourceA444 sourceB444 sourceC444 difference raw8173; decide +kernel
    rw [ha]
    exact (canonical8173 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA444 + difference 1 4) (sourceB444 + difference 4 1) sourceC444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA444 + difference 1 4) (sourceB444 + difference 4 1) sourceC444) = raw8174 := by
      apply Matrix.ext; unfold tripleCharges sourceA444 sourceB444 sourceC444 difference raw8174; decide +kernel
    rw [ha]
    exact (canonical8174 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA444 + difference 1 5) (sourceB444 + difference 5 1) sourceC444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA444 + difference 1 5) (sourceB444 + difference 5 1) sourceC444) = raw8175 := by
      apply Matrix.ext; unfold tripleCharges sourceA444 sourceB444 sourceC444 difference raw8175; decide +kernel
    rw [ha]
    exact (canonical8175 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA444 + sourceB444) sourceC444) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA444 + sourceB444) sourceC444) = raw8166 := by
      apply Matrix.ext; unfold doubleCharges sourceA444 sourceB444 sourceC444 raw8166; decide +kernel
    rw [ha]
    exact (canonical8166 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA444 sourceB444 sourceC444
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm444, Integer.Sparse.eval]
  linarith only [hs]

def sourceA445 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB445 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC445 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceForm445 : Integer.Sparse Master := [(Sum.inr 1433, 1), (Sum.inr 2571, 1), (Sum.inr 2575, 1), (Sum.inr 2600, 1), (Sum.inr 2769, 1), (Sum.inr 3051, 1), (Sum.inr 4092, -1)]

theorem sourceEq445 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm445 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA445 + difference 0 1) (sourceB445 + difference 1 0) sourceC445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA445 + difference 0 1) (sourceB445 + difference 1 0) sourceC445) = raw8161 := by
      apply Matrix.ext; unfold tripleCharges sourceA445 sourceB445 sourceC445 difference raw8161; decide +kernel
    rw [ha]
    exact (canonical8161 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA445 + difference 1 1) (sourceB445 + difference 1 1) sourceC445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA445 + difference 1 1) (sourceB445 + difference 1 1) sourceC445) = raw8160 := by
      apply Matrix.ext; unfold tripleCharges sourceA445 sourceB445 sourceC445 difference raw8160; decide +kernel
    rw [ha]
    exact (canonical8160 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA445 + difference 2 1) (sourceB445 + difference 1 2) sourceC445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2571) := by
    have ha : (tripleCharges (sourceA445 + difference 2 1) (sourceB445 + difference 1 2) sourceC445) = raw8176 := by
      apply Matrix.ext; unfold tripleCharges sourceA445 sourceB445 sourceC445 difference raw8176; decide +kernel
    rw [ha]
    exact (canonical8176 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA445 + difference 3 1) (sourceB445 + difference 1 3) sourceC445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2600) := by
    have ha : (tripleCharges (sourceA445 + difference 3 1) (sourceB445 + difference 1 3) sourceC445) = raw8177 := by
      apply Matrix.ext; unfold tripleCharges sourceA445 sourceB445 sourceC445 difference raw8177; decide +kernel
    rw [ha]
    exact (canonical8177 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA445 + difference 4 1) (sourceB445 + difference 1 4) sourceC445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2575) := by
    have ha : (tripleCharges (sourceA445 + difference 4 1) (sourceB445 + difference 1 4) sourceC445) = raw8178 := by
      apply Matrix.ext; unfold tripleCharges sourceA445 sourceB445 sourceC445 difference raw8178; decide +kernel
    rw [ha]
    exact (canonical8178 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA445 + difference 5 1) (sourceB445 + difference 1 5) sourceC445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1433) := by
    have ha : (tripleCharges (sourceA445 + difference 5 1) (sourceB445 + difference 1 5) sourceC445) = raw8179 := by
      apply Matrix.ext; unfold tripleCharges sourceA445 sourceB445 sourceC445 difference raw8179; decide +kernel
    rw [ha]
    exact (canonical8179 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA445 + sourceB445) sourceC445) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA445 + sourceB445) sourceC445) = raw8166 := by
      apply Matrix.ext; unfold doubleCharges sourceA445 sourceB445 sourceC445 raw8166; decide +kernel
    rw [ha]
    exact (canonical8166 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA445 sourceB445 sourceC445
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm445, Integer.Sparse.eval]
  linarith only [hs]

def sourceA446 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB446 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC446 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceForm446 : Integer.Sparse Master := [(Sum.inr 1437, 1), (Sum.inr 2639, 2), (Sum.inr 2643, 1), (Sum.inr 2769, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

theorem sourceEq446 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm446 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA446 + difference 0 3) (sourceB446 + difference 3 0) sourceC446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA446 + difference 0 3) (sourceB446 + difference 3 0) sourceC446) = raw8163 := by
      apply Matrix.ext; unfold tripleCharges sourceA446 sourceB446 sourceC446 difference raw8163; decide +kernel
    rw [ha]
    exact (canonical8163 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA446 + difference 1 3) (sourceB446 + difference 3 1) sourceC446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2639) := by
    have ha : (tripleCharges (sourceA446 + difference 1 3) (sourceB446 + difference 3 1) sourceC446) = raw8173 := by
      apply Matrix.ext; unfold tripleCharges sourceA446 sourceB446 sourceC446 difference raw8173; decide +kernel
    rw [ha]
    exact (canonical8173 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA446 + difference 2 3) (sourceB446 + difference 3 2) sourceC446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2639) := by
    have ha : (tripleCharges (sourceA446 + difference 2 3) (sourceB446 + difference 3 2) sourceC446) = raw8180 := by
      apply Matrix.ext; unfold tripleCharges sourceA446 sourceB446 sourceC446 difference raw8180; decide +kernel
    rw [ha]
    exact (canonical8180 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA446 + difference 3 3) (sourceB446 + difference 3 3) sourceC446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA446 + difference 3 3) (sourceB446 + difference 3 3) sourceC446) = raw8160 := by
      apply Matrix.ext; unfold tripleCharges sourceA446 sourceB446 sourceC446 difference raw8160; decide +kernel
    rw [ha]
    exact (canonical8160 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA446 + difference 4 3) (sourceB446 + difference 3 4) sourceC446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2643) := by
    have ha : (tripleCharges (sourceA446 + difference 4 3) (sourceB446 + difference 3 4) sourceC446) = raw8181 := by
      apply Matrix.ext; unfold tripleCharges sourceA446 sourceB446 sourceC446 difference raw8181; decide +kernel
    rw [ha]
    exact (canonical8181 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA446 + difference 5 3) (sourceB446 + difference 3 5) sourceC446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1437) := by
    have ha : (tripleCharges (sourceA446 + difference 5 3) (sourceB446 + difference 3 5) sourceC446) = raw8182 := by
      apply Matrix.ext; unfold tripleCharges sourceA446 sourceB446 sourceC446 difference raw8182; decide +kernel
    rw [ha]
    exact (canonical8182 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA446 + sourceB446) sourceC446) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA446 + sourceB446) sourceC446) = raw8166 := by
      apply Matrix.ext; unfold doubleCharges sourceA446 sourceB446 sourceC446 raw8166; decide +kernel
    rw [ha]
    exact (canonical8166 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA446 sourceB446 sourceC446
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm446, Integer.Sparse.eval]
  linarith only [hs]

def sourceA447 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB447 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC447 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceForm447 : Integer.Sparse Master := [(Sum.inr 1273, 1), (Sum.inr 2575, 2), (Sum.inr 2643, 1), (Sum.inr 2765, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

theorem sourceEq447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm447 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA447 + difference 4 0) (sourceB447 + difference 0 4) sourceC447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA447 + difference 4 0) (sourceB447 + difference 0 4) sourceC447) = raw8170 := by
      apply Matrix.ext; unfold tripleCharges sourceA447 sourceB447 sourceC447 difference raw8170; decide +kernel
    rw [ha]
    exact (canonical8170 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA447 + difference 4 1) (sourceB447 + difference 1 4) sourceC447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2575) := by
    have ha : (tripleCharges (sourceA447 + difference 4 1) (sourceB447 + difference 1 4) sourceC447) = raw8178 := by
      apply Matrix.ext; unfold tripleCharges sourceA447 sourceB447 sourceC447 difference raw8178; decide +kernel
    rw [ha]
    exact (canonical8178 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA447 + difference 4 2) (sourceB447 + difference 2 4) sourceC447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2575) := by
    have ha : (tripleCharges (sourceA447 + difference 4 2) (sourceB447 + difference 2 4) sourceC447) = raw8183 := by
      apply Matrix.ext; unfold tripleCharges sourceA447 sourceB447 sourceC447 difference raw8183; decide +kernel
    rw [ha]
    exact (canonical8183 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA447 + difference 4 3) (sourceB447 + difference 3 4) sourceC447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2643) := by
    have ha : (tripleCharges (sourceA447 + difference 4 3) (sourceB447 + difference 3 4) sourceC447) = raw8181 := by
      apply Matrix.ext; unfold tripleCharges sourceA447 sourceB447 sourceC447 difference raw8181; decide +kernel
    rw [ha]
    exact (canonical8181 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA447 + difference 4 4) (sourceB447 + difference 4 4) sourceC447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA447 + difference 4 4) (sourceB447 + difference 4 4) sourceC447) = raw8160 := by
      apply Matrix.ext; unfold tripleCharges sourceA447 sourceB447 sourceC447 difference raw8160; decide +kernel
    rw [ha]
    exact (canonical8160 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA447 + difference 4 5) (sourceB447 + difference 5 4) sourceC447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA447 + difference 4 5) (sourceB447 + difference 5 4) sourceC447) = raw8184 := by
      apply Matrix.ext; unfold tripleCharges sourceA447 sourceB447 sourceC447 difference raw8184; decide +kernel
    rw [ha]
    exact (canonical8184 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA447 + sourceB447) sourceC447) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA447 + sourceB447) sourceC447) = raw8166 := by
      apply Matrix.ext; unfold doubleCharges sourceA447 sourceB447 sourceC447 raw8166; decide +kernel
    rw [ha]
    exact (canonical8166 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA447 sourceB447 sourceC447
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm447, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
