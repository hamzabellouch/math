import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical27

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA0 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB0 : Charge := ![0, 0, 0, 0, 2, -2]
def sourceC0 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm0 : Integer.Sparse Master := [(Sum.inr 4898, 3), (Sum.inr 4899, 2), (Sum.inr 5302, 6), (Sum.inr 5310, 2), (Sum.inr 5412, 6), (Sum.inr 5443, 6), (Sum.inr 5453, 3), (Sum.inr 5455, 2)]

theorem sourceEq0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm0 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA0 + difference 0 1) (sourceB0 + difference 1 0) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA0 + difference 0 1) (sourceB0 + difference 1 0) sourceC0) = raw2631 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2631; decide +kernel
    rw [ha]
    exact (canonical2631 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA0 + difference 0 2) (sourceB0 + difference 2 0) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA0 + difference 0 2) (sourceB0 + difference 2 0) sourceC0) = raw2632 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2632; decide +kernel
    rw [ha]
    exact (canonical2632 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA0 + difference 0 3) (sourceB0 + difference 3 0) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA0 + difference 0 3) (sourceB0 + difference 3 0) sourceC0) = raw2633 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2633; decide +kernel
    rw [ha]
    exact (canonical2633 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA0 + difference 0 4) (sourceB0 + difference 4 0) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA0 + difference 0 4) (sourceB0 + difference 4 0) sourceC0) = raw2634 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2634; decide +kernel
    rw [ha]
    exact (canonical2634 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA0 + difference 0 5) (sourceB0 + difference 5 0) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA0 + difference 0 5) (sourceB0 + difference 5 0) sourceC0) = raw2635 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2635; decide +kernel
    rw [ha]
    exact (canonical2635 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA0 + difference 1 0) (sourceB0 + difference 0 1) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA0 + difference 1 0) (sourceB0 + difference 0 1) sourceC0) = raw2636 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2636; decide +kernel
    rw [ha]
    exact (canonical2636 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA0 + difference 1 2) (sourceB0 + difference 2 1) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA0 + difference 1 2) (sourceB0 + difference 2 1) sourceC0) = raw2637 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2637; decide +kernel
    rw [ha]
    exact (canonical2637 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA0 + difference 1 3) (sourceB0 + difference 3 1) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA0 + difference 1 3) (sourceB0 + difference 3 1) sourceC0) = raw2638 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2638; decide +kernel
    rw [ha]
    exact (canonical2638 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA0 + difference 1 4) (sourceB0 + difference 4 1) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA0 + difference 1 4) (sourceB0 + difference 4 1) sourceC0) = raw2639 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2639; decide +kernel
    rw [ha]
    exact (canonical2639 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA0 + difference 1 5) (sourceB0 + difference 5 1) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA0 + difference 1 5) (sourceB0 + difference 5 1) sourceC0) = raw2640 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2640; decide +kernel
    rw [ha]
    exact (canonical2640 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA0 + difference 2 0) (sourceB0 + difference 0 2) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA0 + difference 2 0) (sourceB0 + difference 0 2) sourceC0) = raw2641 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2641; decide +kernel
    rw [ha]
    exact (canonical2641 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA0 + difference 2 1) (sourceB0 + difference 1 2) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA0 + difference 2 1) (sourceB0 + difference 1 2) sourceC0) = raw2642 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2642; decide +kernel
    rw [ha]
    exact (canonical2642 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA0 + difference 2 3) (sourceB0 + difference 3 2) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA0 + difference 2 3) (sourceB0 + difference 3 2) sourceC0) = raw2643 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2643; decide +kernel
    rw [ha]
    exact (canonical2643 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA0 + difference 2 4) (sourceB0 + difference 4 2) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA0 + difference 2 4) (sourceB0 + difference 4 2) sourceC0) = raw2644 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2644; decide +kernel
    rw [ha]
    exact (canonical2644 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA0 + difference 2 5) (sourceB0 + difference 5 2) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA0 + difference 2 5) (sourceB0 + difference 5 2) sourceC0) = raw2645 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2645; decide +kernel
    rw [ha]
    exact (canonical2645 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA0 + difference 3 0) (sourceB0 + difference 0 3) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA0 + difference 3 0) (sourceB0 + difference 0 3) sourceC0) = raw2646 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2646; decide +kernel
    rw [ha]
    exact (canonical2646 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA0 + difference 3 1) (sourceB0 + difference 1 3) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA0 + difference 3 1) (sourceB0 + difference 1 3) sourceC0) = raw2647 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2647; decide +kernel
    rw [ha]
    exact (canonical2647 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA0 + difference 3 2) (sourceB0 + difference 2 3) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA0 + difference 3 2) (sourceB0 + difference 2 3) sourceC0) = raw2648 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2648; decide +kernel
    rw [ha]
    exact (canonical2648 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA0 + difference 3 4) (sourceB0 + difference 4 3) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA0 + difference 3 4) (sourceB0 + difference 4 3) sourceC0) = raw2649 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2649; decide +kernel
    rw [ha]
    exact (canonical2649 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA0 + difference 3 5) (sourceB0 + difference 5 3) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA0 + difference 3 5) (sourceB0 + difference 5 3) sourceC0) = raw2650 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2650; decide +kernel
    rw [ha]
    exact (canonical2650 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA0 + difference 4 0) (sourceB0 + difference 0 4) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA0 + difference 4 0) (sourceB0 + difference 0 4) sourceC0) = raw2651 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2651; decide +kernel
    rw [ha]
    exact (canonical2651 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA0 + difference 4 1) (sourceB0 + difference 1 4) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA0 + difference 4 1) (sourceB0 + difference 1 4) sourceC0) = raw2652 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2652; decide +kernel
    rw [ha]
    exact (canonical2652 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA0 + difference 4 2) (sourceB0 + difference 2 4) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA0 + difference 4 2) (sourceB0 + difference 2 4) sourceC0) = raw2653 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2653; decide +kernel
    rw [ha]
    exact (canonical2653 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA0 + difference 4 3) (sourceB0 + difference 3 4) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA0 + difference 4 3) (sourceB0 + difference 3 4) sourceC0) = raw2654 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2654; decide +kernel
    rw [ha]
    exact (canonical2654 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA0 + difference 4 5) (sourceB0 + difference 5 4) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA0 + difference 4 5) (sourceB0 + difference 5 4) sourceC0) = raw2655 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2655; decide +kernel
    rw [ha]
    exact (canonical2655 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA0 + difference 5 0) (sourceB0 + difference 0 5) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA0 + difference 5 0) (sourceB0 + difference 0 5) sourceC0) = raw2656 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2656; decide +kernel
    rw [ha]
    exact (canonical2656 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA0 + difference 5 1) (sourceB0 + difference 1 5) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA0 + difference 5 1) (sourceB0 + difference 1 5) sourceC0) = raw2657 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2657; decide +kernel
    rw [ha]
    exact (canonical2657 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA0 + difference 5 2) (sourceB0 + difference 2 5) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA0 + difference 5 2) (sourceB0 + difference 2 5) sourceC0) = raw2658 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2658; decide +kernel
    rw [ha]
    exact (canonical2658 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA0 + difference 5 3) (sourceB0 + difference 3 5) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA0 + difference 5 3) (sourceB0 + difference 3 5) sourceC0) = raw2659 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2659; decide +kernel
    rw [ha]
    exact (canonical2659 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA0 + difference 5 4) (sourceB0 + difference 4 5) sourceC0) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA0 + difference 5 4) (sourceB0 + difference 4 5) sourceC0) = raw2660 := by
      apply Matrix.ext; unfold tripleCharges sourceA0 sourceB0 sourceC0 difference raw2660; decide +kernel
    rw [ha]
    exact (canonical2660 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA0 sourceB0 sourceC0
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm0, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB1 : Charge := ![0, 0, 0, 1, 1, -2]
def sourceC1 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm1 : Integer.Sparse Master := [(Sum.inr 4889, 2), (Sum.inr 4890, 1), (Sum.inr 4896, 2), (Sum.inr 5284, 2), (Sum.inr 5294, 2), (Sum.inr 5406, 2), (Sum.inr 5411, 4), (Sum.inr 5435, 4), (Sum.inr 5443, 2), (Sum.inr 5450, 2), (Sum.inr 5451, 2), (Sum.inr 5452, 2), (Sum.inr 5454, 2), (Sum.inr 5493, 1)]

theorem sourceEq1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1 + difference 0 1) (sourceB1 + difference 1 0) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1 + difference 0 1) (sourceB1 + difference 1 0) sourceC1) = raw2661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2661; decide +kernel
    rw [ha]
    exact (canonical2661 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1 + difference 0 2) (sourceB1 + difference 2 0) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1 + difference 0 2) (sourceB1 + difference 2 0) sourceC1) = raw2662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2662; decide +kernel
    rw [ha]
    exact (canonical2662 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1 + difference 0 3) (sourceB1 + difference 3 0) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1 + difference 0 3) (sourceB1 + difference 3 0) sourceC1) = raw2663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2663; decide +kernel
    rw [ha]
    exact (canonical2663 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1 + difference 0 4) (sourceB1 + difference 4 0) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1 + difference 0 4) (sourceB1 + difference 4 0) sourceC1) = raw2664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2664; decide +kernel
    rw [ha]
    exact (canonical2664 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1 + difference 0 5) (sourceB1 + difference 5 0) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA1 + difference 0 5) (sourceB1 + difference 5 0) sourceC1) = raw2665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2665; decide +kernel
    rw [ha]
    exact (canonical2665 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1 + difference 1 0) (sourceB1 + difference 0 1) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA1 + difference 1 0) (sourceB1 + difference 0 1) sourceC1) = raw2666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2666; decide +kernel
    rw [ha]
    exact (canonical2666 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1 + difference 1 2) (sourceB1 + difference 2 1) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1 + difference 1 2) (sourceB1 + difference 2 1) sourceC1) = raw2667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2667; decide +kernel
    rw [ha]
    exact (canonical2667 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1 + difference 1 3) (sourceB1 + difference 3 1) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1 + difference 1 3) (sourceB1 + difference 3 1) sourceC1) = raw2668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2668; decide +kernel
    rw [ha]
    exact (canonical2668 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1 + difference 1 4) (sourceB1 + difference 4 1) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1 + difference 1 4) (sourceB1 + difference 4 1) sourceC1) = raw2669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2669; decide +kernel
    rw [ha]
    exact (canonical2669 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1 + difference 1 5) (sourceB1 + difference 5 1) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA1 + difference 1 5) (sourceB1 + difference 5 1) sourceC1) = raw2670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2670; decide +kernel
    rw [ha]
    exact (canonical2670 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1 + difference 2 0) (sourceB1 + difference 0 2) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA1 + difference 2 0) (sourceB1 + difference 0 2) sourceC1) = raw2671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2671; decide +kernel
    rw [ha]
    exact (canonical2671 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1 + difference 2 1) (sourceB1 + difference 1 2) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1 + difference 2 1) (sourceB1 + difference 1 2) sourceC1) = raw2672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2672; decide +kernel
    rw [ha]
    exact (canonical2672 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1 + difference 2 3) (sourceB1 + difference 3 2) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1 + difference 2 3) (sourceB1 + difference 3 2) sourceC1) = raw2673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2673; decide +kernel
    rw [ha]
    exact (canonical2673 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1 + difference 2 4) (sourceB1 + difference 4 2) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1 + difference 2 4) (sourceB1 + difference 4 2) sourceC1) = raw2674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2674; decide +kernel
    rw [ha]
    exact (canonical2674 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1 + difference 2 5) (sourceB1 + difference 5 2) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA1 + difference 2 5) (sourceB1 + difference 5 2) sourceC1) = raw2675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2675; decide +kernel
    rw [ha]
    exact (canonical2675 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1 + difference 3 0) (sourceB1 + difference 0 3) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1 + difference 3 0) (sourceB1 + difference 0 3) sourceC1) = raw2676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2676; decide +kernel
    rw [ha]
    exact (canonical2676 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1 + difference 3 1) (sourceB1 + difference 1 3) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1 + difference 3 1) (sourceB1 + difference 1 3) sourceC1) = raw2677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2677; decide +kernel
    rw [ha]
    exact (canonical2677 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1 + difference 3 2) (sourceB1 + difference 2 3) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1 + difference 3 2) (sourceB1 + difference 2 3) sourceC1) = raw2678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2678; decide +kernel
    rw [ha]
    exact (canonical2678 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1 + difference 3 4) (sourceB1 + difference 4 3) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1 + difference 3 4) (sourceB1 + difference 4 3) sourceC1) = raw2679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2679; decide +kernel
    rw [ha]
    exact (canonical2679 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1 + difference 3 5) (sourceB1 + difference 5 3) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA1 + difference 3 5) (sourceB1 + difference 5 3) sourceC1) = raw2680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2680; decide +kernel
    rw [ha]
    exact (canonical2680 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1 + difference 4 0) (sourceB1 + difference 0 4) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1 + difference 4 0) (sourceB1 + difference 0 4) sourceC1) = raw2681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2681; decide +kernel
    rw [ha]
    exact (canonical2681 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1 + difference 4 1) (sourceB1 + difference 1 4) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1 + difference 4 1) (sourceB1 + difference 1 4) sourceC1) = raw2682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2682; decide +kernel
    rw [ha]
    exact (canonical2682 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1 + difference 4 2) (sourceB1 + difference 2 4) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1 + difference 4 2) (sourceB1 + difference 2 4) sourceC1) = raw2683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2683; decide +kernel
    rw [ha]
    exact (canonical2683 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1 + difference 4 3) (sourceB1 + difference 3 4) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1 + difference 4 3) (sourceB1 + difference 3 4) sourceC1) = raw2684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2684; decide +kernel
    rw [ha]
    exact (canonical2684 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1 + difference 4 5) (sourceB1 + difference 5 4) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA1 + difference 4 5) (sourceB1 + difference 5 4) sourceC1) = raw2685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2685; decide +kernel
    rw [ha]
    exact (canonical2685 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1 + difference 5 0) (sourceB1 + difference 0 5) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA1 + difference 5 0) (sourceB1 + difference 0 5) sourceC1) = raw2686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2686; decide +kernel
    rw [ha]
    exact (canonical2686 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1 + difference 5 1) (sourceB1 + difference 1 5) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA1 + difference 5 1) (sourceB1 + difference 1 5) sourceC1) = raw2687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2687; decide +kernel
    rw [ha]
    exact (canonical2687 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1 + difference 5 2) (sourceB1 + difference 2 5) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA1 + difference 5 2) (sourceB1 + difference 2 5) sourceC1) = raw2688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2688; decide +kernel
    rw [ha]
    exact (canonical2688 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1 + difference 5 3) (sourceB1 + difference 3 5) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA1 + difference 5 3) (sourceB1 + difference 3 5) sourceC1) = raw2689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2689; decide +kernel
    rw [ha]
    exact (canonical2689 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1 + difference 5 4) (sourceB1 + difference 4 5) sourceC1) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA1 + difference 5 4) (sourceB1 + difference 4 5) sourceC1) = raw2690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1 sourceB1 sourceC1 difference raw2690; decide +kernel
    rw [ha]
    exact (canonical2690 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1 sourceB1 sourceC1
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB2 : Charge := ![0, 0, 0, 1, 1, -2]
def sourceC2 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm2 : Integer.Sparse Master := [(Sum.inr 2245, 2), (Sum.inr 2247, 1), (Sum.inr 2266, 2), (Sum.inr 3077, 2), (Sum.inr 3101, 2), (Sum.inr 3801, 2), (Sum.inr 3809, 4), (Sum.inr 3853, 4), (Sum.inr 3862, 2), (Sum.inr 3910, 2), (Sum.inr 3913, 2), (Sum.inr 4016, 1), (Sum.inr 4039, 2), (Sum.inr 4040, 2)]

theorem sourceEq2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2 + difference 0 1) (sourceB2 + difference 1 0) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA2 + difference 0 1) (sourceB2 + difference 1 0) sourceC2) = raw2691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2691; decide +kernel
    rw [ha]
    exact (canonical2691 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2 + difference 0 2) (sourceB2 + difference 2 0) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA2 + difference 0 2) (sourceB2 + difference 2 0) sourceC2) = raw2692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2692; decide +kernel
    rw [ha]
    exact (canonical2692 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2 + difference 0 3) (sourceB2 + difference 3 0) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA2 + difference 0 3) (sourceB2 + difference 3 0) sourceC2) = raw2693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2693; decide +kernel
    rw [ha]
    exact (canonical2693 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2 + difference 0 4) (sourceB2 + difference 4 0) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA2 + difference 0 4) (sourceB2 + difference 4 0) sourceC2) = raw2694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2694; decide +kernel
    rw [ha]
    exact (canonical2694 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2 + difference 0 5) (sourceB2 + difference 5 0) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4016) := by
    have ha : (tripleCharges (sourceA2 + difference 0 5) (sourceB2 + difference 5 0) sourceC2) = raw2695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2695; decide +kernel
    rw [ha]
    exact (canonical2695 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2 + difference 1 0) (sourceB2 + difference 0 1) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA2 + difference 1 0) (sourceB2 + difference 0 1) sourceC2) = raw2696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2696; decide +kernel
    rw [ha]
    exact (canonical2696 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2 + difference 1 2) (sourceB2 + difference 2 1) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA2 + difference 1 2) (sourceB2 + difference 2 1) sourceC2) = raw2697 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2697; decide +kernel
    rw [ha]
    exact (canonical2697 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2 + difference 1 3) (sourceB2 + difference 3 1) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA2 + difference 1 3) (sourceB2 + difference 3 1) sourceC2) = raw2698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2698; decide +kernel
    rw [ha]
    exact (canonical2698 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2 + difference 1 4) (sourceB2 + difference 4 1) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA2 + difference 1 4) (sourceB2 + difference 4 1) sourceC2) = raw2699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2699; decide +kernel
    rw [ha]
    exact (canonical2699 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2 + difference 1 5) (sourceB2 + difference 5 1) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4039) := by
    have ha : (tripleCharges (sourceA2 + difference 1 5) (sourceB2 + difference 5 1) sourceC2) = raw2700 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2700; decide +kernel
    rw [ha]
    exact (canonical2700 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2 + difference 2 0) (sourceB2 + difference 0 2) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA2 + difference 2 0) (sourceB2 + difference 0 2) sourceC2) = raw2701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2701; decide +kernel
    rw [ha]
    exact (canonical2701 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2 + difference 2 1) (sourceB2 + difference 1 2) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA2 + difference 2 1) (sourceB2 + difference 1 2) sourceC2) = raw2702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2702; decide +kernel
    rw [ha]
    exact (canonical2702 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2 + difference 2 3) (sourceB2 + difference 3 2) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA2 + difference 2 3) (sourceB2 + difference 3 2) sourceC2) = raw2703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2703; decide +kernel
    rw [ha]
    exact (canonical2703 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2 + difference 2 4) (sourceB2 + difference 4 2) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA2 + difference 2 4) (sourceB2 + difference 4 2) sourceC2) = raw2704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2704; decide +kernel
    rw [ha]
    exact (canonical2704 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2 + difference 2 5) (sourceB2 + difference 5 2) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4039) := by
    have ha : (tripleCharges (sourceA2 + difference 2 5) (sourceB2 + difference 5 2) sourceC2) = raw2705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2705; decide +kernel
    rw [ha]
    exact (canonical2705 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2 + difference 3 0) (sourceB2 + difference 0 3) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA2 + difference 3 0) (sourceB2 + difference 0 3) sourceC2) = raw2706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2706; decide +kernel
    rw [ha]
    exact (canonical2706 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2 + difference 3 1) (sourceB2 + difference 1 3) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA2 + difference 3 1) (sourceB2 + difference 1 3) sourceC2) = raw2707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2707; decide +kernel
    rw [ha]
    exact (canonical2707 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2 + difference 3 2) (sourceB2 + difference 2 3) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA2 + difference 3 2) (sourceB2 + difference 2 3) sourceC2) = raw2708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2708; decide +kernel
    rw [ha]
    exact (canonical2708 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2 + difference 3 4) (sourceB2 + difference 4 3) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA2 + difference 3 4) (sourceB2 + difference 4 3) sourceC2) = raw2709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2709; decide +kernel
    rw [ha]
    exact (canonical2709 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2 + difference 3 5) (sourceB2 + difference 5 3) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4040) := by
    have ha : (tripleCharges (sourceA2 + difference 3 5) (sourceB2 + difference 5 3) sourceC2) = raw2710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2710; decide +kernel
    rw [ha]
    exact (canonical2710 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2 + difference 4 0) (sourceB2 + difference 0 4) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA2 + difference 4 0) (sourceB2 + difference 0 4) sourceC2) = raw2711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2711; decide +kernel
    rw [ha]
    exact (canonical2711 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2 + difference 4 1) (sourceB2 + difference 1 4) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA2 + difference 4 1) (sourceB2 + difference 1 4) sourceC2) = raw2712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2712; decide +kernel
    rw [ha]
    exact (canonical2712 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2 + difference 4 2) (sourceB2 + difference 2 4) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA2 + difference 4 2) (sourceB2 + difference 2 4) sourceC2) = raw2713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2713; decide +kernel
    rw [ha]
    exact (canonical2713 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2 + difference 4 3) (sourceB2 + difference 3 4) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA2 + difference 4 3) (sourceB2 + difference 3 4) sourceC2) = raw2714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2714; decide +kernel
    rw [ha]
    exact (canonical2714 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2 + difference 4 5) (sourceB2 + difference 5 4) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4040) := by
    have ha : (tripleCharges (sourceA2 + difference 4 5) (sourceB2 + difference 5 4) sourceC2) = raw2715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2715; decide +kernel
    rw [ha]
    exact (canonical2715 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2 + difference 5 0) (sourceB2 + difference 0 5) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA2 + difference 5 0) (sourceB2 + difference 0 5) sourceC2) = raw2716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2716; decide +kernel
    rw [ha]
    exact (canonical2716 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2 + difference 5 1) (sourceB2 + difference 1 5) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA2 + difference 5 1) (sourceB2 + difference 1 5) sourceC2) = raw2717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2717; decide +kernel
    rw [ha]
    exact (canonical2717 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2 + difference 5 2) (sourceB2 + difference 2 5) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA2 + difference 5 2) (sourceB2 + difference 2 5) sourceC2) = raw2718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2718; decide +kernel
    rw [ha]
    exact (canonical2718 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2 + difference 5 3) (sourceB2 + difference 3 5) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA2 + difference 5 3) (sourceB2 + difference 3 5) sourceC2) = raw2719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2719; decide +kernel
    rw [ha]
    exact (canonical2719 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2 + difference 5 4) (sourceB2 + difference 4 5) sourceC2) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA2 + difference 5 4) (sourceB2 + difference 4 5) sourceC2) = raw2720 := by
      apply Matrix.ext; unfold tripleCharges sourceA2 sourceB2 sourceC2 difference raw2720; decide +kernel
    rw [ha]
    exact (canonical2720 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2 sourceB2 sourceC2
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2, Integer.Sparse.eval]
  linarith only [hs]

def sourceA3 : Charge := ![0, 0, 0, 1, 1, -2]
def sourceB3 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC3 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceForm3 : Integer.Sparse Master := [(Sum.inr 5301, 4), (Sum.inr 5302, 4), (Sum.inr 5306, 2), (Sum.inr 5412, 4), (Sum.inr 5437, 2), (Sum.inr 5439, 4), (Sum.inr 5453, 4), (Sum.inr 5455, 4), (Sum.inr 5456, 2)]

theorem sourceEq3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm3 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA3 + difference 0 1) (sourceB3 + difference 1 0) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA3 + difference 0 1) (sourceB3 + difference 1 0) sourceC3) = raw2721 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2721; decide +kernel
    rw [ha]
    exact (canonical2721 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA3 + difference 0 2) (sourceB3 + difference 2 0) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA3 + difference 0 2) (sourceB3 + difference 2 0) sourceC3) = raw2722 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2722; decide +kernel
    rw [ha]
    exact (canonical2722 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA3 + difference 0 3) (sourceB3 + difference 3 0) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA3 + difference 0 3) (sourceB3 + difference 3 0) sourceC3) = raw2723 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2723; decide +kernel
    rw [ha]
    exact (canonical2723 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA3 + difference 0 4) (sourceB3 + difference 4 0) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA3 + difference 0 4) (sourceB3 + difference 4 0) sourceC3) = raw2724 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2724; decide +kernel
    rw [ha]
    exact (canonical2724 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA3 + difference 0 5) (sourceB3 + difference 5 0) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA3 + difference 0 5) (sourceB3 + difference 5 0) sourceC3) = raw2725 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2725; decide +kernel
    rw [ha]
    exact (canonical2725 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA3 + difference 1 0) (sourceB3 + difference 0 1) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA3 + difference 1 0) (sourceB3 + difference 0 1) sourceC3) = raw2726 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2726; decide +kernel
    rw [ha]
    exact (canonical2726 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA3 + difference 1 2) (sourceB3 + difference 2 1) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA3 + difference 1 2) (sourceB3 + difference 2 1) sourceC3) = raw2727 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2727; decide +kernel
    rw [ha]
    exact (canonical2727 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA3 + difference 1 3) (sourceB3 + difference 3 1) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA3 + difference 1 3) (sourceB3 + difference 3 1) sourceC3) = raw2728 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2728; decide +kernel
    rw [ha]
    exact (canonical2728 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA3 + difference 1 4) (sourceB3 + difference 4 1) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA3 + difference 1 4) (sourceB3 + difference 4 1) sourceC3) = raw2729 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2729; decide +kernel
    rw [ha]
    exact (canonical2729 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA3 + difference 1 5) (sourceB3 + difference 5 1) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA3 + difference 1 5) (sourceB3 + difference 5 1) sourceC3) = raw2730 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2730; decide +kernel
    rw [ha]
    exact (canonical2730 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA3 + difference 2 0) (sourceB3 + difference 0 2) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA3 + difference 2 0) (sourceB3 + difference 0 2) sourceC3) = raw2731 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2731; decide +kernel
    rw [ha]
    exact (canonical2731 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA3 + difference 2 1) (sourceB3 + difference 1 2) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA3 + difference 2 1) (sourceB3 + difference 1 2) sourceC3) = raw2732 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2732; decide +kernel
    rw [ha]
    exact (canonical2732 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA3 + difference 2 3) (sourceB3 + difference 3 2) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA3 + difference 2 3) (sourceB3 + difference 3 2) sourceC3) = raw2733 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2733; decide +kernel
    rw [ha]
    exact (canonical2733 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA3 + difference 2 4) (sourceB3 + difference 4 2) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA3 + difference 2 4) (sourceB3 + difference 4 2) sourceC3) = raw2734 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2734; decide +kernel
    rw [ha]
    exact (canonical2734 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA3 + difference 2 5) (sourceB3 + difference 5 2) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA3 + difference 2 5) (sourceB3 + difference 5 2) sourceC3) = raw2735 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2735; decide +kernel
    rw [ha]
    exact (canonical2735 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA3 + difference 3 0) (sourceB3 + difference 0 3) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA3 + difference 3 0) (sourceB3 + difference 0 3) sourceC3) = raw2736 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2736; decide +kernel
    rw [ha]
    exact (canonical2736 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA3 + difference 3 1) (sourceB3 + difference 1 3) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA3 + difference 3 1) (sourceB3 + difference 1 3) sourceC3) = raw2737 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2737; decide +kernel
    rw [ha]
    exact (canonical2737 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA3 + difference 3 2) (sourceB3 + difference 2 3) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA3 + difference 3 2) (sourceB3 + difference 2 3) sourceC3) = raw2738 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2738; decide +kernel
    rw [ha]
    exact (canonical2738 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA3 + difference 3 4) (sourceB3 + difference 4 3) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5456) := by
    have ha : (tripleCharges (sourceA3 + difference 3 4) (sourceB3 + difference 4 3) sourceC3) = raw2739 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2739; decide +kernel
    rw [ha]
    exact (canonical2739 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA3 + difference 3 5) (sourceB3 + difference 5 3) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA3 + difference 3 5) (sourceB3 + difference 5 3) sourceC3) = raw2740 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2740; decide +kernel
    rw [ha]
    exact (canonical2740 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA3 + difference 4 0) (sourceB3 + difference 0 4) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA3 + difference 4 0) (sourceB3 + difference 0 4) sourceC3) = raw2741 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2741; decide +kernel
    rw [ha]
    exact (canonical2741 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA3 + difference 4 1) (sourceB3 + difference 1 4) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA3 + difference 4 1) (sourceB3 + difference 1 4) sourceC3) = raw2742 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2742; decide +kernel
    rw [ha]
    exact (canonical2742 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA3 + difference 4 2) (sourceB3 + difference 2 4) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA3 + difference 4 2) (sourceB3 + difference 2 4) sourceC3) = raw2743 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2743; decide +kernel
    rw [ha]
    exact (canonical2743 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA3 + difference 4 3) (sourceB3 + difference 3 4) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5456) := by
    have ha : (tripleCharges (sourceA3 + difference 4 3) (sourceB3 + difference 3 4) sourceC3) = raw2744 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2744; decide +kernel
    rw [ha]
    exact (canonical2744 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA3 + difference 4 5) (sourceB3 + difference 5 4) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA3 + difference 4 5) (sourceB3 + difference 5 4) sourceC3) = raw2745 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2745; decide +kernel
    rw [ha]
    exact (canonical2745 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA3 + difference 5 0) (sourceB3 + difference 0 5) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA3 + difference 5 0) (sourceB3 + difference 0 5) sourceC3) = raw2746 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2746; decide +kernel
    rw [ha]
    exact (canonical2746 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA3 + difference 5 1) (sourceB3 + difference 1 5) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA3 + difference 5 1) (sourceB3 + difference 1 5) sourceC3) = raw2747 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2747; decide +kernel
    rw [ha]
    exact (canonical2747 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA3 + difference 5 2) (sourceB3 + difference 2 5) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA3 + difference 5 2) (sourceB3 + difference 2 5) sourceC3) = raw2748 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2748; decide +kernel
    rw [ha]
    exact (canonical2748 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA3 + difference 5 3) (sourceB3 + difference 3 5) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA3 + difference 5 3) (sourceB3 + difference 3 5) sourceC3) = raw2749 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2749; decide +kernel
    rw [ha]
    exact (canonical2749 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA3 + difference 5 4) (sourceB3 + difference 4 5) sourceC3) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA3 + difference 5 4) (sourceB3 + difference 4 5) sourceC3) = raw2750 := by
      apply Matrix.ext; unfold tripleCharges sourceA3 sourceB3 sourceC3 difference raw2750; decide +kernel
    rw [ha]
    exact (canonical2750 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA3 sourceB3 sourceC3
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm3, Integer.Sparse.eval]
  linarith only [hs]

def sourceA4 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB4 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceC4 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm4 : Integer.Sparse Master := [(Sum.inr 5259, 4), (Sum.inr 5261, 1), (Sum.inr 5275, 2), (Sum.inr 5293, 2), (Sum.inr 5473, 4), (Sum.inr 5475, 1), (Sum.inr 5477, 2), (Sum.inr 5483, 4), (Sum.inr 5487, 1), (Sum.inr 5490, 4), (Sum.inr 5492, 2), (Sum.inr 5493, 2), (Sum.inr 5501, 1)]

theorem sourceEq4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm4 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA4 + difference 0 1) (sourceB4 + difference 1 0) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA4 + difference 0 1) (sourceB4 + difference 1 0) sourceC4) = raw2751 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2751; decide +kernel
    rw [ha]
    exact (canonical2751 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA4 + difference 0 2) (sourceB4 + difference 2 0) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA4 + difference 0 2) (sourceB4 + difference 2 0) sourceC4) = raw2752 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2752; decide +kernel
    rw [ha]
    exact (canonical2752 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA4 + difference 0 3) (sourceB4 + difference 3 0) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA4 + difference 0 3) (sourceB4 + difference 3 0) sourceC4) = raw2753 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2753; decide +kernel
    rw [ha]
    exact (canonical2753 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA4 + difference 0 4) (sourceB4 + difference 4 0) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA4 + difference 0 4) (sourceB4 + difference 4 0) sourceC4) = raw2754 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2754; decide +kernel
    rw [ha]
    exact (canonical2754 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA4 + difference 0 5) (sourceB4 + difference 5 0) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5501) := by
    have ha : (tripleCharges (sourceA4 + difference 0 5) (sourceB4 + difference 5 0) sourceC4) = raw2755 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2755; decide +kernel
    rw [ha]
    exact (canonical2755 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA4 + difference 1 0) (sourceB4 + difference 0 1) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA4 + difference 1 0) (sourceB4 + difference 0 1) sourceC4) = raw2756 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2756; decide +kernel
    rw [ha]
    exact (canonical2756 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA4 + difference 1 2) (sourceB4 + difference 2 1) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA4 + difference 1 2) (sourceB4 + difference 2 1) sourceC4) = raw2757 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2757; decide +kernel
    rw [ha]
    exact (canonical2757 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA4 + difference 1 3) (sourceB4 + difference 3 1) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA4 + difference 1 3) (sourceB4 + difference 3 1) sourceC4) = raw2758 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2758; decide +kernel
    rw [ha]
    exact (canonical2758 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA4 + difference 1 4) (sourceB4 + difference 4 1) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5475) := by
    have ha : (tripleCharges (sourceA4 + difference 1 4) (sourceB4 + difference 4 1) sourceC4) = raw2759 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2759; decide +kernel
    rw [ha]
    exact (canonical2759 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA4 + difference 1 5) (sourceB4 + difference 5 1) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA4 + difference 1 5) (sourceB4 + difference 5 1) sourceC4) = raw2760 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2760; decide +kernel
    rw [ha]
    exact (canonical2760 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA4 + difference 2 0) (sourceB4 + difference 0 2) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA4 + difference 2 0) (sourceB4 + difference 0 2) sourceC4) = raw2761 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2761; decide +kernel
    rw [ha]
    exact (canonical2761 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA4 + difference 2 1) (sourceB4 + difference 1 2) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA4 + difference 2 1) (sourceB4 + difference 1 2) sourceC4) = raw2762 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2762; decide +kernel
    rw [ha]
    exact (canonical2762 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA4 + difference 2 3) (sourceB4 + difference 3 2) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA4 + difference 2 3) (sourceB4 + difference 3 2) sourceC4) = raw2763 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2763; decide +kernel
    rw [ha]
    exact (canonical2763 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA4 + difference 2 4) (sourceB4 + difference 4 2) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA4 + difference 2 4) (sourceB4 + difference 4 2) sourceC4) = raw2764 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2764; decide +kernel
    rw [ha]
    exact (canonical2764 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA4 + difference 2 5) (sourceB4 + difference 5 2) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA4 + difference 2 5) (sourceB4 + difference 5 2) sourceC4) = raw2765 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2765; decide +kernel
    rw [ha]
    exact (canonical2765 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA4 + difference 3 0) (sourceB4 + difference 0 3) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA4 + difference 3 0) (sourceB4 + difference 0 3) sourceC4) = raw2766 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2766; decide +kernel
    rw [ha]
    exact (canonical2766 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA4 + difference 3 1) (sourceB4 + difference 1 3) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA4 + difference 3 1) (sourceB4 + difference 1 3) sourceC4) = raw2767 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2767; decide +kernel
    rw [ha]
    exact (canonical2767 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA4 + difference 3 2) (sourceB4 + difference 2 3) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA4 + difference 3 2) (sourceB4 + difference 2 3) sourceC4) = raw2768 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2768; decide +kernel
    rw [ha]
    exact (canonical2768 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA4 + difference 3 4) (sourceB4 + difference 4 3) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA4 + difference 3 4) (sourceB4 + difference 4 3) sourceC4) = raw2769 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2769; decide +kernel
    rw [ha]
    exact (canonical2769 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA4 + difference 3 5) (sourceB4 + difference 5 3) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA4 + difference 3 5) (sourceB4 + difference 5 3) sourceC4) = raw2770 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2770; decide +kernel
    rw [ha]
    exact (canonical2770 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA4 + difference 4 0) (sourceB4 + difference 0 4) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA4 + difference 4 0) (sourceB4 + difference 0 4) sourceC4) = raw2771 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2771; decide +kernel
    rw [ha]
    exact (canonical2771 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA4 + difference 4 1) (sourceB4 + difference 1 4) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA4 + difference 4 1) (sourceB4 + difference 1 4) sourceC4) = raw2772 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2772; decide +kernel
    rw [ha]
    exact (canonical2772 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA4 + difference 4 2) (sourceB4 + difference 2 4) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA4 + difference 4 2) (sourceB4 + difference 2 4) sourceC4) = raw2773 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2773; decide +kernel
    rw [ha]
    exact (canonical2773 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA4 + difference 4 3) (sourceB4 + difference 3 4) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA4 + difference 4 3) (sourceB4 + difference 3 4) sourceC4) = raw2774 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2774; decide +kernel
    rw [ha]
    exact (canonical2774 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA4 + difference 4 5) (sourceB4 + difference 5 4) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA4 + difference 4 5) (sourceB4 + difference 5 4) sourceC4) = raw2775 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2775; decide +kernel
    rw [ha]
    exact (canonical2775 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA4 + difference 5 0) (sourceB4 + difference 0 5) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA4 + difference 5 0) (sourceB4 + difference 0 5) sourceC4) = raw2776 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2776; decide +kernel
    rw [ha]
    exact (canonical2776 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA4 + difference 5 1) (sourceB4 + difference 1 5) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA4 + difference 5 1) (sourceB4 + difference 1 5) sourceC4) = raw2777 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2777; decide +kernel
    rw [ha]
    exact (canonical2777 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA4 + difference 5 2) (sourceB4 + difference 2 5) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA4 + difference 5 2) (sourceB4 + difference 2 5) sourceC4) = raw2778 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2778; decide +kernel
    rw [ha]
    exact (canonical2778 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA4 + difference 5 3) (sourceB4 + difference 3 5) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA4 + difference 5 3) (sourceB4 + difference 3 5) sourceC4) = raw2779 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2779; decide +kernel
    rw [ha]
    exact (canonical2779 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA4 + difference 5 4) (sourceB4 + difference 4 5) sourceC4) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA4 + difference 5 4) (sourceB4 + difference 4 5) sourceC4) = raw2780 := by
      apply Matrix.ext; unfold tripleCharges sourceA4 sourceB4 sourceC4 difference raw2780; decide +kernel
    rw [ha]
    exact (canonical2780 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA4 sourceB4 sourceC4
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm4, Integer.Sparse.eval]
  linarith only [hs]

def sourceA5 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB5 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceC5 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm5 : Integer.Sparse Master := [(Sum.inr 2723, 4), (Sum.inr 2726, 1), (Sum.inr 2743, 2), (Sum.inr 2767, 2), (Sum.inr 3958, 4), (Sum.inr 3963, 1), (Sum.inr 3971, 2), (Sum.inr 3981, 4), (Sum.inr 4000, 1), (Sum.inr 4013, 4), (Sum.inr 4015, 2), (Sum.inr 4018, 2), (Sum.inr 4055, 1)]

theorem sourceEq5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm5 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA5 + difference 0 1) (sourceB5 + difference 1 0) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4018) := by
    have ha : (tripleCharges (sourceA5 + difference 0 1) (sourceB5 + difference 1 0) sourceC5) = raw2781 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2781; decide +kernel
    rw [ha]
    exact (canonical2781 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA5 + difference 0 2) (sourceB5 + difference 2 0) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA5 + difference 0 2) (sourceB5 + difference 2 0) sourceC5) = raw2782 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2782; decide +kernel
    rw [ha]
    exact (canonical2782 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA5 + difference 0 3) (sourceB5 + difference 3 0) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA5 + difference 0 3) (sourceB5 + difference 3 0) sourceC5) = raw2783 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2783; decide +kernel
    rw [ha]
    exact (canonical2783 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA5 + difference 0 4) (sourceB5 + difference 4 0) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4015) := by
    have ha : (tripleCharges (sourceA5 + difference 0 4) (sourceB5 + difference 4 0) sourceC5) = raw2784 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2784; decide +kernel
    rw [ha]
    exact (canonical2784 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA5 + difference 0 5) (sourceB5 + difference 5 0) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4055) := by
    have ha : (tripleCharges (sourceA5 + difference 0 5) (sourceB5 + difference 5 0) sourceC5) = raw2785 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2785; decide +kernel
    rw [ha]
    exact (canonical2785 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA5 + difference 1 0) (sourceB5 + difference 0 1) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA5 + difference 1 0) (sourceB5 + difference 0 1) sourceC5) = raw2786 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2786; decide +kernel
    rw [ha]
    exact (canonical2786 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA5 + difference 1 2) (sourceB5 + difference 2 1) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA5 + difference 1 2) (sourceB5 + difference 2 1) sourceC5) = raw2787 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2787; decide +kernel
    rw [ha]
    exact (canonical2787 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA5 + difference 1 3) (sourceB5 + difference 3 1) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA5 + difference 1 3) (sourceB5 + difference 3 1) sourceC5) = raw2788 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2788; decide +kernel
    rw [ha]
    exact (canonical2788 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA5 + difference 1 4) (sourceB5 + difference 4 1) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA5 + difference 1 4) (sourceB5 + difference 4 1) sourceC5) = raw2789 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2789; decide +kernel
    rw [ha]
    exact (canonical2789 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA5 + difference 1 5) (sourceB5 + difference 5 1) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4015) := by
    have ha : (tripleCharges (sourceA5 + difference 1 5) (sourceB5 + difference 5 1) sourceC5) = raw2790 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2790; decide +kernel
    rw [ha]
    exact (canonical2790 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA5 + difference 2 0) (sourceB5 + difference 0 2) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA5 + difference 2 0) (sourceB5 + difference 0 2) sourceC5) = raw2791 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2791; decide +kernel
    rw [ha]
    exact (canonical2791 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA5 + difference 2 1) (sourceB5 + difference 1 2) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA5 + difference 2 1) (sourceB5 + difference 1 2) sourceC5) = raw2792 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2792; decide +kernel
    rw [ha]
    exact (canonical2792 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA5 + difference 2 3) (sourceB5 + difference 3 2) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3971) := by
    have ha : (tripleCharges (sourceA5 + difference 2 3) (sourceB5 + difference 3 2) sourceC5) = raw2793 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2793; decide +kernel
    rw [ha]
    exact (canonical2793 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA5 + difference 2 4) (sourceB5 + difference 4 2) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA5 + difference 2 4) (sourceB5 + difference 4 2) sourceC5) = raw2794 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2794; decide +kernel
    rw [ha]
    exact (canonical2794 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA5 + difference 2 5) (sourceB5 + difference 5 2) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA5 + difference 2 5) (sourceB5 + difference 5 2) sourceC5) = raw2795 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2795; decide +kernel
    rw [ha]
    exact (canonical2795 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA5 + difference 3 0) (sourceB5 + difference 0 3) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA5 + difference 3 0) (sourceB5 + difference 0 3) sourceC5) = raw2796 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2796; decide +kernel
    rw [ha]
    exact (canonical2796 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA5 + difference 3 1) (sourceB5 + difference 1 3) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA5 + difference 3 1) (sourceB5 + difference 1 3) sourceC5) = raw2797 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2797; decide +kernel
    rw [ha]
    exact (canonical2797 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA5 + difference 3 2) (sourceB5 + difference 2 3) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3971) := by
    have ha : (tripleCharges (sourceA5 + difference 3 2) (sourceB5 + difference 2 3) sourceC5) = raw2798 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2798; decide +kernel
    rw [ha]
    exact (canonical2798 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA5 + difference 3 4) (sourceB5 + difference 4 3) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA5 + difference 3 4) (sourceB5 + difference 4 3) sourceC5) = raw2799 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2799; decide +kernel
    rw [ha]
    exact (canonical2799 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA5 + difference 3 5) (sourceB5 + difference 5 3) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA5 + difference 3 5) (sourceB5 + difference 5 3) sourceC5) = raw2800 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2800; decide +kernel
    rw [ha]
    exact (canonical2800 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA5 + difference 4 0) (sourceB5 + difference 0 4) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA5 + difference 4 0) (sourceB5 + difference 0 4) sourceC5) = raw2801 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2801; decide +kernel
    rw [ha]
    exact (canonical2801 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA5 + difference 4 1) (sourceB5 + difference 1 4) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4000) := by
    have ha : (tripleCharges (sourceA5 + difference 4 1) (sourceB5 + difference 1 4) sourceC5) = raw2802 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2802; decide +kernel
    rw [ha]
    exact (canonical2802 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA5 + difference 4 2) (sourceB5 + difference 2 4) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA5 + difference 4 2) (sourceB5 + difference 2 4) sourceC5) = raw2803 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2803; decide +kernel
    rw [ha]
    exact (canonical2803 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA5 + difference 4 3) (sourceB5 + difference 3 4) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA5 + difference 4 3) (sourceB5 + difference 3 4) sourceC5) = raw2804 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2804; decide +kernel
    rw [ha]
    exact (canonical2804 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA5 + difference 4 5) (sourceB5 + difference 5 4) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4018) := by
    have ha : (tripleCharges (sourceA5 + difference 4 5) (sourceB5 + difference 5 4) sourceC5) = raw2805 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2805; decide +kernel
    rw [ha]
    exact (canonical2805 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA5 + difference 5 0) (sourceB5 + difference 0 5) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA5 + difference 5 0) (sourceB5 + difference 0 5) sourceC5) = raw2806 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2806; decide +kernel
    rw [ha]
    exact (canonical2806 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA5 + difference 5 1) (sourceB5 + difference 1 5) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA5 + difference 5 1) (sourceB5 + difference 1 5) sourceC5) = raw2807 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2807; decide +kernel
    rw [ha]
    exact (canonical2807 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA5 + difference 5 2) (sourceB5 + difference 2 5) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA5 + difference 5 2) (sourceB5 + difference 2 5) sourceC5) = raw2808 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2808; decide +kernel
    rw [ha]
    exact (canonical2808 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA5 + difference 5 3) (sourceB5 + difference 3 5) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA5 + difference 5 3) (sourceB5 + difference 3 5) sourceC5) = raw2809 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2809; decide +kernel
    rw [ha]
    exact (canonical2809 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA5 + difference 5 4) (sourceB5 + difference 4 5) sourceC5) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA5 + difference 5 4) (sourceB5 + difference 4 5) sourceC5) = raw2810 := by
      apply Matrix.ext; unfold tripleCharges sourceA5 sourceB5 sourceC5 difference raw2810; decide +kernel
    rw [ha]
    exact (canonical2810 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA5 sourceB5 sourceC5
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm5, Integer.Sparse.eval]
  linarith only [hs]

def sourceA6 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB6 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceC6 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm6 : Integer.Sparse Master := [(Sum.inr 7, -1), (Sum.inr 378, 1), (Sum.inr 514, 1), (Sum.inr 518, 1), (Sum.inr 521, 1), (Sum.inr 526, 1), (Sum.inr 527, 1)]

theorem sourceEq6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm6 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA6 + difference 2 0) (sourceB6 + difference 0 2) sourceC6) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 378) := by
    have ha : (tripleCharges (sourceA6 + difference 2 0) (sourceB6 + difference 0 2) sourceC6) = raw2811 := by
      apply Matrix.ext; unfold tripleCharges sourceA6 sourceB6 sourceC6 difference raw2811; decide +kernel
    rw [ha]
    exact (canonical2811 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA6 + difference 2 1) (sourceB6 + difference 1 2) sourceC6) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 521) := by
    have ha : (tripleCharges (sourceA6 + difference 2 1) (sourceB6 + difference 1 2) sourceC6) = raw2812 := by
      apply Matrix.ext; unfold tripleCharges sourceA6 sourceB6 sourceC6 difference raw2812; decide +kernel
    rw [ha]
    exact (canonical2812 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA6 + difference 2 2) (sourceB6 + difference 2 2) sourceC6) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 527) := by
    have ha : (tripleCharges (sourceA6 + difference 2 2) (sourceB6 + difference 2 2) sourceC6) = raw2813 := by
      apply Matrix.ext; unfold tripleCharges sourceA6 sourceB6 sourceC6 difference raw2813; decide +kernel
    rw [ha]
    exact (canonical2813 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA6 + difference 2 3) (sourceB6 + difference 3 2) sourceC6) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 518) := by
    have ha : (tripleCharges (sourceA6 + difference 2 3) (sourceB6 + difference 3 2) sourceC6) = raw2814 := by
      apply Matrix.ext; unfold tripleCharges sourceA6 sourceB6 sourceC6 difference raw2814; decide +kernel
    rw [ha]
    exact (canonical2814 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA6 + difference 2 4) (sourceB6 + difference 4 2) sourceC6) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 514) := by
    have ha : (tripleCharges (sourceA6 + difference 2 4) (sourceB6 + difference 4 2) sourceC6) = raw2815 := by
      apply Matrix.ext; unfold tripleCharges sourceA6 sourceB6 sourceC6 difference raw2815; decide +kernel
    rw [ha]
    exact (canonical2815 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA6 + difference 2 5) (sourceB6 + difference 5 2) sourceC6) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 526) := by
    have ha : (tripleCharges (sourceA6 + difference 2 5) (sourceB6 + difference 5 2) sourceC6) = raw2816 := by
      apply Matrix.ext; unfold tripleCharges sourceA6 sourceB6 sourceC6 difference raw2816; decide +kernel
    rw [ha]
    exact (canonical2816 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA6 + sourceB6) sourceC6) (![0, 0] : Fin 2 → Fin 1) =
      mixedVector B (Sum.inr 7) := by
    have ha : (doubleCharges (sourceA6 + sourceB6) sourceC6) = raw2817 := by
      apply Matrix.ext; unfold doubleCharges sourceA6 sourceB6 sourceC6 raw2817; decide +kernel
    rw [ha]
    exact (canonical2817 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA6 sourceB6 sourceC6
    (0 : Fin 1) 0 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm6, Integer.Sparse.eval]
  linarith only [hs]

def sourceA7 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceB7 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC7 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceForm7 : Integer.Sparse Master := [(Sum.inr 5439, 8), (Sum.inr 5441, 2), (Sum.inr 5443, 4), (Sum.inr 5448, 4), (Sum.inr 5449, 1), (Sum.inr 5455, 4), (Sum.inr 5488, 2), (Sum.inr 5491, 4), (Sum.inr 5496, 1)]

theorem sourceEq7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm7 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA7 + difference 0 1) (sourceB7 + difference 1 0) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA7 + difference 0 1) (sourceB7 + difference 1 0) sourceC7) = raw2818 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2818; decide +kernel
    rw [ha]
    exact (canonical2818 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA7 + difference 0 2) (sourceB7 + difference 2 0) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA7 + difference 0 2) (sourceB7 + difference 2 0) sourceC7) = raw2819 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2819; decide +kernel
    rw [ha]
    exact (canonical2819 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA7 + difference 0 3) (sourceB7 + difference 3 0) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA7 + difference 0 3) (sourceB7 + difference 3 0) sourceC7) = raw2820 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2820; decide +kernel
    rw [ha]
    exact (canonical2820 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA7 + difference 0 4) (sourceB7 + difference 4 0) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA7 + difference 0 4) (sourceB7 + difference 4 0) sourceC7) = raw2821 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2821; decide +kernel
    rw [ha]
    exact (canonical2821 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA7 + difference 0 5) (sourceB7 + difference 5 0) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA7 + difference 0 5) (sourceB7 + difference 5 0) sourceC7) = raw2822 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2822; decide +kernel
    rw [ha]
    exact (canonical2822 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA7 + difference 1 0) (sourceB7 + difference 0 1) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA7 + difference 1 0) (sourceB7 + difference 0 1) sourceC7) = raw2749 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2749; decide +kernel
    rw [ha]
    exact (canonical2749 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA7 + difference 1 2) (sourceB7 + difference 2 1) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA7 + difference 1 2) (sourceB7 + difference 2 1) sourceC7) = raw2823 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2823; decide +kernel
    rw [ha]
    exact (canonical2823 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA7 + difference 1 3) (sourceB7 + difference 3 1) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA7 + difference 1 3) (sourceB7 + difference 3 1) sourceC7) = raw2824 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2824; decide +kernel
    rw [ha]
    exact (canonical2824 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA7 + difference 1 4) (sourceB7 + difference 4 1) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5496) := by
    have ha : (tripleCharges (sourceA7 + difference 1 4) (sourceB7 + difference 4 1) sourceC7) = raw2825 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2825; decide +kernel
    rw [ha]
    exact (canonical2825 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA7 + difference 1 5) (sourceB7 + difference 5 1) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA7 + difference 1 5) (sourceB7 + difference 5 1) sourceC7) = raw2723 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2723; decide +kernel
    rw [ha]
    exact (canonical2723 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA7 + difference 2 0) (sourceB7 + difference 0 2) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA7 + difference 2 0) (sourceB7 + difference 0 2) sourceC7) = raw2826 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2826; decide +kernel
    rw [ha]
    exact (canonical2826 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA7 + difference 2 1) (sourceB7 + difference 1 2) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA7 + difference 2 1) (sourceB7 + difference 1 2) sourceC7) = raw2827 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2827; decide +kernel
    rw [ha]
    exact (canonical2827 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA7 + difference 2 3) (sourceB7 + difference 3 2) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5488) := by
    have ha : (tripleCharges (sourceA7 + difference 2 3) (sourceB7 + difference 3 2) sourceC7) = raw2828 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2828; decide +kernel
    rw [ha]
    exact (canonical2828 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA7 + difference 2 4) (sourceB7 + difference 4 2) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA7 + difference 2 4) (sourceB7 + difference 4 2) sourceC7) = raw2829 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2829; decide +kernel
    rw [ha]
    exact (canonical2829 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA7 + difference 2 5) (sourceB7 + difference 5 2) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA7 + difference 2 5) (sourceB7 + difference 5 2) sourceC7) = raw2830 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2830; decide +kernel
    rw [ha]
    exact (canonical2830 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA7 + difference 3 0) (sourceB7 + difference 0 3) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA7 + difference 3 0) (sourceB7 + difference 0 3) sourceC7) = raw2747 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2747; decide +kernel
    rw [ha]
    exact (canonical2747 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA7 + difference 3 1) (sourceB7 + difference 1 3) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA7 + difference 3 1) (sourceB7 + difference 1 3) sourceC7) = raw2831 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2831; decide +kernel
    rw [ha]
    exact (canonical2831 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA7 + difference 3 2) (sourceB7 + difference 2 3) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5488) := by
    have ha : (tripleCharges (sourceA7 + difference 3 2) (sourceB7 + difference 2 3) sourceC7) = raw2832 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2832; decide +kernel
    rw [ha]
    exact (canonical2832 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA7 + difference 3 4) (sourceB7 + difference 4 3) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA7 + difference 3 4) (sourceB7 + difference 4 3) sourceC7) = raw2833 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2833; decide +kernel
    rw [ha]
    exact (canonical2833 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA7 + difference 3 5) (sourceB7 + difference 5 3) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA7 + difference 3 5) (sourceB7 + difference 5 3) sourceC7) = raw2721 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2721; decide +kernel
    rw [ha]
    exact (canonical2721 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA7 + difference 4 0) (sourceB7 + difference 0 4) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA7 + difference 4 0) (sourceB7 + difference 0 4) sourceC7) = raw2834 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2834; decide +kernel
    rw [ha]
    exact (canonical2834 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA7 + difference 4 1) (sourceB7 + difference 1 4) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5449) := by
    have ha : (tripleCharges (sourceA7 + difference 4 1) (sourceB7 + difference 1 4) sourceC7) = raw2835 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2835; decide +kernel
    rw [ha]
    exact (canonical2835 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA7 + difference 4 2) (sourceB7 + difference 2 4) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA7 + difference 4 2) (sourceB7 + difference 2 4) sourceC7) = raw2836 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2836; decide +kernel
    rw [ha]
    exact (canonical2836 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA7 + difference 4 3) (sourceB7 + difference 3 4) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA7 + difference 4 3) (sourceB7 + difference 3 4) sourceC7) = raw2837 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2837; decide +kernel
    rw [ha]
    exact (canonical2837 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA7 + difference 4 5) (sourceB7 + difference 5 4) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA7 + difference 4 5) (sourceB7 + difference 5 4) sourceC7) = raw2838 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2838; decide +kernel
    rw [ha]
    exact (canonical2838 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA7 + difference 5 0) (sourceB7 + difference 0 5) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA7 + difference 5 0) (sourceB7 + difference 0 5) sourceC7) = raw2839 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2839; decide +kernel
    rw [ha]
    exact (canonical2839 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA7 + difference 5 1) (sourceB7 + difference 1 5) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA7 + difference 5 1) (sourceB7 + difference 1 5) sourceC7) = raw2840 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2840; decide +kernel
    rw [ha]
    exact (canonical2840 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA7 + difference 5 2) (sourceB7 + difference 2 5) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA7 + difference 5 2) (sourceB7 + difference 2 5) sourceC7) = raw2841 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2841; decide +kernel
    rw [ha]
    exact (canonical2841 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA7 + difference 5 3) (sourceB7 + difference 3 5) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA7 + difference 5 3) (sourceB7 + difference 3 5) sourceC7) = raw2842 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2842; decide +kernel
    rw [ha]
    exact (canonical2842 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA7 + difference 5 4) (sourceB7 + difference 4 5) sourceC7) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA7 + difference 5 4) (sourceB7 + difference 4 5) sourceC7) = raw2843 := by
      apply Matrix.ext; unfold tripleCharges sourceA7 sourceB7 sourceC7 difference raw2843; decide +kernel
    rw [ha]
    exact (canonical2843 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA7 sourceB7 sourceC7
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm7, Integer.Sparse.eval]
  linarith only [hs]

def sourceA8 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceB8 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC8 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceForm8 : Integer.Sparse Master := [(Sum.inr 6, -1), (Sum.inr 494, 2), (Sum.inr 500, 1), (Sum.inr 524, 1), (Sum.inr 527, 2)]

theorem sourceEq8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm8 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA8 + difference 2 0) (sourceB8 + difference 0 2) sourceC8) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 494) := by
    have ha : (tripleCharges (sourceA8 + difference 2 0) (sourceB8 + difference 0 2) sourceC8) = raw2844 := by
      apply Matrix.ext; unfold tripleCharges sourceA8 sourceB8 sourceC8 difference raw2844; decide +kernel
    rw [ha]
    exact (canonical2844 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA8 + difference 2 1) (sourceB8 + difference 1 2) sourceC8) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 500) := by
    have ha : (tripleCharges (sourceA8 + difference 2 1) (sourceB8 + difference 1 2) sourceC8) = raw2845 := by
      apply Matrix.ext; unfold tripleCharges sourceA8 sourceB8 sourceC8 difference raw2845; decide +kernel
    rw [ha]
    exact (canonical2845 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA8 + difference 2 2) (sourceB8 + difference 2 2) sourceC8) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 527) := by
    have ha : (tripleCharges (sourceA8 + difference 2 2) (sourceB8 + difference 2 2) sourceC8) = raw2846 := by
      apply Matrix.ext; unfold tripleCharges sourceA8 sourceB8 sourceC8 difference raw2846; decide +kernel
    rw [ha]
    exact (canonical2846 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA8 + difference 2 3) (sourceB8 + difference 3 2) sourceC8) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 524) := by
    have ha : (tripleCharges (sourceA8 + difference 2 3) (sourceB8 + difference 3 2) sourceC8) = raw2847 := by
      apply Matrix.ext; unfold tripleCharges sourceA8 sourceB8 sourceC8 difference raw2847; decide +kernel
    rw [ha]
    exact (canonical2847 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA8 + difference 2 4) (sourceB8 + difference 4 2) sourceC8) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 527) := by
    have ha : (tripleCharges (sourceA8 + difference 2 4) (sourceB8 + difference 4 2) sourceC8) = raw2848 := by
      apply Matrix.ext; unfold tripleCharges sourceA8 sourceB8 sourceC8 difference raw2848; decide +kernel
    rw [ha]
    exact (canonical2848 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA8 + difference 2 5) (sourceB8 + difference 5 2) sourceC8) (![0, 0, 0] : Fin 3 → Fin 1) =
      mixedVector B (Sum.inr 494) := by
    have ha : (tripleCharges (sourceA8 + difference 2 5) (sourceB8 + difference 5 2) sourceC8) = raw2849 := by
      apply Matrix.ext; unfold tripleCharges sourceA8 sourceB8 sourceC8 difference raw2849; decide +kernel
    rw [ha]
    exact (canonical2849 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA8 + sourceB8) sourceC8) (![0, 0] : Fin 2 → Fin 1) =
      mixedVector B (Sum.inr 6) := by
    have ha : (doubleCharges (sourceA8 + sourceB8) sourceC8) = raw2850 := by
      apply Matrix.ext; unfold doubleCharges sourceA8 sourceB8 sourceC8 raw2850; decide +kernel
    rw [ha]
    exact (canonical2850 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA8 sourceB8 sourceC8
    (0 : Fin 1) 0 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm8, Integer.Sparse.eval]
  linarith only [hs]

def sourceA9 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB9 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC9 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceForm9 : Integer.Sparse Master := [(Sum.inr 4093, 1), (Sum.inr 5293, 3), (Sum.inr 5294, 3), (Sum.inr 5296, 1), (Sum.inr 5309, 1), (Sum.inr 5310, 1), (Sum.inr 5434, 6), (Sum.inr 5442, 3), (Sum.inr 5451, 3), (Sum.inr 5454, 3), (Sum.inr 5492, 3), (Sum.inr 5494, 1), (Sum.inr 5495, 1)]

theorem sourceEq9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm9 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA9 + difference 0 1) (sourceB9 + difference 1 0) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA9 + difference 0 1) (sourceB9 + difference 1 0) sourceC9) = raw2851 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2851; decide +kernel
    rw [ha]
    exact (canonical2851 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA9 + difference 0 2) (sourceB9 + difference 2 0) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA9 + difference 0 2) (sourceB9 + difference 2 0) sourceC9) = raw2852 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2852; decide +kernel
    rw [ha]
    exact (canonical2852 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA9 + difference 0 3) (sourceB9 + difference 3 0) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA9 + difference 0 3) (sourceB9 + difference 3 0) sourceC9) = raw2853 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2853; decide +kernel
    rw [ha]
    exact (canonical2853 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA9 + difference 0 4) (sourceB9 + difference 4 0) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA9 + difference 0 4) (sourceB9 + difference 4 0) sourceC9) = raw2854 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2854; decide +kernel
    rw [ha]
    exact (canonical2854 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA9 + difference 0 5) (sourceB9 + difference 5 0) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5495) := by
    have ha : (tripleCharges (sourceA9 + difference 0 5) (sourceB9 + difference 5 0) sourceC9) = raw2855 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2855; decide +kernel
    rw [ha]
    exact (canonical2855 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA9 + difference 1 0) (sourceB9 + difference 0 1) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA9 + difference 1 0) (sourceB9 + difference 0 1) sourceC9) = raw2856 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2856; decide +kernel
    rw [ha]
    exact (canonical2856 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA9 + difference 1 2) (sourceB9 + difference 2 1) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA9 + difference 1 2) (sourceB9 + difference 2 1) sourceC9) = raw2857 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2857; decide +kernel
    rw [ha]
    exact (canonical2857 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA9 + difference 1 3) (sourceB9 + difference 3 1) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA9 + difference 1 3) (sourceB9 + difference 3 1) sourceC9) = raw2858 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2858; decide +kernel
    rw [ha]
    exact (canonical2858 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA9 + difference 1 4) (sourceB9 + difference 4 1) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA9 + difference 1 4) (sourceB9 + difference 4 1) sourceC9) = raw2859 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2859; decide +kernel
    rw [ha]
    exact (canonical2859 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA9 + difference 1 5) (sourceB9 + difference 5 1) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA9 + difference 1 5) (sourceB9 + difference 5 1) sourceC9) = raw2860 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2860; decide +kernel
    rw [ha]
    exact (canonical2860 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA9 + difference 2 0) (sourceB9 + difference 0 2) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA9 + difference 2 0) (sourceB9 + difference 0 2) sourceC9) = raw2861 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2861; decide +kernel
    rw [ha]
    exact (canonical2861 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA9 + difference 2 1) (sourceB9 + difference 1 2) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA9 + difference 2 1) (sourceB9 + difference 1 2) sourceC9) = raw2862 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2862; decide +kernel
    rw [ha]
    exact (canonical2862 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA9 + difference 2 3) (sourceB9 + difference 3 2) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA9 + difference 2 3) (sourceB9 + difference 3 2) sourceC9) = raw2863 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2863; decide +kernel
    rw [ha]
    exact (canonical2863 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA9 + difference 2 4) (sourceB9 + difference 4 2) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA9 + difference 2 4) (sourceB9 + difference 4 2) sourceC9) = raw2864 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2864; decide +kernel
    rw [ha]
    exact (canonical2864 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA9 + difference 2 5) (sourceB9 + difference 5 2) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA9 + difference 2 5) (sourceB9 + difference 5 2) sourceC9) = raw2865 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2865; decide +kernel
    rw [ha]
    exact (canonical2865 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA9 + difference 3 0) (sourceB9 + difference 0 3) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA9 + difference 3 0) (sourceB9 + difference 0 3) sourceC9) = raw2866 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2866; decide +kernel
    rw [ha]
    exact (canonical2866 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA9 + difference 3 1) (sourceB9 + difference 1 3) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA9 + difference 3 1) (sourceB9 + difference 1 3) sourceC9) = raw2867 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2867; decide +kernel
    rw [ha]
    exact (canonical2867 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA9 + difference 3 2) (sourceB9 + difference 2 3) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA9 + difference 3 2) (sourceB9 + difference 2 3) sourceC9) = raw2868 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2868; decide +kernel
    rw [ha]
    exact (canonical2868 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA9 + difference 3 4) (sourceB9 + difference 4 3) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA9 + difference 3 4) (sourceB9 + difference 4 3) sourceC9) = raw2869 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2869; decide +kernel
    rw [ha]
    exact (canonical2869 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA9 + difference 3 5) (sourceB9 + difference 5 3) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA9 + difference 3 5) (sourceB9 + difference 5 3) sourceC9) = raw2870 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2870; decide +kernel
    rw [ha]
    exact (canonical2870 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA9 + difference 4 0) (sourceB9 + difference 0 4) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA9 + difference 4 0) (sourceB9 + difference 0 4) sourceC9) = raw2871 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2871; decide +kernel
    rw [ha]
    exact (canonical2871 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA9 + difference 4 1) (sourceB9 + difference 1 4) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA9 + difference 4 1) (sourceB9 + difference 1 4) sourceC9) = raw2872 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2872; decide +kernel
    rw [ha]
    exact (canonical2872 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA9 + difference 4 2) (sourceB9 + difference 2 4) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA9 + difference 4 2) (sourceB9 + difference 2 4) sourceC9) = raw2873 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2873; decide +kernel
    rw [ha]
    exact (canonical2873 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA9 + difference 4 3) (sourceB9 + difference 3 4) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA9 + difference 4 3) (sourceB9 + difference 3 4) sourceC9) = raw2874 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2874; decide +kernel
    rw [ha]
    exact (canonical2874 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA9 + difference 4 5) (sourceB9 + difference 5 4) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5494) := by
    have ha : (tripleCharges (sourceA9 + difference 4 5) (sourceB9 + difference 5 4) sourceC9) = raw2875 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2875; decide +kernel
    rw [ha]
    exact (canonical2875 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA9 + difference 5 0) (sourceB9 + difference 0 5) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA9 + difference 5 0) (sourceB9 + difference 0 5) sourceC9) = raw2876 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2876; decide +kernel
    rw [ha]
    exact (canonical2876 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA9 + difference 5 1) (sourceB9 + difference 1 5) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA9 + difference 5 1) (sourceB9 + difference 1 5) sourceC9) = raw2877 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2877; decide +kernel
    rw [ha]
    exact (canonical2877 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA9 + difference 5 2) (sourceB9 + difference 2 5) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA9 + difference 5 2) (sourceB9 + difference 2 5) sourceC9) = raw2878 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2878; decide +kernel
    rw [ha]
    exact (canonical2878 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA9 + difference 5 3) (sourceB9 + difference 3 5) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA9 + difference 5 3) (sourceB9 + difference 3 5) sourceC9) = raw2879 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2879; decide +kernel
    rw [ha]
    exact (canonical2879 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA9 + difference 5 4) (sourceB9 + difference 4 5) sourceC9) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA9 + difference 5 4) (sourceB9 + difference 4 5) sourceC9) = raw2880 := by
      apply Matrix.ext; unfold tripleCharges sourceA9 sourceB9 sourceC9 difference raw2880; decide +kernel
    rw [ha]
    exact (canonical2880 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA9 sourceB9 sourceC9
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm9, Integer.Sparse.eval]
  linarith only [hs]

def sourceA10 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceB10 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC10 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceForm10 : Integer.Sparse Master := [(Sum.inr 4094, 1), (Sum.inr 5306, 3), (Sum.inr 5308, 1), (Sum.inr 5310, 1), (Sum.inr 5439, 6), (Sum.inr 5441, 3), (Sum.inr 5443, 3), (Sum.inr 5453, 3), (Sum.inr 5455, 4), (Sum.inr 5456, 1), (Sum.inr 5491, 3), (Sum.inr 5496, 1)]

theorem sourceEq10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm10 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA10 + difference 0 1) (sourceB10 + difference 1 0) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA10 + difference 0 1) (sourceB10 + difference 1 0) sourceC10) = raw2881 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2881; decide +kernel
    rw [ha]
    exact (canonical2881 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA10 + difference 0 2) (sourceB10 + difference 2 0) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA10 + difference 0 2) (sourceB10 + difference 2 0) sourceC10) = raw2882 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2882; decide +kernel
    rw [ha]
    exact (canonical2882 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA10 + difference 0 3) (sourceB10 + difference 3 0) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA10 + difference 0 3) (sourceB10 + difference 3 0) sourceC10) = raw2883 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2883; decide +kernel
    rw [ha]
    exact (canonical2883 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA10 + difference 0 4) (sourceB10 + difference 4 0) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5456) := by
    have ha : (tripleCharges (sourceA10 + difference 0 4) (sourceB10 + difference 4 0) sourceC10) = raw2884 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2884; decide +kernel
    rw [ha]
    exact (canonical2884 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA10 + difference 0 5) (sourceB10 + difference 5 0) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA10 + difference 0 5) (sourceB10 + difference 5 0) sourceC10) = raw2885 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2885; decide +kernel
    rw [ha]
    exact (canonical2885 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA10 + difference 1 0) (sourceB10 + difference 0 1) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA10 + difference 1 0) (sourceB10 + difference 0 1) sourceC10) = raw2886 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2886; decide +kernel
    rw [ha]
    exact (canonical2886 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA10 + difference 1 2) (sourceB10 + difference 2 1) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA10 + difference 1 2) (sourceB10 + difference 2 1) sourceC10) = raw2887 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2887; decide +kernel
    rw [ha]
    exact (canonical2887 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA10 + difference 1 3) (sourceB10 + difference 3 1) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA10 + difference 1 3) (sourceB10 + difference 3 1) sourceC10) = raw2888 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2888; decide +kernel
    rw [ha]
    exact (canonical2888 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA10 + difference 1 4) (sourceB10 + difference 4 1) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA10 + difference 1 4) (sourceB10 + difference 4 1) sourceC10) = raw2889 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2889; decide +kernel
    rw [ha]
    exact (canonical2889 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA10 + difference 1 5) (sourceB10 + difference 5 1) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA10 + difference 1 5) (sourceB10 + difference 5 1) sourceC10) = raw2890 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2890; decide +kernel
    rw [ha]
    exact (canonical2890 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA10 + difference 2 0) (sourceB10 + difference 0 2) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA10 + difference 2 0) (sourceB10 + difference 0 2) sourceC10) = raw2891 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2891; decide +kernel
    rw [ha]
    exact (canonical2891 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA10 + difference 2 1) (sourceB10 + difference 1 2) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA10 + difference 2 1) (sourceB10 + difference 1 2) sourceC10) = raw2892 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2892; decide +kernel
    rw [ha]
    exact (canonical2892 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA10 + difference 2 3) (sourceB10 + difference 3 2) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA10 + difference 2 3) (sourceB10 + difference 3 2) sourceC10) = raw2893 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2893; decide +kernel
    rw [ha]
    exact (canonical2893 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA10 + difference 2 4) (sourceB10 + difference 4 2) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA10 + difference 2 4) (sourceB10 + difference 4 2) sourceC10) = raw2894 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2894; decide +kernel
    rw [ha]
    exact (canonical2894 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA10 + difference 2 5) (sourceB10 + difference 5 2) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA10 + difference 2 5) (sourceB10 + difference 5 2) sourceC10) = raw2895 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2895; decide +kernel
    rw [ha]
    exact (canonical2895 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA10 + difference 3 0) (sourceB10 + difference 0 3) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA10 + difference 3 0) (sourceB10 + difference 0 3) sourceC10) = raw2896 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2896; decide +kernel
    rw [ha]
    exact (canonical2896 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA10 + difference 3 1) (sourceB10 + difference 1 3) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA10 + difference 3 1) (sourceB10 + difference 1 3) sourceC10) = raw2897 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2897; decide +kernel
    rw [ha]
    exact (canonical2897 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA10 + difference 3 2) (sourceB10 + difference 2 3) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA10 + difference 3 2) (sourceB10 + difference 2 3) sourceC10) = raw2898 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2898; decide +kernel
    rw [ha]
    exact (canonical2898 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA10 + difference 3 4) (sourceB10 + difference 4 3) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA10 + difference 3 4) (sourceB10 + difference 4 3) sourceC10) = raw2899 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2899; decide +kernel
    rw [ha]
    exact (canonical2899 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA10 + difference 3 5) (sourceB10 + difference 5 3) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA10 + difference 3 5) (sourceB10 + difference 5 3) sourceC10) = raw2900 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2900; decide +kernel
    rw [ha]
    exact (canonical2900 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA10 + difference 4 0) (sourceB10 + difference 0 4) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4094) := by
    have ha : (tripleCharges (sourceA10 + difference 4 0) (sourceB10 + difference 0 4) sourceC10) = raw2901 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2901; decide +kernel
    rw [ha]
    exact (canonical2901 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA10 + difference 4 1) (sourceB10 + difference 1 4) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA10 + difference 4 1) (sourceB10 + difference 1 4) sourceC10) = raw2843 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2843; decide +kernel
    rw [ha]
    exact (canonical2843 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA10 + difference 4 2) (sourceB10 + difference 2 4) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA10 + difference 4 2) (sourceB10 + difference 2 4) sourceC10) = raw2902 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2902; decide +kernel
    rw [ha]
    exact (canonical2902 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA10 + difference 4 3) (sourceB10 + difference 3 4) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA10 + difference 4 3) (sourceB10 + difference 3 4) sourceC10) = raw2903 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2903; decide +kernel
    rw [ha]
    exact (canonical2903 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA10 + difference 4 5) (sourceB10 + difference 5 4) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5496) := by
    have ha : (tripleCharges (sourceA10 + difference 4 5) (sourceB10 + difference 5 4) sourceC10) = raw2825 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2825; decide +kernel
    rw [ha]
    exact (canonical2825 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA10 + difference 5 0) (sourceB10 + difference 0 5) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA10 + difference 5 0) (sourceB10 + difference 0 5) sourceC10) = raw2904 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2904; decide +kernel
    rw [ha]
    exact (canonical2904 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA10 + difference 5 1) (sourceB10 + difference 1 5) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA10 + difference 5 1) (sourceB10 + difference 1 5) sourceC10) = raw2905 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2905; decide +kernel
    rw [ha]
    exact (canonical2905 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA10 + difference 5 2) (sourceB10 + difference 2 5) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA10 + difference 5 2) (sourceB10 + difference 2 5) sourceC10) = raw2906 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2906; decide +kernel
    rw [ha]
    exact (canonical2906 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA10 + difference 5 3) (sourceB10 + difference 3 5) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA10 + difference 5 3) (sourceB10 + difference 3 5) sourceC10) = raw2907 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2907; decide +kernel
    rw [ha]
    exact (canonical2907 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA10 + difference 5 4) (sourceB10 + difference 4 5) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA10 + difference 5 4) (sourceB10 + difference 4 5) sourceC10) = raw2908 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2908; decide +kernel
    rw [ha]
    exact (canonical2908 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA10 sourceB10 sourceC10
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm10, Integer.Sparse.eval]
  linarith only [hs]

def sourceA11 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB11 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC11 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm11 : Integer.Sparse Master := [(Sum.inr 4084, 8), (Sum.inr 4085, 1), (Sum.inr 4092, 12), (Sum.inr 4093, 8), (Sum.inr 4097, 1)]

theorem sourceEq11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm11 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA11 + difference 0 1) (sourceB11 + difference 1 0) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 0 1) (sourceB11 + difference 1 0) sourceC11) = raw2909 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2909; decide +kernel
    rw [ha]
    exact (canonical2909 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA11 + difference 0 2) (sourceB11 + difference 2 0) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 0 2) (sourceB11 + difference 2 0) sourceC11) = raw2910 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2910; decide +kernel
    rw [ha]
    exact (canonical2910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA11 + difference 0 3) (sourceB11 + difference 3 0) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 0 3) (sourceB11 + difference 3 0) sourceC11) = raw2911 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2911; decide +kernel
    rw [ha]
    exact (canonical2911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA11 + difference 0 4) (sourceB11 + difference 4 0) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 0 4) (sourceB11 + difference 4 0) sourceC11) = raw2912 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2912; decide +kernel
    rw [ha]
    exact (canonical2912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA11 + difference 0 5) (sourceB11 + difference 5 0) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4097) := by
    have ha : (tripleCharges (sourceA11 + difference 0 5) (sourceB11 + difference 5 0) sourceC11) = raw2913 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2913; decide +kernel
    rw [ha]
    exact (canonical2913 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA11 + difference 1 0) (sourceB11 + difference 0 1) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 1 0) (sourceB11 + difference 0 1) sourceC11) = raw2914 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2914; decide +kernel
    rw [ha]
    exact (canonical2914 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA11 + difference 1 2) (sourceB11 + difference 2 1) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 1 2) (sourceB11 + difference 2 1) sourceC11) = raw2915 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2915; decide +kernel
    rw [ha]
    exact (canonical2915 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA11 + difference 1 3) (sourceB11 + difference 3 1) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 1 3) (sourceB11 + difference 3 1) sourceC11) = raw2916 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2916; decide +kernel
    rw [ha]
    exact (canonical2916 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA11 + difference 1 4) (sourceB11 + difference 4 1) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 1 4) (sourceB11 + difference 4 1) sourceC11) = raw2917 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2917; decide +kernel
    rw [ha]
    exact (canonical2917 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA11 + difference 1 5) (sourceB11 + difference 5 1) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 1 5) (sourceB11 + difference 5 1) sourceC11) = raw2918 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2918; decide +kernel
    rw [ha]
    exact (canonical2918 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA11 + difference 2 0) (sourceB11 + difference 0 2) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 2 0) (sourceB11 + difference 0 2) sourceC11) = raw2919 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2919; decide +kernel
    rw [ha]
    exact (canonical2919 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA11 + difference 2 1) (sourceB11 + difference 1 2) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 2 1) (sourceB11 + difference 1 2) sourceC11) = raw2920 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2920; decide +kernel
    rw [ha]
    exact (canonical2920 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA11 + difference 2 3) (sourceB11 + difference 3 2) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 2 3) (sourceB11 + difference 3 2) sourceC11) = raw2921 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2921; decide +kernel
    rw [ha]
    exact (canonical2921 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA11 + difference 2 4) (sourceB11 + difference 4 2) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 2 4) (sourceB11 + difference 4 2) sourceC11) = raw2922 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2922; decide +kernel
    rw [ha]
    exact (canonical2922 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA11 + difference 2 5) (sourceB11 + difference 5 2) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 2 5) (sourceB11 + difference 5 2) sourceC11) = raw2923 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2923; decide +kernel
    rw [ha]
    exact (canonical2923 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA11 + difference 3 0) (sourceB11 + difference 0 3) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 3 0) (sourceB11 + difference 0 3) sourceC11) = raw2924 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2924; decide +kernel
    rw [ha]
    exact (canonical2924 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA11 + difference 3 1) (sourceB11 + difference 1 3) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 3 1) (sourceB11 + difference 1 3) sourceC11) = raw2925 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2925; decide +kernel
    rw [ha]
    exact (canonical2925 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA11 + difference 3 2) (sourceB11 + difference 2 3) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 3 2) (sourceB11 + difference 2 3) sourceC11) = raw2926 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2926; decide +kernel
    rw [ha]
    exact (canonical2926 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA11 + difference 3 4) (sourceB11 + difference 4 3) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 3 4) (sourceB11 + difference 4 3) sourceC11) = raw2927 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2927; decide +kernel
    rw [ha]
    exact (canonical2927 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA11 + difference 3 5) (sourceB11 + difference 5 3) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 3 5) (sourceB11 + difference 5 3) sourceC11) = raw2928 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2928; decide +kernel
    rw [ha]
    exact (canonical2928 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA11 + difference 4 0) (sourceB11 + difference 0 4) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 4 0) (sourceB11 + difference 0 4) sourceC11) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA11 + difference 4 1) (sourceB11 + difference 1 4) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 4 1) (sourceB11 + difference 1 4) sourceC11) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA11 + difference 4 2) (sourceB11 + difference 2 4) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 4 2) (sourceB11 + difference 2 4) sourceC11) = raw2931 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2931; decide +kernel
    rw [ha]
    exact (canonical2931 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA11 + difference 4 3) (sourceB11 + difference 3 4) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA11 + difference 4 3) (sourceB11 + difference 3 4) sourceC11) = raw2932 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2932; decide +kernel
    rw [ha]
    exact (canonical2932 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA11 + difference 4 5) (sourceB11 + difference 5 4) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA11 + difference 4 5) (sourceB11 + difference 5 4) sourceC11) = raw2933 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2933; decide +kernel
    rw [ha]
    exact (canonical2933 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA11 + difference 5 0) (sourceB11 + difference 0 5) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA11 + difference 5 0) (sourceB11 + difference 0 5) sourceC11) = raw2934 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2934; decide +kernel
    rw [ha]
    exact (canonical2934 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA11 + difference 5 1) (sourceB11 + difference 1 5) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 5 1) (sourceB11 + difference 1 5) sourceC11) = raw2935 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2935; decide +kernel
    rw [ha]
    exact (canonical2935 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA11 + difference 5 2) (sourceB11 + difference 2 5) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 5 2) (sourceB11 + difference 2 5) sourceC11) = raw2936 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2936; decide +kernel
    rw [ha]
    exact (canonical2936 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA11 + difference 5 3) (sourceB11 + difference 3 5) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 5 3) (sourceB11 + difference 3 5) sourceC11) = raw2937 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2937; decide +kernel
    rw [ha]
    exact (canonical2937 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA11 + difference 5 4) (sourceB11 + difference 4 5) sourceC11) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA11 + difference 5 4) (sourceB11 + difference 4 5) sourceC11) = raw2938 := by
      apply Matrix.ext; unfold tripleCharges sourceA11 sourceB11 sourceC11 difference raw2938; decide +kernel
    rw [ha]
    exact (canonical2938 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA11 sourceB11 sourceC11
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm11, Integer.Sparse.eval]
  linarith only [hs]

def sourceA12 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB12 : Charge := ![0, 0, 1, 1, -1, -1]
def sourceC12 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceForm12 : Integer.Sparse Master := [(Sum.inr 5283, 1), (Sum.inr 5284, 2), (Sum.inr 5292, 2), (Sum.inr 5406, 2), (Sum.inr 5411, 4), (Sum.inr 5433, 2), (Sum.inr 5447, 2), (Sum.inr 5450, 2), (Sum.inr 5452, 2), (Sum.inr 5453, 2), (Sum.inr 5454, 4), (Sum.inr 5485, 2), (Sum.inr 5489, 1), (Sum.inr 5493, 2)]

theorem sourceEq12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm12 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA12 + difference 0 1) (sourceB12 + difference 1 0) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA12 + difference 0 1) (sourceB12 + difference 1 0) sourceC12) = raw2939 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2939; decide +kernel
    rw [ha]
    exact (canonical2939 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA12 + difference 0 2) (sourceB12 + difference 2 0) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA12 + difference 0 2) (sourceB12 + difference 2 0) sourceC12) = raw2940 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2940; decide +kernel
    rw [ha]
    exact (canonical2940 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA12 + difference 0 3) (sourceB12 + difference 3 0) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA12 + difference 0 3) (sourceB12 + difference 3 0) sourceC12) = raw2941 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2941; decide +kernel
    rw [ha]
    exact (canonical2941 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA12 + difference 0 4) (sourceB12 + difference 4 0) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA12 + difference 0 4) (sourceB12 + difference 4 0) sourceC12) = raw2942 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2942; decide +kernel
    rw [ha]
    exact (canonical2942 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA12 + difference 0 5) (sourceB12 + difference 5 0) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA12 + difference 0 5) (sourceB12 + difference 5 0) sourceC12) = raw2943 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2943; decide +kernel
    rw [ha]
    exact (canonical2943 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA12 + difference 1 0) (sourceB12 + difference 0 1) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA12 + difference 1 0) (sourceB12 + difference 0 1) sourceC12) = raw2944 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2944; decide +kernel
    rw [ha]
    exact (canonical2944 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA12 + difference 1 2) (sourceB12 + difference 2 1) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA12 + difference 1 2) (sourceB12 + difference 2 1) sourceC12) = raw2945 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2945; decide +kernel
    rw [ha]
    exact (canonical2945 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA12 + difference 1 3) (sourceB12 + difference 3 1) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA12 + difference 1 3) (sourceB12 + difference 3 1) sourceC12) = raw2946 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2946; decide +kernel
    rw [ha]
    exact (canonical2946 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA12 + difference 1 4) (sourceB12 + difference 4 1) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA12 + difference 1 4) (sourceB12 + difference 4 1) sourceC12) = raw2947 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2947; decide +kernel
    rw [ha]
    exact (canonical2947 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA12 + difference 1 5) (sourceB12 + difference 5 1) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA12 + difference 1 5) (sourceB12 + difference 5 1) sourceC12) = raw2948 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2948; decide +kernel
    rw [ha]
    exact (canonical2948 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA12 + difference 2 0) (sourceB12 + difference 0 2) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA12 + difference 2 0) (sourceB12 + difference 0 2) sourceC12) = raw2949 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2949; decide +kernel
    rw [ha]
    exact (canonical2949 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA12 + difference 2 1) (sourceB12 + difference 1 2) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA12 + difference 2 1) (sourceB12 + difference 1 2) sourceC12) = raw2950 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2950; decide +kernel
    rw [ha]
    exact (canonical2950 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA12 + difference 2 3) (sourceB12 + difference 3 2) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA12 + difference 2 3) (sourceB12 + difference 3 2) sourceC12) = raw2951 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2951; decide +kernel
    rw [ha]
    exact (canonical2951 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA12 + difference 2 4) (sourceB12 + difference 4 2) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA12 + difference 2 4) (sourceB12 + difference 4 2) sourceC12) = raw2952 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2952; decide +kernel
    rw [ha]
    exact (canonical2952 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA12 + difference 2 5) (sourceB12 + difference 5 2) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA12 + difference 2 5) (sourceB12 + difference 5 2) sourceC12) = raw2953 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2953; decide +kernel
    rw [ha]
    exact (canonical2953 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA12 + difference 3 0) (sourceB12 + difference 0 3) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA12 + difference 3 0) (sourceB12 + difference 0 3) sourceC12) = raw2954 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2954; decide +kernel
    rw [ha]
    exact (canonical2954 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA12 + difference 3 1) (sourceB12 + difference 1 3) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA12 + difference 3 1) (sourceB12 + difference 1 3) sourceC12) = raw2955 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2955; decide +kernel
    rw [ha]
    exact (canonical2955 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA12 + difference 3 2) (sourceB12 + difference 2 3) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA12 + difference 3 2) (sourceB12 + difference 2 3) sourceC12) = raw2956 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2956; decide +kernel
    rw [ha]
    exact (canonical2956 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA12 + difference 3 4) (sourceB12 + difference 4 3) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA12 + difference 3 4) (sourceB12 + difference 4 3) sourceC12) = raw2957 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2957; decide +kernel
    rw [ha]
    exact (canonical2957 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA12 + difference 3 5) (sourceB12 + difference 5 3) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA12 + difference 3 5) (sourceB12 + difference 5 3) sourceC12) = raw2958 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2958; decide +kernel
    rw [ha]
    exact (canonical2958 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA12 + difference 4 0) (sourceB12 + difference 0 4) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA12 + difference 4 0) (sourceB12 + difference 0 4) sourceC12) = raw2959 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2959; decide +kernel
    rw [ha]
    exact (canonical2959 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA12 + difference 4 1) (sourceB12 + difference 1 4) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA12 + difference 4 1) (sourceB12 + difference 1 4) sourceC12) = raw2960 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2960; decide +kernel
    rw [ha]
    exact (canonical2960 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA12 + difference 4 2) (sourceB12 + difference 2 4) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA12 + difference 4 2) (sourceB12 + difference 2 4) sourceC12) = raw2961 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2961; decide +kernel
    rw [ha]
    exact (canonical2961 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA12 + difference 4 3) (sourceB12 + difference 3 4) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA12 + difference 4 3) (sourceB12 + difference 3 4) sourceC12) = raw2962 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2962; decide +kernel
    rw [ha]
    exact (canonical2962 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA12 + difference 4 5) (sourceB12 + difference 5 4) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA12 + difference 4 5) (sourceB12 + difference 5 4) sourceC12) = raw2963 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2963; decide +kernel
    rw [ha]
    exact (canonical2963 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA12 + difference 5 0) (sourceB12 + difference 0 5) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA12 + difference 5 0) (sourceB12 + difference 0 5) sourceC12) = raw2964 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2964; decide +kernel
    rw [ha]
    exact (canonical2964 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA12 + difference 5 1) (sourceB12 + difference 1 5) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA12 + difference 5 1) (sourceB12 + difference 1 5) sourceC12) = raw2965 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2965; decide +kernel
    rw [ha]
    exact (canonical2965 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA12 + difference 5 2) (sourceB12 + difference 2 5) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA12 + difference 5 2) (sourceB12 + difference 2 5) sourceC12) = raw2966 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2966; decide +kernel
    rw [ha]
    exact (canonical2966 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA12 + difference 5 3) (sourceB12 + difference 3 5) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA12 + difference 5 3) (sourceB12 + difference 3 5) sourceC12) = raw2967 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2967; decide +kernel
    rw [ha]
    exact (canonical2967 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA12 + difference 5 4) (sourceB12 + difference 4 5) sourceC12) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA12 + difference 5 4) (sourceB12 + difference 4 5) sourceC12) = raw2968 := by
      apply Matrix.ext; unfold tripleCharges sourceA12 sourceB12 sourceC12 difference raw2968; decide +kernel
    rw [ha]
    exact (canonical2968 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA12 sourceB12 sourceC12
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm12, Integer.Sparse.eval]
  linarith only [hs]

def sourceA13 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB13 : Charge := ![0, 0, 1, 1, -1, -1]
def sourceC13 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceForm13 : Integer.Sparse Master := [(Sum.inr 3076, 1), (Sum.inr 3077, 2), (Sum.inr 3100, 2), (Sum.inr 3801, 2), (Sum.inr 3809, 4), (Sum.inr 3912, 2), (Sum.inr 4009, 1), (Sum.inr 4010, 2), (Sum.inr 4016, 2), (Sum.inr 4025, 2), (Sum.inr 4029, 2), (Sum.inr 4033, 2), (Sum.inr 4039, 2), (Sum.inr 4040, 4)]

theorem sourceEq13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm13 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA13 + difference 0 1) (sourceB13 + difference 1 0) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4009) := by
    have ha : (tripleCharges (sourceA13 + difference 0 1) (sourceB13 + difference 1 0) sourceC13) = raw2969 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2969; decide +kernel
    rw [ha]
    exact (canonical2969 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA13 + difference 0 2) (sourceB13 + difference 2 0) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA13 + difference 0 2) (sourceB13 + difference 2 0) sourceC13) = raw2970 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2970; decide +kernel
    rw [ha]
    exact (canonical2970 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA13 + difference 0 3) (sourceB13 + difference 3 0) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA13 + difference 0 3) (sourceB13 + difference 3 0) sourceC13) = raw2971 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2971; decide +kernel
    rw [ha]
    exact (canonical2971 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA13 + difference 0 4) (sourceB13 + difference 4 0) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4016) := by
    have ha : (tripleCharges (sourceA13 + difference 0 4) (sourceB13 + difference 4 0) sourceC13) = raw2972 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2972; decide +kernel
    rw [ha]
    exact (canonical2972 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA13 + difference 0 5) (sourceB13 + difference 5 0) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4016) := by
    have ha : (tripleCharges (sourceA13 + difference 0 5) (sourceB13 + difference 5 0) sourceC13) = raw2973 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2973; decide +kernel
    rw [ha]
    exact (canonical2973 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA13 + difference 1 0) (sourceB13 + difference 0 1) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3076) := by
    have ha : (tripleCharges (sourceA13 + difference 1 0) (sourceB13 + difference 0 1) sourceC13) = raw2974 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2974; decide +kernel
    rw [ha]
    exact (canonical2974 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA13 + difference 1 2) (sourceB13 + difference 2 1) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4025) := by
    have ha : (tripleCharges (sourceA13 + difference 1 2) (sourceB13 + difference 2 1) sourceC13) = raw2975 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2975; decide +kernel
    rw [ha]
    exact (canonical2975 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA13 + difference 1 3) (sourceB13 + difference 3 1) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4025) := by
    have ha : (tripleCharges (sourceA13 + difference 1 3) (sourceB13 + difference 3 1) sourceC13) = raw2976 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2976; decide +kernel
    rw [ha]
    exact (canonical2976 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA13 + difference 1 4) (sourceB13 + difference 4 1) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4039) := by
    have ha : (tripleCharges (sourceA13 + difference 1 4) (sourceB13 + difference 4 1) sourceC13) = raw2977 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2977; decide +kernel
    rw [ha]
    exact (canonical2977 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA13 + difference 1 5) (sourceB13 + difference 5 1) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4039) := by
    have ha : (tripleCharges (sourceA13 + difference 1 5) (sourceB13 + difference 5 1) sourceC13) = raw2978 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2978; decide +kernel
    rw [ha]
    exact (canonical2978 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA13 + difference 2 0) (sourceB13 + difference 0 2) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA13 + difference 2 0) (sourceB13 + difference 0 2) sourceC13) = raw2979 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2979; decide +kernel
    rw [ha]
    exact (canonical2979 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA13 + difference 2 1) (sourceB13 + difference 1 2) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA13 + difference 2 1) (sourceB13 + difference 1 2) sourceC13) = raw2980 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2980; decide +kernel
    rw [ha]
    exact (canonical2980 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA13 + difference 2 3) (sourceB13 + difference 3 2) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA13 + difference 2 3) (sourceB13 + difference 3 2) sourceC13) = raw2981 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2981; decide +kernel
    rw [ha]
    exact (canonical2981 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA13 + difference 2 4) (sourceB13 + difference 4 2) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4040) := by
    have ha : (tripleCharges (sourceA13 + difference 2 4) (sourceB13 + difference 4 2) sourceC13) = raw2982 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2982; decide +kernel
    rw [ha]
    exact (canonical2982 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA13 + difference 2 5) (sourceB13 + difference 5 2) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4040) := by
    have ha : (tripleCharges (sourceA13 + difference 2 5) (sourceB13 + difference 5 2) sourceC13) = raw2983 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2983; decide +kernel
    rw [ha]
    exact (canonical2983 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA13 + difference 3 0) (sourceB13 + difference 0 3) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA13 + difference 3 0) (sourceB13 + difference 0 3) sourceC13) = raw2984 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2984; decide +kernel
    rw [ha]
    exact (canonical2984 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA13 + difference 3 1) (sourceB13 + difference 1 3) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA13 + difference 3 1) (sourceB13 + difference 1 3) sourceC13) = raw2985 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2985; decide +kernel
    rw [ha]
    exact (canonical2985 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA13 + difference 3 2) (sourceB13 + difference 2 3) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA13 + difference 3 2) (sourceB13 + difference 2 3) sourceC13) = raw2986 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2986; decide +kernel
    rw [ha]
    exact (canonical2986 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA13 + difference 3 4) (sourceB13 + difference 4 3) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4040) := by
    have ha : (tripleCharges (sourceA13 + difference 3 4) (sourceB13 + difference 4 3) sourceC13) = raw2987 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2987; decide +kernel
    rw [ha]
    exact (canonical2987 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA13 + difference 3 5) (sourceB13 + difference 5 3) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4040) := by
    have ha : (tripleCharges (sourceA13 + difference 3 5) (sourceB13 + difference 5 3) sourceC13) = raw2988 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2988; decide +kernel
    rw [ha]
    exact (canonical2988 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA13 + difference 4 0) (sourceB13 + difference 0 4) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA13 + difference 4 0) (sourceB13 + difference 0 4) sourceC13) = raw2989 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2989; decide +kernel
    rw [ha]
    exact (canonical2989 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA13 + difference 4 1) (sourceB13 + difference 1 4) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA13 + difference 4 1) (sourceB13 + difference 1 4) sourceC13) = raw2990 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2990; decide +kernel
    rw [ha]
    exact (canonical2990 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA13 + difference 4 2) (sourceB13 + difference 2 4) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA13 + difference 4 2) (sourceB13 + difference 2 4) sourceC13) = raw2991 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2991; decide +kernel
    rw [ha]
    exact (canonical2991 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA13 + difference 4 3) (sourceB13 + difference 3 4) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA13 + difference 4 3) (sourceB13 + difference 3 4) sourceC13) = raw2992 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2992; decide +kernel
    rw [ha]
    exact (canonical2992 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA13 + difference 4 5) (sourceB13 + difference 5 4) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3912) := by
    have ha : (tripleCharges (sourceA13 + difference 4 5) (sourceB13 + difference 5 4) sourceC13) = raw2993 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2993; decide +kernel
    rw [ha]
    exact (canonical2993 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA13 + difference 5 0) (sourceB13 + difference 0 5) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA13 + difference 5 0) (sourceB13 + difference 0 5) sourceC13) = raw2994 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2994; decide +kernel
    rw [ha]
    exact (canonical2994 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA13 + difference 5 1) (sourceB13 + difference 1 5) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA13 + difference 5 1) (sourceB13 + difference 1 5) sourceC13) = raw2995 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2995; decide +kernel
    rw [ha]
    exact (canonical2995 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA13 + difference 5 2) (sourceB13 + difference 2 5) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA13 + difference 5 2) (sourceB13 + difference 2 5) sourceC13) = raw2996 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2996; decide +kernel
    rw [ha]
    exact (canonical2996 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA13 + difference 5 3) (sourceB13 + difference 3 5) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA13 + difference 5 3) (sourceB13 + difference 3 5) sourceC13) = raw2997 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2997; decide +kernel
    rw [ha]
    exact (canonical2997 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA13 + difference 5 4) (sourceB13 + difference 4 5) sourceC13) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3912) := by
    have ha : (tripleCharges (sourceA13 + difference 5 4) (sourceB13 + difference 4 5) sourceC13) = raw2998 := by
      apply Matrix.ext; unfold tripleCharges sourceA13 sourceB13 sourceC13 difference raw2998; decide +kernel
    rw [ha]
    exact (canonical2998 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA13 sourceB13 sourceC13
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm13, Integer.Sparse.eval]
  linarith only [hs]

def sourceA14 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB14 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC14 : Charge := ![0, 0, 1, 1, -1, -1]
def sourceForm14 : Integer.Sparse Master := [(Sum.inr 4887, 1), (Sum.inr 4888, 4), (Sum.inr 5405, 4), (Sum.inr 5433, 4), (Sum.inr 5434, 8), (Sum.inr 5439, 4), (Sum.inr 5498, 1), (Sum.inr 5499, 4)]

theorem sourceEq14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm14 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA14 + difference 0 1) (sourceB14 + difference 1 0) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5498) := by
    have ha : (tripleCharges (sourceA14 + difference 0 1) (sourceB14 + difference 1 0) sourceC14) = raw2999 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw2999; decide +kernel
    rw [ha]
    exact (canonical2999 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA14 + difference 0 2) (sourceB14 + difference 2 0) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA14 + difference 0 2) (sourceB14 + difference 2 0) sourceC14) = raw3000 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3000; decide +kernel
    rw [ha]
    exact (canonical3000 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA14 + difference 0 3) (sourceB14 + difference 3 0) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA14 + difference 0 3) (sourceB14 + difference 3 0) sourceC14) = raw3001 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3001; decide +kernel
    rw [ha]
    exact (canonical3001 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA14 + difference 0 4) (sourceB14 + difference 4 0) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA14 + difference 0 4) (sourceB14 + difference 4 0) sourceC14) = raw3002 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3002; decide +kernel
    rw [ha]
    exact (canonical3002 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA14 + difference 0 5) (sourceB14 + difference 5 0) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA14 + difference 0 5) (sourceB14 + difference 5 0) sourceC14) = raw3003 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3003; decide +kernel
    rw [ha]
    exact (canonical3003 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA14 + difference 1 0) (sourceB14 + difference 0 1) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA14 + difference 1 0) (sourceB14 + difference 0 1) sourceC14) = raw3004 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3004; decide +kernel
    rw [ha]
    exact (canonical3004 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA14 + difference 1 2) (sourceB14 + difference 2 1) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA14 + difference 1 2) (sourceB14 + difference 2 1) sourceC14) = raw3005 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3005; decide +kernel
    rw [ha]
    exact (canonical3005 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA14 + difference 1 3) (sourceB14 + difference 3 1) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA14 + difference 1 3) (sourceB14 + difference 3 1) sourceC14) = raw3006 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3006; decide +kernel
    rw [ha]
    exact (canonical3006 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA14 + difference 1 4) (sourceB14 + difference 4 1) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA14 + difference 1 4) (sourceB14 + difference 4 1) sourceC14) = raw3007 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3007; decide +kernel
    rw [ha]
    exact (canonical3007 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA14 + difference 1 5) (sourceB14 + difference 5 1) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA14 + difference 1 5) (sourceB14 + difference 5 1) sourceC14) = raw3008 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3008; decide +kernel
    rw [ha]
    exact (canonical3008 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA14 + difference 2 0) (sourceB14 + difference 0 2) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA14 + difference 2 0) (sourceB14 + difference 0 2) sourceC14) = raw3009 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3009; decide +kernel
    rw [ha]
    exact (canonical3009 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA14 + difference 2 1) (sourceB14 + difference 1 2) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA14 + difference 2 1) (sourceB14 + difference 1 2) sourceC14) = raw3010 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3010; decide +kernel
    rw [ha]
    exact (canonical3010 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA14 + difference 2 3) (sourceB14 + difference 3 2) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA14 + difference 2 3) (sourceB14 + difference 3 2) sourceC14) = raw3011 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3011; decide +kernel
    rw [ha]
    exact (canonical3011 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA14 + difference 2 4) (sourceB14 + difference 4 2) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA14 + difference 2 4) (sourceB14 + difference 4 2) sourceC14) = raw3012 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3012; decide +kernel
    rw [ha]
    exact (canonical3012 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA14 + difference 2 5) (sourceB14 + difference 5 2) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA14 + difference 2 5) (sourceB14 + difference 5 2) sourceC14) = raw3013 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3013; decide +kernel
    rw [ha]
    exact (canonical3013 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA14 + difference 3 0) (sourceB14 + difference 0 3) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA14 + difference 3 0) (sourceB14 + difference 0 3) sourceC14) = raw3014 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3014; decide +kernel
    rw [ha]
    exact (canonical3014 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA14 + difference 3 1) (sourceB14 + difference 1 3) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA14 + difference 3 1) (sourceB14 + difference 1 3) sourceC14) = raw3015 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3015; decide +kernel
    rw [ha]
    exact (canonical3015 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA14 + difference 3 2) (sourceB14 + difference 2 3) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA14 + difference 3 2) (sourceB14 + difference 2 3) sourceC14) = raw3016 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3016; decide +kernel
    rw [ha]
    exact (canonical3016 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA14 + difference 3 4) (sourceB14 + difference 4 3) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA14 + difference 3 4) (sourceB14 + difference 4 3) sourceC14) = raw3017 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3017; decide +kernel
    rw [ha]
    exact (canonical3017 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA14 + difference 3 5) (sourceB14 + difference 5 3) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA14 + difference 3 5) (sourceB14 + difference 5 3) sourceC14) = raw3018 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3018; decide +kernel
    rw [ha]
    exact (canonical3018 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA14 + difference 4 0) (sourceB14 + difference 0 4) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA14 + difference 4 0) (sourceB14 + difference 0 4) sourceC14) = raw3019 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3019; decide +kernel
    rw [ha]
    exact (canonical3019 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA14 + difference 4 1) (sourceB14 + difference 1 4) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA14 + difference 4 1) (sourceB14 + difference 1 4) sourceC14) = raw3020 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3020; decide +kernel
    rw [ha]
    exact (canonical3020 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA14 + difference 4 2) (sourceB14 + difference 2 4) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA14 + difference 4 2) (sourceB14 + difference 2 4) sourceC14) = raw3021 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3021; decide +kernel
    rw [ha]
    exact (canonical3021 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA14 + difference 4 3) (sourceB14 + difference 3 4) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA14 + difference 4 3) (sourceB14 + difference 3 4) sourceC14) = raw3022 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3022; decide +kernel
    rw [ha]
    exact (canonical3022 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA14 + difference 4 5) (sourceB14 + difference 5 4) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA14 + difference 4 5) (sourceB14 + difference 5 4) sourceC14) = raw3023 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3023; decide +kernel
    rw [ha]
    exact (canonical3023 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA14 + difference 5 0) (sourceB14 + difference 0 5) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA14 + difference 5 0) (sourceB14 + difference 0 5) sourceC14) = raw3024 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3024; decide +kernel
    rw [ha]
    exact (canonical3024 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA14 + difference 5 1) (sourceB14 + difference 1 5) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA14 + difference 5 1) (sourceB14 + difference 1 5) sourceC14) = raw3025 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3025; decide +kernel
    rw [ha]
    exact (canonical3025 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA14 + difference 5 2) (sourceB14 + difference 2 5) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA14 + difference 5 2) (sourceB14 + difference 2 5) sourceC14) = raw3026 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3026; decide +kernel
    rw [ha]
    exact (canonical3026 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA14 + difference 5 3) (sourceB14 + difference 3 5) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA14 + difference 5 3) (sourceB14 + difference 3 5) sourceC14) = raw3027 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3027; decide +kernel
    rw [ha]
    exact (canonical3027 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA14 + difference 5 4) (sourceB14 + difference 4 5) sourceC14) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA14 + difference 5 4) (sourceB14 + difference 4 5) sourceC14) = raw3028 := by
      apply Matrix.ext; unfold tripleCharges sourceA14 sourceB14 sourceC14 difference raw3028; decide +kernel
    rw [ha]
    exact (canonical3028 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA14 sourceB14 sourceC14
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm14, Integer.Sparse.eval]
  linarith only [hs]

def sourceA15 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB15 : Charge := ![1, -1, 0, 0, -1, 1]
def sourceC15 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm15 : Integer.Sparse Master := [(Sum.inr 5290, 2), (Sum.inr 5291, 1), (Sum.inr 5294, 1), (Sum.inr 5304, 1), (Sum.inr 5434, 2), (Sum.inr 5438, 2), (Sum.inr 5442, 1), (Sum.inr 5443, 1), (Sum.inr 5450, 2), (Sum.inr 5451, 2), (Sum.inr 5454, 1), (Sum.inr 5455, 1), (Sum.inr 5481, 2), (Sum.inr 5484, 2), (Sum.inr 5485, 2), (Sum.inr 5490, 2), (Sum.inr 5492, 2), (Sum.inr 5493, 1), (Sum.inr 5494, 1), (Sum.inr 5495, 1)]

theorem sourceEq15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm15 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA15 + difference 0 1) (sourceB15 + difference 1 0) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA15 + difference 0 1) (sourceB15 + difference 1 0) sourceC15) = raw3029 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3029; decide +kernel
    rw [ha]
    exact (canonical3029 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA15 + difference 0 2) (sourceB15 + difference 2 0) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA15 + difference 0 2) (sourceB15 + difference 2 0) sourceC15) = raw3030 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3030; decide +kernel
    rw [ha]
    exact (canonical3030 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA15 + difference 0 3) (sourceB15 + difference 3 0) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA15 + difference 0 3) (sourceB15 + difference 3 0) sourceC15) = raw3031 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3031; decide +kernel
    rw [ha]
    exact (canonical3031 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA15 + difference 0 4) (sourceB15 + difference 4 0) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5495) := by
    have ha : (tripleCharges (sourceA15 + difference 0 4) (sourceB15 + difference 4 0) sourceC15) = raw3032 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3032; decide +kernel
    rw [ha]
    exact (canonical3032 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA15 + difference 0 5) (sourceB15 + difference 5 0) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA15 + difference 0 5) (sourceB15 + difference 5 0) sourceC15) = raw3033 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3033; decide +kernel
    rw [ha]
    exact (canonical3033 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA15 + difference 1 0) (sourceB15 + difference 0 1) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA15 + difference 1 0) (sourceB15 + difference 0 1) sourceC15) = raw3034 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3034; decide +kernel
    rw [ha]
    exact (canonical3034 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA15 + difference 1 2) (sourceB15 + difference 2 1) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA15 + difference 1 2) (sourceB15 + difference 2 1) sourceC15) = raw3035 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3035; decide +kernel
    rw [ha]
    exact (canonical3035 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA15 + difference 1 3) (sourceB15 + difference 3 1) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA15 + difference 1 3) (sourceB15 + difference 3 1) sourceC15) = raw3036 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3036; decide +kernel
    rw [ha]
    exact (canonical3036 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA15 + difference 1 4) (sourceB15 + difference 4 1) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5494) := by
    have ha : (tripleCharges (sourceA15 + difference 1 4) (sourceB15 + difference 4 1) sourceC15) = raw3037 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3037; decide +kernel
    rw [ha]
    exact (canonical3037 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA15 + difference 1 5) (sourceB15 + difference 5 1) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA15 + difference 1 5) (sourceB15 + difference 5 1) sourceC15) = raw3038 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3038; decide +kernel
    rw [ha]
    exact (canonical3038 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA15 + difference 2 0) (sourceB15 + difference 0 2) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA15 + difference 2 0) (sourceB15 + difference 0 2) sourceC15) = raw3039 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3039; decide +kernel
    rw [ha]
    exact (canonical3039 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA15 + difference 2 1) (sourceB15 + difference 1 2) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA15 + difference 2 1) (sourceB15 + difference 1 2) sourceC15) = raw3040 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3040; decide +kernel
    rw [ha]
    exact (canonical3040 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA15 + difference 2 3) (sourceB15 + difference 3 2) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA15 + difference 2 3) (sourceB15 + difference 3 2) sourceC15) = raw3041 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3041; decide +kernel
    rw [ha]
    exact (canonical3041 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA15 + difference 2 4) (sourceB15 + difference 4 2) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA15 + difference 2 4) (sourceB15 + difference 4 2) sourceC15) = raw3042 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3042; decide +kernel
    rw [ha]
    exact (canonical3042 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA15 + difference 2 5) (sourceB15 + difference 5 2) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA15 + difference 2 5) (sourceB15 + difference 5 2) sourceC15) = raw3043 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3043; decide +kernel
    rw [ha]
    exact (canonical3043 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA15 + difference 3 0) (sourceB15 + difference 0 3) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA15 + difference 3 0) (sourceB15 + difference 0 3) sourceC15) = raw3044 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3044; decide +kernel
    rw [ha]
    exact (canonical3044 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA15 + difference 3 1) (sourceB15 + difference 1 3) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA15 + difference 3 1) (sourceB15 + difference 1 3) sourceC15) = raw3045 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3045; decide +kernel
    rw [ha]
    exact (canonical3045 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA15 + difference 3 2) (sourceB15 + difference 2 3) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA15 + difference 3 2) (sourceB15 + difference 2 3) sourceC15) = raw3046 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3046; decide +kernel
    rw [ha]
    exact (canonical3046 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA15 + difference 3 4) (sourceB15 + difference 4 3) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA15 + difference 3 4) (sourceB15 + difference 4 3) sourceC15) = raw3047 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3047; decide +kernel
    rw [ha]
    exact (canonical3047 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA15 + difference 3 5) (sourceB15 + difference 5 3) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA15 + difference 3 5) (sourceB15 + difference 5 3) sourceC15) = raw3048 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3048; decide +kernel
    rw [ha]
    exact (canonical3048 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA15 + difference 4 0) (sourceB15 + difference 0 4) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA15 + difference 4 0) (sourceB15 + difference 0 4) sourceC15) = raw3049 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3049; decide +kernel
    rw [ha]
    exact (canonical3049 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA15 + difference 4 1) (sourceB15 + difference 1 4) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA15 + difference 4 1) (sourceB15 + difference 1 4) sourceC15) = raw3050 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3050; decide +kernel
    rw [ha]
    exact (canonical3050 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA15 + difference 4 2) (sourceB15 + difference 2 4) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA15 + difference 4 2) (sourceB15 + difference 2 4) sourceC15) = raw3051 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3051; decide +kernel
    rw [ha]
    exact (canonical3051 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA15 + difference 4 3) (sourceB15 + difference 3 4) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA15 + difference 4 3) (sourceB15 + difference 3 4) sourceC15) = raw3052 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3052; decide +kernel
    rw [ha]
    exact (canonical3052 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA15 + difference 4 5) (sourceB15 + difference 5 4) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA15 + difference 4 5) (sourceB15 + difference 5 4) sourceC15) = raw3053 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3053; decide +kernel
    rw [ha]
    exact (canonical3053 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA15 + difference 5 0) (sourceB15 + difference 0 5) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA15 + difference 5 0) (sourceB15 + difference 0 5) sourceC15) = raw3054 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3054; decide +kernel
    rw [ha]
    exact (canonical3054 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA15 + difference 5 1) (sourceB15 + difference 1 5) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA15 + difference 5 1) (sourceB15 + difference 1 5) sourceC15) = raw3055 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3055; decide +kernel
    rw [ha]
    exact (canonical3055 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA15 + difference 5 2) (sourceB15 + difference 2 5) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA15 + difference 5 2) (sourceB15 + difference 2 5) sourceC15) = raw3056 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3056; decide +kernel
    rw [ha]
    exact (canonical3056 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA15 + difference 5 3) (sourceB15 + difference 3 5) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA15 + difference 5 3) (sourceB15 + difference 3 5) sourceC15) = raw3057 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3057; decide +kernel
    rw [ha]
    exact (canonical3057 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA15 + difference 5 4) (sourceB15 + difference 4 5) sourceC15) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA15 + difference 5 4) (sourceB15 + difference 4 5) sourceC15) = raw3058 := by
      apply Matrix.ext; unfold tripleCharges sourceA15 sourceB15 sourceC15 difference raw3058; decide +kernel
    rw [ha]
    exact (canonical3058 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA15 sourceB15 sourceC15
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm15, Integer.Sparse.eval]
  linarith only [hs]

def sourceA16 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB16 : Charge := ![1, -1, 0, 0, -1, 1]
def sourceC16 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm16 : Integer.Sparse Master := [(Sum.inr 2764, 2), (Sum.inr 2765, 1), (Sum.inr 2768, 1), (Sum.inr 2782, 1), (Sum.inr 3876, 2), (Sum.inr 3888, 1), (Sum.inr 3907, 1), (Sum.inr 3910, 2), (Sum.inr 3913, 1), (Sum.inr 3914, 1), (Sum.inr 3979, 2), (Sum.inr 3982, 2), (Sum.inr 3983, 2), (Sum.inr 3998, 2), (Sum.inr 4001, 1), (Sum.inr 4013, 2), (Sum.inr 4017, 2), (Sum.inr 4018, 1), (Sum.inr 4019, 1), (Sum.inr 4020, 1), (Sum.inr 4021, 1)]

theorem sourceEq16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm16 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA16 + difference 0 1) (sourceB16 + difference 1 0) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4018) := by
    have ha : (tripleCharges (sourceA16 + difference 0 1) (sourceB16 + difference 1 0) sourceC16) = raw3059 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3059; decide +kernel
    rw [ha]
    exact (canonical3059 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA16 + difference 0 2) (sourceB16 + difference 2 0) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA16 + difference 0 2) (sourceB16 + difference 2 0) sourceC16) = raw3060 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3060; decide +kernel
    rw [ha]
    exact (canonical3060 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA16 + difference 0 3) (sourceB16 + difference 3 0) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA16 + difference 0 3) (sourceB16 + difference 3 0) sourceC16) = raw3061 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3061; decide +kernel
    rw [ha]
    exact (canonical3061 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA16 + difference 0 4) (sourceB16 + difference 4 0) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4021) := by
    have ha : (tripleCharges (sourceA16 + difference 0 4) (sourceB16 + difference 4 0) sourceC16) = raw3062 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3062; decide +kernel
    rw [ha]
    exact (canonical3062 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA16 + difference 0 5) (sourceB16 + difference 5 0) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3914) := by
    have ha : (tripleCharges (sourceA16 + difference 0 5) (sourceB16 + difference 5 0) sourceC16) = raw3063 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3063; decide +kernel
    rw [ha]
    exact (canonical3063 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA16 + difference 1 0) (sourceB16 + difference 0 1) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA16 + difference 1 0) (sourceB16 + difference 0 1) sourceC16) = raw3064 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3064; decide +kernel
    rw [ha]
    exact (canonical3064 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA16 + difference 1 2) (sourceB16 + difference 2 1) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA16 + difference 1 2) (sourceB16 + difference 2 1) sourceC16) = raw3065 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3065; decide +kernel
    rw [ha]
    exact (canonical3065 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA16 + difference 1 3) (sourceB16 + difference 3 1) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA16 + difference 1 3) (sourceB16 + difference 3 1) sourceC16) = raw3066 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3066; decide +kernel
    rw [ha]
    exact (canonical3066 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA16 + difference 1 4) (sourceB16 + difference 4 1) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4020) := by
    have ha : (tripleCharges (sourceA16 + difference 1 4) (sourceB16 + difference 4 1) sourceC16) = raw3067 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3067; decide +kernel
    rw [ha]
    exact (canonical3067 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA16 + difference 1 5) (sourceB16 + difference 5 1) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA16 + difference 1 5) (sourceB16 + difference 5 1) sourceC16) = raw3068 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3068; decide +kernel
    rw [ha]
    exact (canonical3068 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA16 + difference 2 0) (sourceB16 + difference 0 2) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA16 + difference 2 0) (sourceB16 + difference 0 2) sourceC16) = raw3069 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3069; decide +kernel
    rw [ha]
    exact (canonical3069 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA16 + difference 2 1) (sourceB16 + difference 1 2) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA16 + difference 2 1) (sourceB16 + difference 1 2) sourceC16) = raw3070 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3070; decide +kernel
    rw [ha]
    exact (canonical3070 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA16 + difference 2 3) (sourceB16 + difference 3 2) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA16 + difference 2 3) (sourceB16 + difference 3 2) sourceC16) = raw3071 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3071; decide +kernel
    rw [ha]
    exact (canonical3071 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA16 + difference 2 4) (sourceB16 + difference 4 2) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4017) := by
    have ha : (tripleCharges (sourceA16 + difference 2 4) (sourceB16 + difference 4 2) sourceC16) = raw3072 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3072; decide +kernel
    rw [ha]
    exact (canonical3072 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA16 + difference 2 5) (sourceB16 + difference 5 2) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA16 + difference 2 5) (sourceB16 + difference 5 2) sourceC16) = raw3073 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3073; decide +kernel
    rw [ha]
    exact (canonical3073 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA16 + difference 3 0) (sourceB16 + difference 0 3) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA16 + difference 3 0) (sourceB16 + difference 0 3) sourceC16) = raw3074 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3074; decide +kernel
    rw [ha]
    exact (canonical3074 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA16 + difference 3 1) (sourceB16 + difference 1 3) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA16 + difference 3 1) (sourceB16 + difference 1 3) sourceC16) = raw3075 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3075; decide +kernel
    rw [ha]
    exact (canonical3075 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA16 + difference 3 2) (sourceB16 + difference 2 3) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA16 + difference 3 2) (sourceB16 + difference 2 3) sourceC16) = raw3076 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3076; decide +kernel
    rw [ha]
    exact (canonical3076 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA16 + difference 3 4) (sourceB16 + difference 4 3) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4017) := by
    have ha : (tripleCharges (sourceA16 + difference 3 4) (sourceB16 + difference 4 3) sourceC16) = raw3077 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3077; decide +kernel
    rw [ha]
    exact (canonical3077 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA16 + difference 3 5) (sourceB16 + difference 5 3) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA16 + difference 3 5) (sourceB16 + difference 5 3) sourceC16) = raw3078 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3078; decide +kernel
    rw [ha]
    exact (canonical3078 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA16 + difference 4 0) (sourceB16 + difference 0 4) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA16 + difference 4 0) (sourceB16 + difference 0 4) sourceC16) = raw3079 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3079; decide +kernel
    rw [ha]
    exact (canonical3079 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA16 + difference 4 1) (sourceB16 + difference 1 4) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA16 + difference 4 1) (sourceB16 + difference 1 4) sourceC16) = raw3080 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3080; decide +kernel
    rw [ha]
    exact (canonical3080 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA16 + difference 4 2) (sourceB16 + difference 2 4) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA16 + difference 4 2) (sourceB16 + difference 2 4) sourceC16) = raw3081 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3081; decide +kernel
    rw [ha]
    exact (canonical3081 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA16 + difference 4 3) (sourceB16 + difference 3 4) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA16 + difference 4 3) (sourceB16 + difference 3 4) sourceC16) = raw3082 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3082; decide +kernel
    rw [ha]
    exact (canonical3082 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA16 + difference 4 5) (sourceB16 + difference 5 4) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA16 + difference 4 5) (sourceB16 + difference 5 4) sourceC16) = raw3083 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3083; decide +kernel
    rw [ha]
    exact (canonical3083 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA16 + difference 5 0) (sourceB16 + difference 0 5) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA16 + difference 5 0) (sourceB16 + difference 0 5) sourceC16) = raw3084 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3084; decide +kernel
    rw [ha]
    exact (canonical3084 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA16 + difference 5 1) (sourceB16 + difference 1 5) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA16 + difference 5 1) (sourceB16 + difference 1 5) sourceC16) = raw3085 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3085; decide +kernel
    rw [ha]
    exact (canonical3085 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA16 + difference 5 2) (sourceB16 + difference 2 5) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA16 + difference 5 2) (sourceB16 + difference 2 5) sourceC16) = raw3086 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3086; decide +kernel
    rw [ha]
    exact (canonical3086 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA16 + difference 5 3) (sourceB16 + difference 3 5) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA16 + difference 5 3) (sourceB16 + difference 3 5) sourceC16) = raw3087 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3087; decide +kernel
    rw [ha]
    exact (canonical3087 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA16 + difference 5 4) (sourceB16 + difference 4 5) sourceC16) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4019) := by
    have ha : (tripleCharges (sourceA16 + difference 5 4) (sourceB16 + difference 4 5) sourceC16) = raw3088 := by
      apply Matrix.ext; unfold tripleCharges sourceA16 sourceB16 sourceC16 difference raw3088; decide +kernel
    rw [ha]
    exact (canonical3088 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA16 sourceB16 sourceC16
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm16, Integer.Sparse.eval]
  linarith only [hs]

def sourceA17 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB17 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC17 : Charge := ![1, -1, 0, 0, -1, 1]
def sourceForm17 : Integer.Sparse Master := [(Sum.inr 5271, 4), (Sum.inr 5272, 1), (Sum.inr 5275, 2), (Sum.inr 5306, 2), (Sum.inr 5473, 4), (Sum.inr 5475, 1), (Sum.inr 5478, 2), (Sum.inr 5485, 4), (Sum.inr 5490, 4), (Sum.inr 5491, 2), (Sum.inr 5492, 1), (Sum.inr 5493, 2), (Sum.inr 5501, 1)]

theorem sourceEq17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm17 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA17 + difference 0 1) (sourceB17 + difference 1 0) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA17 + difference 0 1) (sourceB17 + difference 1 0) sourceC17) = raw3089 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3089; decide +kernel
    rw [ha]
    exact (canonical3089 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA17 + difference 0 2) (sourceB17 + difference 2 0) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA17 + difference 0 2) (sourceB17 + difference 2 0) sourceC17) = raw3090 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3090; decide +kernel
    rw [ha]
    exact (canonical3090 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA17 + difference 0 3) (sourceB17 + difference 3 0) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA17 + difference 0 3) (sourceB17 + difference 3 0) sourceC17) = raw3091 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3091; decide +kernel
    rw [ha]
    exact (canonical3091 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA17 + difference 0 4) (sourceB17 + difference 4 0) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA17 + difference 0 4) (sourceB17 + difference 4 0) sourceC17) = raw3092 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3092; decide +kernel
    rw [ha]
    exact (canonical3092 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA17 + difference 0 5) (sourceB17 + difference 5 0) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5501) := by
    have ha : (tripleCharges (sourceA17 + difference 0 5) (sourceB17 + difference 5 0) sourceC17) = raw3093 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3093; decide +kernel
    rw [ha]
    exact (canonical3093 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA17 + difference 1 0) (sourceB17 + difference 0 1) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA17 + difference 1 0) (sourceB17 + difference 0 1) sourceC17) = raw3094 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3094; decide +kernel
    rw [ha]
    exact (canonical3094 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA17 + difference 1 2) (sourceB17 + difference 2 1) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA17 + difference 1 2) (sourceB17 + difference 2 1) sourceC17) = raw3095 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3095; decide +kernel
    rw [ha]
    exact (canonical3095 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA17 + difference 1 3) (sourceB17 + difference 3 1) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA17 + difference 1 3) (sourceB17 + difference 3 1) sourceC17) = raw3096 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3096; decide +kernel
    rw [ha]
    exact (canonical3096 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA17 + difference 1 4) (sourceB17 + difference 4 1) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA17 + difference 1 4) (sourceB17 + difference 4 1) sourceC17) = raw3097 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3097; decide +kernel
    rw [ha]
    exact (canonical3097 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA17 + difference 1 5) (sourceB17 + difference 5 1) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA17 + difference 1 5) (sourceB17 + difference 5 1) sourceC17) = raw3098 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3098; decide +kernel
    rw [ha]
    exact (canonical3098 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA17 + difference 2 0) (sourceB17 + difference 0 2) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA17 + difference 2 0) (sourceB17 + difference 0 2) sourceC17) = raw3099 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3099; decide +kernel
    rw [ha]
    exact (canonical3099 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA17 + difference 2 1) (sourceB17 + difference 1 2) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA17 + difference 2 1) (sourceB17 + difference 1 2) sourceC17) = raw3100 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3100; decide +kernel
    rw [ha]
    exact (canonical3100 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA17 + difference 2 3) (sourceB17 + difference 3 2) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA17 + difference 2 3) (sourceB17 + difference 3 2) sourceC17) = raw3101 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3101; decide +kernel
    rw [ha]
    exact (canonical3101 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA17 + difference 2 4) (sourceB17 + difference 4 2) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA17 + difference 2 4) (sourceB17 + difference 4 2) sourceC17) = raw3102 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3102; decide +kernel
    rw [ha]
    exact (canonical3102 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA17 + difference 2 5) (sourceB17 + difference 5 2) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA17 + difference 2 5) (sourceB17 + difference 5 2) sourceC17) = raw3103 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3103; decide +kernel
    rw [ha]
    exact (canonical3103 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA17 + difference 3 0) (sourceB17 + difference 0 3) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA17 + difference 3 0) (sourceB17 + difference 0 3) sourceC17) = raw3104 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3104; decide +kernel
    rw [ha]
    exact (canonical3104 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA17 + difference 3 1) (sourceB17 + difference 1 3) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA17 + difference 3 1) (sourceB17 + difference 1 3) sourceC17) = raw3105 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3105; decide +kernel
    rw [ha]
    exact (canonical3105 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA17 + difference 3 2) (sourceB17 + difference 2 3) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA17 + difference 3 2) (sourceB17 + difference 2 3) sourceC17) = raw3106 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3106; decide +kernel
    rw [ha]
    exact (canonical3106 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA17 + difference 3 4) (sourceB17 + difference 4 3) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA17 + difference 3 4) (sourceB17 + difference 4 3) sourceC17) = raw3107 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3107; decide +kernel
    rw [ha]
    exact (canonical3107 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA17 + difference 3 5) (sourceB17 + difference 5 3) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA17 + difference 3 5) (sourceB17 + difference 5 3) sourceC17) = raw3108 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3108; decide +kernel
    rw [ha]
    exact (canonical3108 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA17 + difference 4 0) (sourceB17 + difference 0 4) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA17 + difference 4 0) (sourceB17 + difference 0 4) sourceC17) = raw3109 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3109; decide +kernel
    rw [ha]
    exact (canonical3109 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA17 + difference 4 1) (sourceB17 + difference 1 4) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5475) := by
    have ha : (tripleCharges (sourceA17 + difference 4 1) (sourceB17 + difference 1 4) sourceC17) = raw3110 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3110; decide +kernel
    rw [ha]
    exact (canonical3110 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA17 + difference 4 2) (sourceB17 + difference 2 4) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA17 + difference 4 2) (sourceB17 + difference 2 4) sourceC17) = raw3111 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3111; decide +kernel
    rw [ha]
    exact (canonical3111 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA17 + difference 4 3) (sourceB17 + difference 3 4) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA17 + difference 4 3) (sourceB17 + difference 3 4) sourceC17) = raw3112 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3112; decide +kernel
    rw [ha]
    exact (canonical3112 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA17 + difference 4 5) (sourceB17 + difference 5 4) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA17 + difference 4 5) (sourceB17 + difference 5 4) sourceC17) = raw3113 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3113; decide +kernel
    rw [ha]
    exact (canonical3113 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA17 + difference 5 0) (sourceB17 + difference 0 5) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA17 + difference 5 0) (sourceB17 + difference 0 5) sourceC17) = raw3114 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3114; decide +kernel
    rw [ha]
    exact (canonical3114 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA17 + difference 5 1) (sourceB17 + difference 1 5) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA17 + difference 5 1) (sourceB17 + difference 1 5) sourceC17) = raw3115 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3115; decide +kernel
    rw [ha]
    exact (canonical3115 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA17 + difference 5 2) (sourceB17 + difference 2 5) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA17 + difference 5 2) (sourceB17 + difference 2 5) sourceC17) = raw3116 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3116; decide +kernel
    rw [ha]
    exact (canonical3116 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA17 + difference 5 3) (sourceB17 + difference 3 5) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA17 + difference 5 3) (sourceB17 + difference 3 5) sourceC17) = raw3117 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3117; decide +kernel
    rw [ha]
    exact (canonical3117 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA17 + difference 5 4) (sourceB17 + difference 4 5) sourceC17) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA17 + difference 5 4) (sourceB17 + difference 4 5) sourceC17) = raw3118 := by
      apply Matrix.ext; unfold tripleCharges sourceA17 sourceB17 sourceC17 difference raw3118; decide +kernel
    rw [ha]
    exact (canonical3118 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA17 sourceB17 sourceC17
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm17, Integer.Sparse.eval]
  linarith only [hs]

def sourceA18 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB18 : Charge := ![1, -1, 0, 1, -1, 0]
def sourceC18 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceForm18 : Integer.Sparse Master := [(Sum.inr 5257, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5271, 1), (Sum.inr 5292, 1), (Sum.inr 5424, 1), (Sum.inr 5428, 1), (Sum.inr 5434, 1), (Sum.inr 5439, 1), (Sum.inr 5472, 1), (Sum.inr 5473, 2), (Sum.inr 5477, 1), (Sum.inr 5478, 1), (Sum.inr 5482, 2), (Sum.inr 5483, 1), (Sum.inr 5485, 1), (Sum.inr 5486, 1), (Sum.inr 5489, 1), (Sum.inr 5490, 3), (Sum.inr 5491, 1), (Sum.inr 5492, 1), (Sum.inr 5493, 1), (Sum.inr 5499, 2), (Sum.inr 5500, 1), (Sum.inr 5501, 1)]

theorem sourceEq18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm18 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA18 + difference 0 1) (sourceB18 + difference 1 0) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA18 + difference 0 1) (sourceB18 + difference 1 0) sourceC18) = raw3119 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3119; decide +kernel
    rw [ha]
    exact (canonical3119 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA18 + difference 0 2) (sourceB18 + difference 2 0) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA18 + difference 0 2) (sourceB18 + difference 2 0) sourceC18) = raw3120 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3120; decide +kernel
    rw [ha]
    exact (canonical3120 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA18 + difference 0 3) (sourceB18 + difference 3 0) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA18 + difference 0 3) (sourceB18 + difference 3 0) sourceC18) = raw3121 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3121; decide +kernel
    rw [ha]
    exact (canonical3121 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA18 + difference 0 4) (sourceB18 + difference 4 0) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5501) := by
    have ha : (tripleCharges (sourceA18 + difference 0 4) (sourceB18 + difference 4 0) sourceC18) = raw3122 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3122; decide +kernel
    rw [ha]
    exact (canonical3122 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA18 + difference 0 5) (sourceB18 + difference 5 0) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA18 + difference 0 5) (sourceB18 + difference 5 0) sourceC18) = raw3123 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3123; decide +kernel
    rw [ha]
    exact (canonical3123 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA18 + difference 1 0) (sourceB18 + difference 0 1) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA18 + difference 1 0) (sourceB18 + difference 0 1) sourceC18) = raw3124 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3124; decide +kernel
    rw [ha]
    exact (canonical3124 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA18 + difference 1 2) (sourceB18 + difference 2 1) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA18 + difference 1 2) (sourceB18 + difference 2 1) sourceC18) = raw3125 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3125; decide +kernel
    rw [ha]
    exact (canonical3125 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA18 + difference 1 3) (sourceB18 + difference 3 1) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA18 + difference 1 3) (sourceB18 + difference 3 1) sourceC18) = raw3126 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3126; decide +kernel
    rw [ha]
    exact (canonical3126 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA18 + difference 1 4) (sourceB18 + difference 4 1) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA18 + difference 1 4) (sourceB18 + difference 4 1) sourceC18) = raw3127 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3127; decide +kernel
    rw [ha]
    exact (canonical3127 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA18 + difference 1 5) (sourceB18 + difference 5 1) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA18 + difference 1 5) (sourceB18 + difference 5 1) sourceC18) = raw3128 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3128; decide +kernel
    rw [ha]
    exact (canonical3128 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA18 + difference 2 0) (sourceB18 + difference 0 2) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA18 + difference 2 0) (sourceB18 + difference 0 2) sourceC18) = raw3129 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3129; decide +kernel
    rw [ha]
    exact (canonical3129 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA18 + difference 2 1) (sourceB18 + difference 1 2) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA18 + difference 2 1) (sourceB18 + difference 1 2) sourceC18) = raw3130 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3130; decide +kernel
    rw [ha]
    exact (canonical3130 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA18 + difference 2 3) (sourceB18 + difference 3 2) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA18 + difference 2 3) (sourceB18 + difference 3 2) sourceC18) = raw3131 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3131; decide +kernel
    rw [ha]
    exact (canonical3131 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA18 + difference 2 4) (sourceB18 + difference 4 2) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA18 + difference 2 4) (sourceB18 + difference 4 2) sourceC18) = raw3132 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3132; decide +kernel
    rw [ha]
    exact (canonical3132 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA18 + difference 2 5) (sourceB18 + difference 5 2) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA18 + difference 2 5) (sourceB18 + difference 5 2) sourceC18) = raw3133 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3133; decide +kernel
    rw [ha]
    exact (canonical3133 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA18 + difference 3 0) (sourceB18 + difference 0 3) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA18 + difference 3 0) (sourceB18 + difference 0 3) sourceC18) = raw3134 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3134; decide +kernel
    rw [ha]
    exact (canonical3134 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA18 + difference 3 1) (sourceB18 + difference 1 3) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA18 + difference 3 1) (sourceB18 + difference 1 3) sourceC18) = raw3135 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3135; decide +kernel
    rw [ha]
    exact (canonical3135 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA18 + difference 3 2) (sourceB18 + difference 2 3) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA18 + difference 3 2) (sourceB18 + difference 2 3) sourceC18) = raw3136 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3136; decide +kernel
    rw [ha]
    exact (canonical3136 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA18 + difference 3 4) (sourceB18 + difference 4 3) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA18 + difference 3 4) (sourceB18 + difference 4 3) sourceC18) = raw3137 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3137; decide +kernel
    rw [ha]
    exact (canonical3137 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA18 + difference 3 5) (sourceB18 + difference 5 3) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA18 + difference 3 5) (sourceB18 + difference 5 3) sourceC18) = raw3138 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3138; decide +kernel
    rw [ha]
    exact (canonical3138 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA18 + difference 4 0) (sourceB18 + difference 0 4) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA18 + difference 4 0) (sourceB18 + difference 0 4) sourceC18) = raw3139 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3139; decide +kernel
    rw [ha]
    exact (canonical3139 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA18 + difference 4 1) (sourceB18 + difference 1 4) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA18 + difference 4 1) (sourceB18 + difference 1 4) sourceC18) = raw3140 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3140; decide +kernel
    rw [ha]
    exact (canonical3140 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA18 + difference 4 2) (sourceB18 + difference 2 4) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA18 + difference 4 2) (sourceB18 + difference 2 4) sourceC18) = raw3141 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3141; decide +kernel
    rw [ha]
    exact (canonical3141 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA18 + difference 4 3) (sourceB18 + difference 3 4) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA18 + difference 4 3) (sourceB18 + difference 3 4) sourceC18) = raw3142 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3142; decide +kernel
    rw [ha]
    exact (canonical3142 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA18 + difference 4 5) (sourceB18 + difference 5 4) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA18 + difference 4 5) (sourceB18 + difference 5 4) sourceC18) = raw3143 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3143; decide +kernel
    rw [ha]
    exact (canonical3143 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA18 + difference 5 0) (sourceB18 + difference 0 5) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA18 + difference 5 0) (sourceB18 + difference 0 5) sourceC18) = raw3144 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3144; decide +kernel
    rw [ha]
    exact (canonical3144 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA18 + difference 5 1) (sourceB18 + difference 1 5) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA18 + difference 5 1) (sourceB18 + difference 1 5) sourceC18) = raw3145 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3145; decide +kernel
    rw [ha]
    exact (canonical3145 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA18 + difference 5 2) (sourceB18 + difference 2 5) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA18 + difference 5 2) (sourceB18 + difference 2 5) sourceC18) = raw3146 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3146; decide +kernel
    rw [ha]
    exact (canonical3146 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA18 + difference 5 3) (sourceB18 + difference 3 5) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA18 + difference 5 3) (sourceB18 + difference 3 5) sourceC18) = raw3147 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3147; decide +kernel
    rw [ha]
    exact (canonical3147 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA18 + difference 5 4) (sourceB18 + difference 4 5) sourceC18) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA18 + difference 5 4) (sourceB18 + difference 4 5) sourceC18) = raw3148 := by
      apply Matrix.ext; unfold tripleCharges sourceA18 sourceB18 sourceC18 difference raw3148; decide +kernel
    rw [ha]
    exact (canonical3148 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA18 sourceB18 sourceC18
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm18, Integer.Sparse.eval]
  linarith only [hs]

def sourceA19 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB19 : Charge := ![1, -1, 0, 1, -1, 0]
def sourceC19 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceForm19 : Integer.Sparse Master := [(Sum.inr 2721, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 2739, 1), (Sum.inr 2766, 1), (Sum.inr 3838, 1), (Sum.inr 3845, 1), (Sum.inr 3852, 1), (Sum.inr 3902, 1), (Sum.inr 3957, 1), (Sum.inr 3958, 1), (Sum.inr 3961, 1), (Sum.inr 3971, 1), (Sum.inr 3974, 1), (Sum.inr 3980, 1), (Sum.inr 3981, 1), (Sum.inr 3992, 1), (Sum.inr 3999, 1), (Sum.inr 4009, 1), (Sum.inr 4010, 1), (Sum.inr 4013, 2), (Sum.inr 4014, 1), (Sum.inr 4015, 1), (Sum.inr 4018, 1), (Sum.inr 4050, 1), (Sum.inr 4052, 1), (Sum.inr 4053, 1), (Sum.inr 4054, 1), (Sum.inr 4055, 1)]

theorem sourceEq19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm19 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA19 + difference 0 1) (sourceB19 + difference 1 0) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4054) := by
    have ha : (tripleCharges (sourceA19 + difference 0 1) (sourceB19 + difference 1 0) sourceC19) = raw3149 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3149; decide +kernel
    rw [ha]
    exact (canonical3149 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA19 + difference 0 2) (sourceB19 + difference 2 0) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4053) := by
    have ha : (tripleCharges (sourceA19 + difference 0 2) (sourceB19 + difference 2 0) sourceC19) = raw3150 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3150; decide +kernel
    rw [ha]
    exact (canonical3150 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA19 + difference 0 3) (sourceB19 + difference 3 0) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4050) := by
    have ha : (tripleCharges (sourceA19 + difference 0 3) (sourceB19 + difference 3 0) sourceC19) = raw3151 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3151; decide +kernel
    rw [ha]
    exact (canonical3151 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA19 + difference 0 4) (sourceB19 + difference 4 0) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4055) := by
    have ha : (tripleCharges (sourceA19 + difference 0 4) (sourceB19 + difference 4 0) sourceC19) = raw3152 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3152; decide +kernel
    rw [ha]
    exact (canonical3152 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA19 + difference 0 5) (sourceB19 + difference 5 0) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4052) := by
    have ha : (tripleCharges (sourceA19 + difference 0 5) (sourceB19 + difference 5 0) sourceC19) = raw3153 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3153; decide +kernel
    rw [ha]
    exact (canonical3153 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA19 + difference 1 0) (sourceB19 + difference 0 1) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA19 + difference 1 0) (sourceB19 + difference 0 1) sourceC19) = raw3154 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3154; decide +kernel
    rw [ha]
    exact (canonical3154 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA19 + difference 1 2) (sourceB19 + difference 2 1) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA19 + difference 1 2) (sourceB19 + difference 2 1) sourceC19) = raw3155 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3155; decide +kernel
    rw [ha]
    exact (canonical3155 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA19 + difference 1 3) (sourceB19 + difference 3 1) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA19 + difference 1 3) (sourceB19 + difference 3 1) sourceC19) = raw3156 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3156; decide +kernel
    rw [ha]
    exact (canonical3156 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA19 + difference 1 4) (sourceB19 + difference 4 1) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4015) := by
    have ha : (tripleCharges (sourceA19 + difference 1 4) (sourceB19 + difference 4 1) sourceC19) = raw3157 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3157; decide +kernel
    rw [ha]
    exact (canonical3157 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA19 + difference 1 5) (sourceB19 + difference 5 1) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA19 + difference 1 5) (sourceB19 + difference 5 1) sourceC19) = raw3158 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3158; decide +kernel
    rw [ha]
    exact (canonical3158 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA19 + difference 2 0) (sourceB19 + difference 0 2) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA19 + difference 2 0) (sourceB19 + difference 0 2) sourceC19) = raw3159 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3159; decide +kernel
    rw [ha]
    exact (canonical3159 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA19 + difference 2 1) (sourceB19 + difference 1 2) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3992) := by
    have ha : (tripleCharges (sourceA19 + difference 2 1) (sourceB19 + difference 1 2) sourceC19) = raw3160 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3160; decide +kernel
    rw [ha]
    exact (canonical3160 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA19 + difference 2 3) (sourceB19 + difference 3 2) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA19 + difference 2 3) (sourceB19 + difference 3 2) sourceC19) = raw3161 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3161; decide +kernel
    rw [ha]
    exact (canonical3161 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA19 + difference 2 4) (sourceB19 + difference 4 2) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA19 + difference 2 4) (sourceB19 + difference 4 2) sourceC19) = raw3162 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3162; decide +kernel
    rw [ha]
    exact (canonical3162 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA19 + difference 2 5) (sourceB19 + difference 5 2) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4009) := by
    have ha : (tripleCharges (sourceA19 + difference 2 5) (sourceB19 + difference 5 2) sourceC19) = raw3163 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3163; decide +kernel
    rw [ha]
    exact (canonical3163 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA19 + difference 3 0) (sourceB19 + difference 0 3) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA19 + difference 3 0) (sourceB19 + difference 0 3) sourceC19) = raw3164 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3164; decide +kernel
    rw [ha]
    exact (canonical3164 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA19 + difference 3 1) (sourceB19 + difference 1 3) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3999) := by
    have ha : (tripleCharges (sourceA19 + difference 3 1) (sourceB19 + difference 1 3) sourceC19) = raw3165 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3165; decide +kernel
    rw [ha]
    exact (canonical3165 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA19 + difference 3 2) (sourceB19 + difference 2 3) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA19 + difference 3 2) (sourceB19 + difference 2 3) sourceC19) = raw3166 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3166; decide +kernel
    rw [ha]
    exact (canonical3166 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA19 + difference 3 4) (sourceB19 + difference 4 3) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4018) := by
    have ha : (tripleCharges (sourceA19 + difference 3 4) (sourceB19 + difference 4 3) sourceC19) = raw3167 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3167; decide +kernel
    rw [ha]
    exact (canonical3167 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA19 + difference 3 5) (sourceB19 + difference 5 3) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA19 + difference 3 5) (sourceB19 + difference 5 3) sourceC19) = raw3168 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3168; decide +kernel
    rw [ha]
    exact (canonical3168 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA19 + difference 4 0) (sourceB19 + difference 0 4) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA19 + difference 4 0) (sourceB19 + difference 0 4) sourceC19) = raw3169 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3169; decide +kernel
    rw [ha]
    exact (canonical3169 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA19 + difference 4 1) (sourceB19 + difference 1 4) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA19 + difference 4 1) (sourceB19 + difference 1 4) sourceC19) = raw3170 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3170; decide +kernel
    rw [ha]
    exact (canonical3170 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA19 + difference 4 2) (sourceB19 + difference 2 4) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA19 + difference 4 2) (sourceB19 + difference 2 4) sourceC19) = raw3171 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3171; decide +kernel
    rw [ha]
    exact (canonical3171 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA19 + difference 4 3) (sourceB19 + difference 3 4) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA19 + difference 4 3) (sourceB19 + difference 3 4) sourceC19) = raw3172 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3172; decide +kernel
    rw [ha]
    exact (canonical3172 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA19 + difference 4 5) (sourceB19 + difference 5 4) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA19 + difference 4 5) (sourceB19 + difference 5 4) sourceC19) = raw3173 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3173; decide +kernel
    rw [ha]
    exact (canonical3173 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA19 + difference 5 0) (sourceB19 + difference 0 5) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA19 + difference 5 0) (sourceB19 + difference 0 5) sourceC19) = raw3174 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3174; decide +kernel
    rw [ha]
    exact (canonical3174 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA19 + difference 5 1) (sourceB19 + difference 1 5) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA19 + difference 5 1) (sourceB19 + difference 1 5) sourceC19) = raw3175 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3175; decide +kernel
    rw [ha]
    exact (canonical3175 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA19 + difference 5 2) (sourceB19 + difference 2 5) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3971) := by
    have ha : (tripleCharges (sourceA19 + difference 5 2) (sourceB19 + difference 2 5) sourceC19) = raw3176 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3176; decide +kernel
    rw [ha]
    exact (canonical3176 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA19 + difference 5 3) (sourceB19 + difference 3 5) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA19 + difference 5 3) (sourceB19 + difference 3 5) sourceC19) = raw3177 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3177; decide +kernel
    rw [ha]
    exact (canonical3177 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA19 + difference 5 4) (sourceB19 + difference 4 5) sourceC19) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4014) := by
    have ha : (tripleCharges (sourceA19 + difference 5 4) (sourceB19 + difference 4 5) sourceC19) = raw3178 := by
      apply Matrix.ext; unfold tripleCharges sourceA19 sourceB19 sourceC19 difference raw3178; decide +kernel
    rw [ha]
    exact (canonical3178 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA19 sourceB19 sourceC19
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm19, Integer.Sparse.eval]
  linarith only [hs]

def sourceA20 : Charge := ![1, -1, 0, 1, -1, 0]
def sourceB20 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC20 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceForm20 : Integer.Sparse Master := [(Sum.inr 5431, 2), (Sum.inr 5432, 1), (Sum.inr 5433, 2), (Sum.inr 5434, 2), (Sum.inr 5435, 2), (Sum.inr 5438, 2), (Sum.inr 5440, 2), (Sum.inr 5450, 2), (Sum.inr 5454, 2), (Sum.inr 5481, 2), (Sum.inr 5484, 1), (Sum.inr 5489, 2), (Sum.inr 5490, 3), (Sum.inr 5492, 2), (Sum.inr 5493, 2), (Sum.inr 5495, 1)]

theorem sourceEq20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm20 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA20 + difference 0 1) (sourceB20 + difference 1 0) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA20 + difference 0 1) (sourceB20 + difference 1 0) sourceC20) = raw3179 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3179; decide +kernel
    rw [ha]
    exact (canonical3179 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA20 + difference 0 2) (sourceB20 + difference 2 0) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA20 + difference 0 2) (sourceB20 + difference 2 0) sourceC20) = raw3180 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3180; decide +kernel
    rw [ha]
    exact (canonical3180 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA20 + difference 0 3) (sourceB20 + difference 3 0) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA20 + difference 0 3) (sourceB20 + difference 3 0) sourceC20) = raw3181 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3181; decide +kernel
    rw [ha]
    exact (canonical3181 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA20 + difference 0 4) (sourceB20 + difference 4 0) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA20 + difference 0 4) (sourceB20 + difference 4 0) sourceC20) = raw3182 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3182; decide +kernel
    rw [ha]
    exact (canonical3182 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA20 + difference 0 5) (sourceB20 + difference 5 0) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA20 + difference 0 5) (sourceB20 + difference 5 0) sourceC20) = raw3183 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3183; decide +kernel
    rw [ha]
    exact (canonical3183 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA20 + difference 1 0) (sourceB20 + difference 0 1) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA20 + difference 1 0) (sourceB20 + difference 0 1) sourceC20) = raw3184 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3184; decide +kernel
    rw [ha]
    exact (canonical3184 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA20 + difference 1 2) (sourceB20 + difference 2 1) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA20 + difference 1 2) (sourceB20 + difference 2 1) sourceC20) = raw3185 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3185; decide +kernel
    rw [ha]
    exact (canonical3185 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA20 + difference 1 3) (sourceB20 + difference 3 1) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5495) := by
    have ha : (tripleCharges (sourceA20 + difference 1 3) (sourceB20 + difference 3 1) sourceC20) = raw3186 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3186; decide +kernel
    rw [ha]
    exact (canonical3186 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA20 + difference 1 4) (sourceB20 + difference 4 1) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA20 + difference 1 4) (sourceB20 + difference 4 1) sourceC20) = raw3187 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3187; decide +kernel
    rw [ha]
    exact (canonical3187 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA20 + difference 1 5) (sourceB20 + difference 5 1) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA20 + difference 1 5) (sourceB20 + difference 5 1) sourceC20) = raw3188 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3188; decide +kernel
    rw [ha]
    exact (canonical3188 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA20 + difference 2 0) (sourceB20 + difference 0 2) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA20 + difference 2 0) (sourceB20 + difference 0 2) sourceC20) = raw3189 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3189; decide +kernel
    rw [ha]
    exact (canonical3189 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA20 + difference 2 1) (sourceB20 + difference 1 2) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA20 + difference 2 1) (sourceB20 + difference 1 2) sourceC20) = raw3190 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3190; decide +kernel
    rw [ha]
    exact (canonical3190 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA20 + difference 2 3) (sourceB20 + difference 3 2) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA20 + difference 2 3) (sourceB20 + difference 3 2) sourceC20) = raw3191 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3191; decide +kernel
    rw [ha]
    exact (canonical3191 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA20 + difference 2 4) (sourceB20 + difference 4 2) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA20 + difference 2 4) (sourceB20 + difference 4 2) sourceC20) = raw3192 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3192; decide +kernel
    rw [ha]
    exact (canonical3192 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA20 + difference 2 5) (sourceB20 + difference 5 2) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA20 + difference 2 5) (sourceB20 + difference 5 2) sourceC20) = raw3193 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3193; decide +kernel
    rw [ha]
    exact (canonical3193 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA20 + difference 3 0) (sourceB20 + difference 0 3) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA20 + difference 3 0) (sourceB20 + difference 0 3) sourceC20) = raw3194 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3194; decide +kernel
    rw [ha]
    exact (canonical3194 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA20 + difference 3 1) (sourceB20 + difference 1 3) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA20 + difference 3 1) (sourceB20 + difference 1 3) sourceC20) = raw3195 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3195; decide +kernel
    rw [ha]
    exact (canonical3195 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA20 + difference 3 2) (sourceB20 + difference 2 3) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA20 + difference 3 2) (sourceB20 + difference 2 3) sourceC20) = raw3196 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3196; decide +kernel
    rw [ha]
    exact (canonical3196 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA20 + difference 3 4) (sourceB20 + difference 4 3) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA20 + difference 3 4) (sourceB20 + difference 4 3) sourceC20) = raw3197 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3197; decide +kernel
    rw [ha]
    exact (canonical3197 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA20 + difference 3 5) (sourceB20 + difference 5 3) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA20 + difference 3 5) (sourceB20 + difference 5 3) sourceC20) = raw3198 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3198; decide +kernel
    rw [ha]
    exact (canonical3198 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA20 + difference 4 0) (sourceB20 + difference 0 4) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA20 + difference 4 0) (sourceB20 + difference 0 4) sourceC20) = raw3199 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3199; decide +kernel
    rw [ha]
    exact (canonical3199 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA20 + difference 4 1) (sourceB20 + difference 1 4) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA20 + difference 4 1) (sourceB20 + difference 1 4) sourceC20) = raw3200 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3200; decide +kernel
    rw [ha]
    exact (canonical3200 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA20 + difference 4 2) (sourceB20 + difference 2 4) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA20 + difference 4 2) (sourceB20 + difference 2 4) sourceC20) = raw3201 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3201; decide +kernel
    rw [ha]
    exact (canonical3201 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA20 + difference 4 3) (sourceB20 + difference 3 4) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA20 + difference 4 3) (sourceB20 + difference 3 4) sourceC20) = raw3202 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3202; decide +kernel
    rw [ha]
    exact (canonical3202 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA20 + difference 4 5) (sourceB20 + difference 5 4) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA20 + difference 4 5) (sourceB20 + difference 5 4) sourceC20) = raw3203 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3203; decide +kernel
    rw [ha]
    exact (canonical3203 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA20 + difference 5 0) (sourceB20 + difference 0 5) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA20 + difference 5 0) (sourceB20 + difference 0 5) sourceC20) = raw3204 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3204; decide +kernel
    rw [ha]
    exact (canonical3204 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA20 + difference 5 1) (sourceB20 + difference 1 5) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA20 + difference 5 1) (sourceB20 + difference 1 5) sourceC20) = raw3205 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3205; decide +kernel
    rw [ha]
    exact (canonical3205 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA20 + difference 5 2) (sourceB20 + difference 2 5) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA20 + difference 5 2) (sourceB20 + difference 2 5) sourceC20) = raw3206 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3206; decide +kernel
    rw [ha]
    exact (canonical3206 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA20 + difference 5 3) (sourceB20 + difference 3 5) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA20 + difference 5 3) (sourceB20 + difference 3 5) sourceC20) = raw3207 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3207; decide +kernel
    rw [ha]
    exact (canonical3207 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA20 + difference 5 4) (sourceB20 + difference 4 5) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA20 + difference 5 4) (sourceB20 + difference 4 5) sourceC20) = raw3208 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3208; decide +kernel
    rw [ha]
    exact (canonical3208 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA20 sourceB20 sourceC20
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm20, Integer.Sparse.eval]
  linarith only [hs]

def sourceA21 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB21 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceC21 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceForm21 : Integer.Sparse Master := [(Sum.inr 5304, 6), (Sum.inr 5305, 1), (Sum.inr 5310, 2), (Sum.inr 5451, 6), (Sum.inr 5455, 2), (Sum.inr 5484, 6), (Sum.inr 5492, 6), (Sum.inr 5495, 1)]

theorem sourceEq21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm21 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA21 + difference 0 1) (sourceB21 + difference 1 0) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA21 + difference 0 1) (sourceB21 + difference 1 0) sourceC21) = raw3209 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3209; decide +kernel
    rw [ha]
    exact (canonical3209 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA21 + difference 0 2) (sourceB21 + difference 2 0) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA21 + difference 0 2) (sourceB21 + difference 2 0) sourceC21) = raw3210 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3210; decide +kernel
    rw [ha]
    exact (canonical3210 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA21 + difference 0 3) (sourceB21 + difference 3 0) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA21 + difference 0 3) (sourceB21 + difference 3 0) sourceC21) = raw3211 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3211; decide +kernel
    rw [ha]
    exact (canonical3211 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA21 + difference 0 4) (sourceB21 + difference 4 0) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5495) := by
    have ha : (tripleCharges (sourceA21 + difference 0 4) (sourceB21 + difference 4 0) sourceC21) = raw2855 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2855; decide +kernel
    rw [ha]
    exact (canonical2855 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA21 + difference 0 5) (sourceB21 + difference 5 0) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA21 + difference 0 5) (sourceB21 + difference 5 0) sourceC21) = raw3212 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3212; decide +kernel
    rw [ha]
    exact (canonical3212 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA21 + difference 1 0) (sourceB21 + difference 0 1) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA21 + difference 1 0) (sourceB21 + difference 0 1) sourceC21) = raw3213 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3213; decide +kernel
    rw [ha]
    exact (canonical3213 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA21 + difference 1 2) (sourceB21 + difference 2 1) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA21 + difference 1 2) (sourceB21 + difference 2 1) sourceC21) = raw3214 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3214; decide +kernel
    rw [ha]
    exact (canonical3214 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA21 + difference 1 3) (sourceB21 + difference 3 1) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA21 + difference 1 3) (sourceB21 + difference 3 1) sourceC21) = raw3215 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3215; decide +kernel
    rw [ha]
    exact (canonical3215 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA21 + difference 1 4) (sourceB21 + difference 4 1) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA21 + difference 1 4) (sourceB21 + difference 4 1) sourceC21) = raw2860 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2860; decide +kernel
    rw [ha]
    exact (canonical2860 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA21 + difference 1 5) (sourceB21 + difference 5 1) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA21 + difference 1 5) (sourceB21 + difference 5 1) sourceC21) = raw3216 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3216; decide +kernel
    rw [ha]
    exact (canonical3216 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA21 + difference 2 0) (sourceB21 + difference 0 2) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA21 + difference 2 0) (sourceB21 + difference 0 2) sourceC21) = raw3217 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3217; decide +kernel
    rw [ha]
    exact (canonical3217 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA21 + difference 2 1) (sourceB21 + difference 1 2) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA21 + difference 2 1) (sourceB21 + difference 1 2) sourceC21) = raw3218 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3218; decide +kernel
    rw [ha]
    exact (canonical3218 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA21 + difference 2 3) (sourceB21 + difference 3 2) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA21 + difference 2 3) (sourceB21 + difference 3 2) sourceC21) = raw3219 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3219; decide +kernel
    rw [ha]
    exact (canonical3219 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA21 + difference 2 4) (sourceB21 + difference 4 2) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA21 + difference 2 4) (sourceB21 + difference 4 2) sourceC21) = raw2865 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2865; decide +kernel
    rw [ha]
    exact (canonical2865 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA21 + difference 2 5) (sourceB21 + difference 5 2) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA21 + difference 2 5) (sourceB21 + difference 5 2) sourceC21) = raw3220 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3220; decide +kernel
    rw [ha]
    exact (canonical3220 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA21 + difference 3 0) (sourceB21 + difference 0 3) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA21 + difference 3 0) (sourceB21 + difference 0 3) sourceC21) = raw3221 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3221; decide +kernel
    rw [ha]
    exact (canonical3221 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA21 + difference 3 1) (sourceB21 + difference 1 3) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA21 + difference 3 1) (sourceB21 + difference 1 3) sourceC21) = raw3222 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3222; decide +kernel
    rw [ha]
    exact (canonical3222 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA21 + difference 3 2) (sourceB21 + difference 2 3) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA21 + difference 3 2) (sourceB21 + difference 2 3) sourceC21) = raw3223 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3223; decide +kernel
    rw [ha]
    exact (canonical3223 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA21 + difference 3 4) (sourceB21 + difference 4 3) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA21 + difference 3 4) (sourceB21 + difference 4 3) sourceC21) = raw2870 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2870; decide +kernel
    rw [ha]
    exact (canonical2870 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA21 + difference 3 5) (sourceB21 + difference 5 3) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA21 + difference 3 5) (sourceB21 + difference 5 3) sourceC21) = raw3224 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3224; decide +kernel
    rw [ha]
    exact (canonical3224 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA21 + difference 4 0) (sourceB21 + difference 0 4) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA21 + difference 4 0) (sourceB21 + difference 0 4) sourceC21) = raw3225 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3225; decide +kernel
    rw [ha]
    exact (canonical3225 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA21 + difference 4 1) (sourceB21 + difference 1 4) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA21 + difference 4 1) (sourceB21 + difference 1 4) sourceC21) = raw3226 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3226; decide +kernel
    rw [ha]
    exact (canonical3226 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA21 + difference 4 2) (sourceB21 + difference 2 4) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA21 + difference 4 2) (sourceB21 + difference 2 4) sourceC21) = raw3227 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3227; decide +kernel
    rw [ha]
    exact (canonical3227 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA21 + difference 4 3) (sourceB21 + difference 3 4) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA21 + difference 4 3) (sourceB21 + difference 3 4) sourceC21) = raw3228 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3228; decide +kernel
    rw [ha]
    exact (canonical3228 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA21 + difference 4 5) (sourceB21 + difference 5 4) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA21 + difference 4 5) (sourceB21 + difference 5 4) sourceC21) = raw3229 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3229; decide +kernel
    rw [ha]
    exact (canonical3229 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA21 + difference 5 0) (sourceB21 + difference 0 5) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA21 + difference 5 0) (sourceB21 + difference 0 5) sourceC21) = raw2871 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2871; decide +kernel
    rw [ha]
    exact (canonical2871 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA21 + difference 5 1) (sourceB21 + difference 1 5) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA21 + difference 5 1) (sourceB21 + difference 1 5) sourceC21) = raw2872 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2872; decide +kernel
    rw [ha]
    exact (canonical2872 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA21 + difference 5 2) (sourceB21 + difference 2 5) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA21 + difference 5 2) (sourceB21 + difference 2 5) sourceC21) = raw2873 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2873; decide +kernel
    rw [ha]
    exact (canonical2873 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA21 + difference 5 3) (sourceB21 + difference 3 5) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA21 + difference 5 3) (sourceB21 + difference 3 5) sourceC21) = raw2874 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2874; decide +kernel
    rw [ha]
    exact (canonical2874 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA21 + difference 5 4) (sourceB21 + difference 4 5) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA21 + difference 5 4) (sourceB21 + difference 4 5) sourceC21) = raw3230 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3230; decide +kernel
    rw [ha]
    exact (canonical3230 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA21 sourceB21 sourceC21
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm21, Integer.Sparse.eval]
  linarith only [hs]

def sourceA22 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB22 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC22 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceForm22 : Integer.Sparse Master := [(Sum.inr 4096, 1), (Sum.inr 5292, 2), (Sum.inr 5293, 2), (Sum.inr 5306, 1), (Sum.inr 5482, 2), (Sum.inr 5483, 4), (Sum.inr 5485, 2), (Sum.inr 5486, 2), (Sum.inr 5487, 2), (Sum.inr 5490, 4), (Sum.inr 5491, 2), (Sum.inr 5492, 2), (Sum.inr 5499, 2), (Sum.inr 5501, 2)]

theorem sourceEq22 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm22 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA22 + difference 0 1) (sourceB22 + difference 1 0) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA22 + difference 0 1) (sourceB22 + difference 1 0) sourceC22) = raw3231 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3231; decide +kernel
    rw [ha]
    exact (canonical3231 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA22 + difference 0 2) (sourceB22 + difference 2 0) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA22 + difference 0 2) (sourceB22 + difference 2 0) sourceC22) = raw3232 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3232; decide +kernel
    rw [ha]
    exact (canonical3232 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA22 + difference 0 3) (sourceB22 + difference 3 0) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA22 + difference 0 3) (sourceB22 + difference 3 0) sourceC22) = raw3233 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3233; decide +kernel
    rw [ha]
    exact (canonical3233 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA22 + difference 0 4) (sourceB22 + difference 4 0) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5501) := by
    have ha : (tripleCharges (sourceA22 + difference 0 4) (sourceB22 + difference 4 0) sourceC22) = raw3234 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3234; decide +kernel
    rw [ha]
    exact (canonical3234 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA22 + difference 0 5) (sourceB22 + difference 5 0) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5501) := by
    have ha : (tripleCharges (sourceA22 + difference 0 5) (sourceB22 + difference 5 0) sourceC22) = raw3235 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3235; decide +kernel
    rw [ha]
    exact (canonical3235 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA22 + difference 1 0) (sourceB22 + difference 0 1) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA22 + difference 1 0) (sourceB22 + difference 0 1) sourceC22) = raw3236 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3236; decide +kernel
    rw [ha]
    exact (canonical3236 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA22 + difference 1 2) (sourceB22 + difference 2 1) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA22 + difference 1 2) (sourceB22 + difference 2 1) sourceC22) = raw3237 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3237; decide +kernel
    rw [ha]
    exact (canonical3237 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA22 + difference 1 3) (sourceB22 + difference 3 1) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA22 + difference 1 3) (sourceB22 + difference 3 1) sourceC22) = raw3238 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3238; decide +kernel
    rw [ha]
    exact (canonical3238 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA22 + difference 1 4) (sourceB22 + difference 4 1) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA22 + difference 1 4) (sourceB22 + difference 4 1) sourceC22) = raw3239 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3239; decide +kernel
    rw [ha]
    exact (canonical3239 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA22 + difference 1 5) (sourceB22 + difference 5 1) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA22 + difference 1 5) (sourceB22 + difference 5 1) sourceC22) = raw3240 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3240; decide +kernel
    rw [ha]
    exact (canonical3240 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA22 + difference 2 0) (sourceB22 + difference 0 2) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA22 + difference 2 0) (sourceB22 + difference 0 2) sourceC22) = raw3241 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3241; decide +kernel
    rw [ha]
    exact (canonical3241 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA22 + difference 2 1) (sourceB22 + difference 1 2) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA22 + difference 2 1) (sourceB22 + difference 1 2) sourceC22) = raw3242 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3242; decide +kernel
    rw [ha]
    exact (canonical3242 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA22 + difference 2 3) (sourceB22 + difference 3 2) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA22 + difference 2 3) (sourceB22 + difference 3 2) sourceC22) = raw3243 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3243; decide +kernel
    rw [ha]
    exact (canonical3243 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA22 + difference 2 4) (sourceB22 + difference 4 2) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA22 + difference 2 4) (sourceB22 + difference 4 2) sourceC22) = raw3244 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3244; decide +kernel
    rw [ha]
    exact (canonical3244 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA22 + difference 2 5) (sourceB22 + difference 5 2) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA22 + difference 2 5) (sourceB22 + difference 5 2) sourceC22) = raw3245 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3245; decide +kernel
    rw [ha]
    exact (canonical3245 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA22 + difference 3 0) (sourceB22 + difference 0 3) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA22 + difference 3 0) (sourceB22 + difference 0 3) sourceC22) = raw3246 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3246; decide +kernel
    rw [ha]
    exact (canonical3246 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA22 + difference 3 1) (sourceB22 + difference 1 3) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA22 + difference 3 1) (sourceB22 + difference 1 3) sourceC22) = raw3247 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3247; decide +kernel
    rw [ha]
    exact (canonical3247 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA22 + difference 3 2) (sourceB22 + difference 2 3) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA22 + difference 3 2) (sourceB22 + difference 2 3) sourceC22) = raw3248 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3248; decide +kernel
    rw [ha]
    exact (canonical3248 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA22 + difference 3 4) (sourceB22 + difference 4 3) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA22 + difference 3 4) (sourceB22 + difference 4 3) sourceC22) = raw3249 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3249; decide +kernel
    rw [ha]
    exact (canonical3249 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA22 + difference 3 5) (sourceB22 + difference 5 3) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA22 + difference 3 5) (sourceB22 + difference 5 3) sourceC22) = raw3250 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3250; decide +kernel
    rw [ha]
    exact (canonical3250 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA22 + difference 4 0) (sourceB22 + difference 0 4) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA22 + difference 4 0) (sourceB22 + difference 0 4) sourceC22) = raw3251 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3251; decide +kernel
    rw [ha]
    exact (canonical3251 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA22 + difference 4 1) (sourceB22 + difference 1 4) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA22 + difference 4 1) (sourceB22 + difference 1 4) sourceC22) = raw3252 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3252; decide +kernel
    rw [ha]
    exact (canonical3252 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA22 + difference 4 2) (sourceB22 + difference 2 4) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA22 + difference 4 2) (sourceB22 + difference 2 4) sourceC22) = raw3253 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3253; decide +kernel
    rw [ha]
    exact (canonical3253 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA22 + difference 4 3) (sourceB22 + difference 3 4) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA22 + difference 4 3) (sourceB22 + difference 3 4) sourceC22) = raw3254 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3254; decide +kernel
    rw [ha]
    exact (canonical3254 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA22 + difference 4 5) (sourceB22 + difference 5 4) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA22 + difference 4 5) (sourceB22 + difference 5 4) sourceC22) = raw3255 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3255; decide +kernel
    rw [ha]
    exact (canonical3255 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA22 + difference 5 0) (sourceB22 + difference 0 5) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA22 + difference 5 0) (sourceB22 + difference 0 5) sourceC22) = raw3256 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3256; decide +kernel
    rw [ha]
    exact (canonical3256 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA22 + difference 5 1) (sourceB22 + difference 1 5) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA22 + difference 5 1) (sourceB22 + difference 1 5) sourceC22) = raw3257 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3257; decide +kernel
    rw [ha]
    exact (canonical3257 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA22 + difference 5 2) (sourceB22 + difference 2 5) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA22 + difference 5 2) (sourceB22 + difference 2 5) sourceC22) = raw3258 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3258; decide +kernel
    rw [ha]
    exact (canonical3258 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA22 + difference 5 3) (sourceB22 + difference 3 5) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA22 + difference 5 3) (sourceB22 + difference 3 5) sourceC22) = raw3259 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3259; decide +kernel
    rw [ha]
    exact (canonical3259 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA22 + difference 5 4) (sourceB22 + difference 4 5) sourceC22) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA22 + difference 5 4) (sourceB22 + difference 4 5) sourceC22) = raw3260 := by
      apply Matrix.ext; unfold tripleCharges sourceA22 sourceB22 sourceC22 difference raw3260; decide +kernel
    rw [ha]
    exact (canonical3260 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA22 sourceB22 sourceC22
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm22, Integer.Sparse.eval]
  linarith only [hs]

def sourceA23 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceB23 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC23 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceForm23 : Integer.Sparse Master := [(Sum.inr 4093, 1), (Sum.inr 5440, 2), (Sum.inr 5442, 2), (Sum.inr 5450, 2), (Sum.inr 5451, 2), (Sum.inr 5452, 2), (Sum.inr 5453, 1), (Sum.inr 5454, 2), (Sum.inr 5485, 4), (Sum.inr 5489, 2), (Sum.inr 5490, 4), (Sum.inr 5492, 2), (Sum.inr 5493, 2), (Sum.inr 5495, 2)]

theorem sourceEq23 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm23 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA23 + difference 0 1) (sourceB23 + difference 1 0) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA23 + difference 0 1) (sourceB23 + difference 1 0) sourceC23) = raw3261 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3261; decide +kernel
    rw [ha]
    exact (canonical3261 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA23 + difference 0 2) (sourceB23 + difference 2 0) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA23 + difference 0 2) (sourceB23 + difference 2 0) sourceC23) = raw3262 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3262; decide +kernel
    rw [ha]
    exact (canonical3262 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA23 + difference 0 3) (sourceB23 + difference 3 0) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA23 + difference 0 3) (sourceB23 + difference 3 0) sourceC23) = raw3263 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3263; decide +kernel
    rw [ha]
    exact (canonical3263 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA23 + difference 0 4) (sourceB23 + difference 4 0) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA23 + difference 0 4) (sourceB23 + difference 4 0) sourceC23) = raw3264 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3264; decide +kernel
    rw [ha]
    exact (canonical3264 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA23 + difference 0 5) (sourceB23 + difference 5 0) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA23 + difference 0 5) (sourceB23 + difference 5 0) sourceC23) = raw3265 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3265; decide +kernel
    rw [ha]
    exact (canonical3265 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA23 + difference 1 0) (sourceB23 + difference 0 1) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA23 + difference 1 0) (sourceB23 + difference 0 1) sourceC23) = raw3266 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3266; decide +kernel
    rw [ha]
    exact (canonical3266 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA23 + difference 1 2) (sourceB23 + difference 2 1) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA23 + difference 1 2) (sourceB23 + difference 2 1) sourceC23) = raw3267 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3267; decide +kernel
    rw [ha]
    exact (canonical3267 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA23 + difference 1 3) (sourceB23 + difference 3 1) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA23 + difference 1 3) (sourceB23 + difference 3 1) sourceC23) = raw3268 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3268; decide +kernel
    rw [ha]
    exact (canonical3268 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA23 + difference 1 4) (sourceB23 + difference 4 1) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA23 + difference 1 4) (sourceB23 + difference 4 1) sourceC23) = raw3269 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3269; decide +kernel
    rw [ha]
    exact (canonical3269 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA23 + difference 1 5) (sourceB23 + difference 5 1) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA23 + difference 1 5) (sourceB23 + difference 5 1) sourceC23) = raw3270 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3270; decide +kernel
    rw [ha]
    exact (canonical3270 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA23 + difference 2 0) (sourceB23 + difference 0 2) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA23 + difference 2 0) (sourceB23 + difference 0 2) sourceC23) = raw3271 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3271; decide +kernel
    rw [ha]
    exact (canonical3271 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA23 + difference 2 1) (sourceB23 + difference 1 2) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA23 + difference 2 1) (sourceB23 + difference 1 2) sourceC23) = raw3272 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3272; decide +kernel
    rw [ha]
    exact (canonical3272 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA23 + difference 2 3) (sourceB23 + difference 3 2) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA23 + difference 2 3) (sourceB23 + difference 3 2) sourceC23) = raw3273 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3273; decide +kernel
    rw [ha]
    exact (canonical3273 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA23 + difference 2 4) (sourceB23 + difference 4 2) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA23 + difference 2 4) (sourceB23 + difference 4 2) sourceC23) = raw3274 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3274; decide +kernel
    rw [ha]
    exact (canonical3274 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA23 + difference 2 5) (sourceB23 + difference 5 2) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA23 + difference 2 5) (sourceB23 + difference 5 2) sourceC23) = raw3275 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3275; decide +kernel
    rw [ha]
    exact (canonical3275 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA23 + difference 3 0) (sourceB23 + difference 0 3) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA23 + difference 3 0) (sourceB23 + difference 0 3) sourceC23) = raw3276 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3276; decide +kernel
    rw [ha]
    exact (canonical3276 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA23 + difference 3 1) (sourceB23 + difference 1 3) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA23 + difference 3 1) (sourceB23 + difference 1 3) sourceC23) = raw3202 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3202; decide +kernel
    rw [ha]
    exact (canonical3202 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA23 + difference 3 2) (sourceB23 + difference 2 3) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA23 + difference 3 2) (sourceB23 + difference 2 3) sourceC23) = raw3277 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3277; decide +kernel
    rw [ha]
    exact (canonical3277 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA23 + difference 3 4) (sourceB23 + difference 4 3) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5495) := by
    have ha : (tripleCharges (sourceA23 + difference 3 4) (sourceB23 + difference 4 3) sourceC23) = raw3186 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3186; decide +kernel
    rw [ha]
    exact (canonical3186 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA23 + difference 3 5) (sourceB23 + difference 5 3) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5495) := by
    have ha : (tripleCharges (sourceA23 + difference 3 5) (sourceB23 + difference 5 3) sourceC23) = raw3278 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3278; decide +kernel
    rw [ha]
    exact (canonical3278 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA23 + difference 4 0) (sourceB23 + difference 0 4) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA23 + difference 4 0) (sourceB23 + difference 0 4) sourceC23) = raw3279 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3279; decide +kernel
    rw [ha]
    exact (canonical3279 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA23 + difference 4 1) (sourceB23 + difference 1 4) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA23 + difference 4 1) (sourceB23 + difference 1 4) sourceC23) = raw3280 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3280; decide +kernel
    rw [ha]
    exact (canonical3280 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA23 + difference 4 2) (sourceB23 + difference 2 4) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA23 + difference 4 2) (sourceB23 + difference 2 4) sourceC23) = raw3281 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3281; decide +kernel
    rw [ha]
    exact (canonical3281 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA23 + difference 4 3) (sourceB23 + difference 3 4) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA23 + difference 4 3) (sourceB23 + difference 3 4) sourceC23) = raw3282 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3282; decide +kernel
    rw [ha]
    exact (canonical3282 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA23 + difference 4 5) (sourceB23 + difference 5 4) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA23 + difference 4 5) (sourceB23 + difference 5 4) sourceC23) = raw3283 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3283; decide +kernel
    rw [ha]
    exact (canonical3283 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA23 + difference 5 0) (sourceB23 + difference 0 5) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA23 + difference 5 0) (sourceB23 + difference 0 5) sourceC23) = raw3284 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3284; decide +kernel
    rw [ha]
    exact (canonical3284 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA23 + difference 5 1) (sourceB23 + difference 1 5) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA23 + difference 5 1) (sourceB23 + difference 1 5) sourceC23) = raw3285 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3285; decide +kernel
    rw [ha]
    exact (canonical3285 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA23 + difference 5 2) (sourceB23 + difference 2 5) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA23 + difference 5 2) (sourceB23 + difference 2 5) sourceC23) = raw3286 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3286; decide +kernel
    rw [ha]
    exact (canonical3286 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA23 + difference 5 3) (sourceB23 + difference 3 5) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA23 + difference 5 3) (sourceB23 + difference 3 5) sourceC23) = raw3287 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3287; decide +kernel
    rw [ha]
    exact (canonical3287 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA23 + difference 5 4) (sourceB23 + difference 4 5) sourceC23) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA23 + difference 5 4) (sourceB23 + difference 4 5) sourceC23) = raw3288 := by
      apply Matrix.ext; unfold tripleCharges sourceA23 sourceB23 sourceC23 difference raw3288; decide +kernel
    rw [ha]
    exact (canonical3288 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA23 sourceB23 sourceC23
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm23, Integer.Sparse.eval]
  linarith only [hs]

def sourceA24 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB24 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC24 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceForm24 : Integer.Sparse Master := [(Sum.inr 4093, 1), (Sum.inr 5292, 2), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5307, 1), (Sum.inr 5433, 2), (Sum.inr 5434, 2), (Sum.inr 5435, 2), (Sum.inr 5440, 2), (Sum.inr 5443, 1), (Sum.inr 5450, 2), (Sum.inr 5451, 1), (Sum.inr 5452, 2), (Sum.inr 5453, 1), (Sum.inr 5454, 3), (Sum.inr 5455, 1), (Sum.inr 5490, 2), (Sum.inr 5492, 1), (Sum.inr 5493, 1), (Sum.inr 5495, 1)]

theorem sourceEq24 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm24 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA24 + difference 0 1) (sourceB24 + difference 1 0) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA24 + difference 0 1) (sourceB24 + difference 1 0) sourceC24) = raw3289 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3289; decide +kernel
    rw [ha]
    exact (canonical3289 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA24 + difference 0 2) (sourceB24 + difference 2 0) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA24 + difference 0 2) (sourceB24 + difference 2 0) sourceC24) = raw3290 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3290; decide +kernel
    rw [ha]
    exact (canonical3290 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA24 + difference 0 3) (sourceB24 + difference 3 0) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA24 + difference 0 3) (sourceB24 + difference 3 0) sourceC24) = raw3291 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3291; decide +kernel
    rw [ha]
    exact (canonical3291 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA24 + difference 0 4) (sourceB24 + difference 4 0) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA24 + difference 0 4) (sourceB24 + difference 4 0) sourceC24) = raw3292 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3292; decide +kernel
    rw [ha]
    exact (canonical3292 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA24 + difference 0 5) (sourceB24 + difference 5 0) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5495) := by
    have ha : (tripleCharges (sourceA24 + difference 0 5) (sourceB24 + difference 5 0) sourceC24) = raw3293 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3293; decide +kernel
    rw [ha]
    exact (canonical3293 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA24 + difference 1 0) (sourceB24 + difference 0 1) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA24 + difference 1 0) (sourceB24 + difference 0 1) sourceC24) = raw3294 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3294; decide +kernel
    rw [ha]
    exact (canonical3294 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA24 + difference 1 2) (sourceB24 + difference 2 1) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA24 + difference 1 2) (sourceB24 + difference 2 1) sourceC24) = raw3295 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3295; decide +kernel
    rw [ha]
    exact (canonical3295 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA24 + difference 1 3) (sourceB24 + difference 3 1) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA24 + difference 1 3) (sourceB24 + difference 3 1) sourceC24) = raw3296 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3296; decide +kernel
    rw [ha]
    exact (canonical3296 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA24 + difference 1 4) (sourceB24 + difference 4 1) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA24 + difference 1 4) (sourceB24 + difference 4 1) sourceC24) = raw3297 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3297; decide +kernel
    rw [ha]
    exact (canonical3297 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA24 + difference 1 5) (sourceB24 + difference 5 1) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA24 + difference 1 5) (sourceB24 + difference 5 1) sourceC24) = raw3298 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3298; decide +kernel
    rw [ha]
    exact (canonical3298 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA24 + difference 2 0) (sourceB24 + difference 0 2) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA24 + difference 2 0) (sourceB24 + difference 0 2) sourceC24) = raw3299 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3299; decide +kernel
    rw [ha]
    exact (canonical3299 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA24 + difference 2 1) (sourceB24 + difference 1 2) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA24 + difference 2 1) (sourceB24 + difference 1 2) sourceC24) = raw3300 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3300; decide +kernel
    rw [ha]
    exact (canonical3300 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA24 + difference 2 3) (sourceB24 + difference 3 2) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA24 + difference 2 3) (sourceB24 + difference 3 2) sourceC24) = raw3301 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3301; decide +kernel
    rw [ha]
    exact (canonical3301 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA24 + difference 2 4) (sourceB24 + difference 4 2) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA24 + difference 2 4) (sourceB24 + difference 4 2) sourceC24) = raw3302 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3302; decide +kernel
    rw [ha]
    exact (canonical3302 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA24 + difference 2 5) (sourceB24 + difference 5 2) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA24 + difference 2 5) (sourceB24 + difference 5 2) sourceC24) = raw3303 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3303; decide +kernel
    rw [ha]
    exact (canonical3303 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA24 + difference 3 0) (sourceB24 + difference 0 3) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA24 + difference 3 0) (sourceB24 + difference 0 3) sourceC24) = raw3304 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3304; decide +kernel
    rw [ha]
    exact (canonical3304 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA24 + difference 3 1) (sourceB24 + difference 1 3) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA24 + difference 3 1) (sourceB24 + difference 1 3) sourceC24) = raw3305 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3305; decide +kernel
    rw [ha]
    exact (canonical3305 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA24 + difference 3 2) (sourceB24 + difference 2 3) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA24 + difference 3 2) (sourceB24 + difference 2 3) sourceC24) = raw3306 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3306; decide +kernel
    rw [ha]
    exact (canonical3306 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA24 + difference 3 4) (sourceB24 + difference 4 3) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA24 + difference 3 4) (sourceB24 + difference 4 3) sourceC24) = raw3307 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3307; decide +kernel
    rw [ha]
    exact (canonical3307 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA24 + difference 3 5) (sourceB24 + difference 5 3) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA24 + difference 3 5) (sourceB24 + difference 5 3) sourceC24) = raw3308 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3308; decide +kernel
    rw [ha]
    exact (canonical3308 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA24 + difference 4 0) (sourceB24 + difference 0 4) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA24 + difference 4 0) (sourceB24 + difference 0 4) sourceC24) = raw3309 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3309; decide +kernel
    rw [ha]
    exact (canonical3309 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA24 + difference 4 1) (sourceB24 + difference 1 4) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA24 + difference 4 1) (sourceB24 + difference 1 4) sourceC24) = raw3310 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3310; decide +kernel
    rw [ha]
    exact (canonical3310 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA24 + difference 4 2) (sourceB24 + difference 2 4) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA24 + difference 4 2) (sourceB24 + difference 2 4) sourceC24) = raw3311 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3311; decide +kernel
    rw [ha]
    exact (canonical3311 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA24 + difference 4 3) (sourceB24 + difference 3 4) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA24 + difference 4 3) (sourceB24 + difference 3 4) sourceC24) = raw3312 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3312; decide +kernel
    rw [ha]
    exact (canonical3312 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA24 + difference 4 5) (sourceB24 + difference 5 4) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA24 + difference 4 5) (sourceB24 + difference 5 4) sourceC24) = raw3313 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3313; decide +kernel
    rw [ha]
    exact (canonical3313 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA24 + difference 5 0) (sourceB24 + difference 0 5) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA24 + difference 5 0) (sourceB24 + difference 0 5) sourceC24) = raw3314 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3314; decide +kernel
    rw [ha]
    exact (canonical3314 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA24 + difference 5 1) (sourceB24 + difference 1 5) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA24 + difference 5 1) (sourceB24 + difference 1 5) sourceC24) = raw3315 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3315; decide +kernel
    rw [ha]
    exact (canonical3315 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA24 + difference 5 2) (sourceB24 + difference 2 5) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA24 + difference 5 2) (sourceB24 + difference 2 5) sourceC24) = raw3316 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3316; decide +kernel
    rw [ha]
    exact (canonical3316 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA24 + difference 5 3) (sourceB24 + difference 3 5) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA24 + difference 5 3) (sourceB24 + difference 3 5) sourceC24) = raw3317 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3317; decide +kernel
    rw [ha]
    exact (canonical3317 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA24 + difference 5 4) (sourceB24 + difference 4 5) sourceC24) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA24 + difference 5 4) (sourceB24 + difference 4 5) sourceC24) = raw3318 := by
      apply Matrix.ext; unfold tripleCharges sourceA24 sourceB24 sourceC24 difference raw3318; decide +kernel
    rw [ha]
    exact (canonical3318 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA24 sourceB24 sourceC24
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm24, Integer.Sparse.eval]
  linarith only [hs]

def sourceA25 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB25 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC25 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm25 : Integer.Sparse Master := [(Sum.inr 4083, 3), (Sum.inr 4084, 2), (Sum.inr 4091, 6), (Sum.inr 4092, 6), (Sum.inr 4093, 6), (Sum.inr 4094, 2), (Sum.inr 4096, 3), (Sum.inr 4097, 2)]

theorem sourceEq25 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm25 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA25 + difference 0 1) (sourceB25 + difference 1 0) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA25 + difference 0 1) (sourceB25 + difference 1 0) sourceC25) = raw3319 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3319; decide +kernel
    rw [ha]
    exact (canonical3319 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA25 + difference 0 2) (sourceB25 + difference 2 0) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA25 + difference 0 2) (sourceB25 + difference 2 0) sourceC25) = raw3320 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3320; decide +kernel
    rw [ha]
    exact (canonical3320 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA25 + difference 0 3) (sourceB25 + difference 3 0) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA25 + difference 0 3) (sourceB25 + difference 3 0) sourceC25) = raw3321 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3321; decide +kernel
    rw [ha]
    exact (canonical3321 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA25 + difference 0 4) (sourceB25 + difference 4 0) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4097) := by
    have ha : (tripleCharges (sourceA25 + difference 0 4) (sourceB25 + difference 4 0) sourceC25) = raw2913 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2913; decide +kernel
    rw [ha]
    exact (canonical2913 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA25 + difference 0 5) (sourceB25 + difference 5 0) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4097) := by
    have ha : (tripleCharges (sourceA25 + difference 0 5) (sourceB25 + difference 5 0) sourceC25) = raw3322 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3322; decide +kernel
    rw [ha]
    exact (canonical3322 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA25 + difference 1 0) (sourceB25 + difference 0 1) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA25 + difference 1 0) (sourceB25 + difference 0 1) sourceC25) = raw3323 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3323; decide +kernel
    rw [ha]
    exact (canonical3323 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA25 + difference 1 2) (sourceB25 + difference 2 1) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA25 + difference 1 2) (sourceB25 + difference 2 1) sourceC25) = raw3324 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3324; decide +kernel
    rw [ha]
    exact (canonical3324 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA25 + difference 1 3) (sourceB25 + difference 3 1) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA25 + difference 1 3) (sourceB25 + difference 3 1) sourceC25) = raw3325 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3325; decide +kernel
    rw [ha]
    exact (canonical3325 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA25 + difference 1 4) (sourceB25 + difference 4 1) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA25 + difference 1 4) (sourceB25 + difference 4 1) sourceC25) = raw2918 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2918; decide +kernel
    rw [ha]
    exact (canonical2918 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA25 + difference 1 5) (sourceB25 + difference 5 1) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA25 + difference 1 5) (sourceB25 + difference 5 1) sourceC25) = raw3326 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3326; decide +kernel
    rw [ha]
    exact (canonical3326 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA25 + difference 2 0) (sourceB25 + difference 0 2) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA25 + difference 2 0) (sourceB25 + difference 0 2) sourceC25) = raw3327 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3327; decide +kernel
    rw [ha]
    exact (canonical3327 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA25 + difference 2 1) (sourceB25 + difference 1 2) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA25 + difference 2 1) (sourceB25 + difference 1 2) sourceC25) = raw3328 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3328; decide +kernel
    rw [ha]
    exact (canonical3328 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA25 + difference 2 3) (sourceB25 + difference 3 2) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA25 + difference 2 3) (sourceB25 + difference 3 2) sourceC25) = raw3329 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3329; decide +kernel
    rw [ha]
    exact (canonical3329 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA25 + difference 2 4) (sourceB25 + difference 4 2) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA25 + difference 2 4) (sourceB25 + difference 4 2) sourceC25) = raw2923 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2923; decide +kernel
    rw [ha]
    exact (canonical2923 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA25 + difference 2 5) (sourceB25 + difference 5 2) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA25 + difference 2 5) (sourceB25 + difference 5 2) sourceC25) = raw3330 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3330; decide +kernel
    rw [ha]
    exact (canonical3330 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA25 + difference 3 0) (sourceB25 + difference 0 3) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA25 + difference 3 0) (sourceB25 + difference 0 3) sourceC25) = raw3331 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3331; decide +kernel
    rw [ha]
    exact (canonical3331 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA25 + difference 3 1) (sourceB25 + difference 1 3) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA25 + difference 3 1) (sourceB25 + difference 1 3) sourceC25) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA25 + difference 3 2) (sourceB25 + difference 2 3) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA25 + difference 3 2) (sourceB25 + difference 2 3) sourceC25) = raw3333 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3333; decide +kernel
    rw [ha]
    exact (canonical3333 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA25 + difference 3 4) (sourceB25 + difference 4 3) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA25 + difference 3 4) (sourceB25 + difference 4 3) sourceC25) = raw2928 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2928; decide +kernel
    rw [ha]
    exact (canonical2928 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA25 + difference 3 5) (sourceB25 + difference 5 3) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA25 + difference 3 5) (sourceB25 + difference 5 3) sourceC25) = raw3334 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3334; decide +kernel
    rw [ha]
    exact (canonical3334 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA25 + difference 4 0) (sourceB25 + difference 0 4) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA25 + difference 4 0) (sourceB25 + difference 0 4) sourceC25) = raw3335 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3335; decide +kernel
    rw [ha]
    exact (canonical3335 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA25 + difference 4 1) (sourceB25 + difference 1 4) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA25 + difference 4 1) (sourceB25 + difference 1 4) sourceC25) = raw3336 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3336; decide +kernel
    rw [ha]
    exact (canonical3336 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA25 + difference 4 2) (sourceB25 + difference 2 4) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA25 + difference 4 2) (sourceB25 + difference 2 4) sourceC25) = raw3337 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3337; decide +kernel
    rw [ha]
    exact (canonical3337 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA25 + difference 4 3) (sourceB25 + difference 3 4) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA25 + difference 4 3) (sourceB25 + difference 3 4) sourceC25) = raw3338 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3338; decide +kernel
    rw [ha]
    exact (canonical3338 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA25 + difference 4 5) (sourceB25 + difference 5 4) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4094) := by
    have ha : (tripleCharges (sourceA25 + difference 4 5) (sourceB25 + difference 5 4) sourceC25) = raw3339 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3339; decide +kernel
    rw [ha]
    exact (canonical3339 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA25 + difference 5 0) (sourceB25 + difference 0 5) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA25 + difference 5 0) (sourceB25 + difference 0 5) sourceC25) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA25 + difference 5 1) (sourceB25 + difference 1 5) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA25 + difference 5 1) (sourceB25 + difference 1 5) sourceC25) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA25 + difference 5 2) (sourceB25 + difference 2 5) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA25 + difference 5 2) (sourceB25 + difference 2 5) sourceC25) = raw2931 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2931; decide +kernel
    rw [ha]
    exact (canonical2931 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA25 + difference 5 3) (sourceB25 + difference 3 5) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA25 + difference 5 3) (sourceB25 + difference 3 5) sourceC25) = raw2932 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2932; decide +kernel
    rw [ha]
    exact (canonical2932 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA25 + difference 5 4) (sourceB25 + difference 4 5) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4094) := by
    have ha : (tripleCharges (sourceA25 + difference 5 4) (sourceB25 + difference 4 5) sourceC25) = raw3340 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3340; decide +kernel
    rw [ha]
    exact (canonical3340 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA25 sourceB25 sourceC25
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm25, Integer.Sparse.eval]
  linarith only [hs]

def sourceA26 : Charge := ![-1, -1, 0, 0, 1, 1]
def sourceB26 : Charge := ![0, 0, 1, 1, -1, -1]
def sourceC26 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceForm26 : Integer.Sparse Master := [(Sum.inr 5405, 8), (Sum.inr 5452, 2), (Sum.inr 5482, 8), (Sum.inr 5489, 4), (Sum.inr 5499, 8)]

theorem sourceEq26 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm26 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA26 + difference 0 1) (sourceB26 + difference 1 0) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA26 + difference 0 1) (sourceB26 + difference 1 0) sourceC26) = raw3341 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3341; decide +kernel
    rw [ha]
    exact (canonical3341 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA26 + difference 0 2) (sourceB26 + difference 2 0) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 0 2) (sourceB26 + difference 2 0) sourceC26) = raw3342 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3342; decide +kernel
    rw [ha]
    exact (canonical3342 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA26 + difference 0 3) (sourceB26 + difference 3 0) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 0 3) (sourceB26 + difference 3 0) sourceC26) = raw3343 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3343; decide +kernel
    rw [ha]
    exact (canonical3343 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA26 + difference 0 4) (sourceB26 + difference 4 0) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 0 4) (sourceB26 + difference 4 0) sourceC26) = raw3344 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3344; decide +kernel
    rw [ha]
    exact (canonical3344 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA26 + difference 0 5) (sourceB26 + difference 5 0) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 0 5) (sourceB26 + difference 5 0) sourceC26) = raw3345 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3345; decide +kernel
    rw [ha]
    exact (canonical3345 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA26 + difference 1 0) (sourceB26 + difference 0 1) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA26 + difference 1 0) (sourceB26 + difference 0 1) sourceC26) = raw3346 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3346; decide +kernel
    rw [ha]
    exact (canonical3346 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA26 + difference 1 2) (sourceB26 + difference 2 1) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 1 2) (sourceB26 + difference 2 1) sourceC26) = raw3347 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3347; decide +kernel
    rw [ha]
    exact (canonical3347 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA26 + difference 1 3) (sourceB26 + difference 3 1) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 1 3) (sourceB26 + difference 3 1) sourceC26) = raw3348 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3348; decide +kernel
    rw [ha]
    exact (canonical3348 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA26 + difference 1 4) (sourceB26 + difference 4 1) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 1 4) (sourceB26 + difference 4 1) sourceC26) = raw3349 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3349; decide +kernel
    rw [ha]
    exact (canonical3349 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA26 + difference 1 5) (sourceB26 + difference 5 1) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 1 5) (sourceB26 + difference 5 1) sourceC26) = raw3350 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3350; decide +kernel
    rw [ha]
    exact (canonical3350 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA26 + difference 2 0) (sourceB26 + difference 0 2) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 2 0) (sourceB26 + difference 0 2) sourceC26) = raw3351 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3351; decide +kernel
    rw [ha]
    exact (canonical3351 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA26 + difference 2 1) (sourceB26 + difference 1 2) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 2 1) (sourceB26 + difference 1 2) sourceC26) = raw3352 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3352; decide +kernel
    rw [ha]
    exact (canonical3352 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA26 + difference 2 3) (sourceB26 + difference 3 2) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA26 + difference 2 3) (sourceB26 + difference 3 2) sourceC26) = raw3353 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3353; decide +kernel
    rw [ha]
    exact (canonical3353 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA26 + difference 2 4) (sourceB26 + difference 4 2) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 2 4) (sourceB26 + difference 4 2) sourceC26) = raw3354 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3354; decide +kernel
    rw [ha]
    exact (canonical3354 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA26 + difference 2 5) (sourceB26 + difference 5 2) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 2 5) (sourceB26 + difference 5 2) sourceC26) = raw3355 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3355; decide +kernel
    rw [ha]
    exact (canonical3355 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA26 + difference 3 0) (sourceB26 + difference 0 3) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 3 0) (sourceB26 + difference 0 3) sourceC26) = raw3356 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3356; decide +kernel
    rw [ha]
    exact (canonical3356 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA26 + difference 3 1) (sourceB26 + difference 1 3) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 3 1) (sourceB26 + difference 1 3) sourceC26) = raw3357 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3357; decide +kernel
    rw [ha]
    exact (canonical3357 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA26 + difference 3 2) (sourceB26 + difference 2 3) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA26 + difference 3 2) (sourceB26 + difference 2 3) sourceC26) = raw3358 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3358; decide +kernel
    rw [ha]
    exact (canonical3358 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA26 + difference 3 4) (sourceB26 + difference 4 3) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 3 4) (sourceB26 + difference 4 3) sourceC26) = raw3359 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3359; decide +kernel
    rw [ha]
    exact (canonical3359 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA26 + difference 3 5) (sourceB26 + difference 5 3) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 3 5) (sourceB26 + difference 5 3) sourceC26) = raw3360 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3360; decide +kernel
    rw [ha]
    exact (canonical3360 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA26 + difference 4 0) (sourceB26 + difference 0 4) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 4 0) (sourceB26 + difference 0 4) sourceC26) = raw3361 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3361; decide +kernel
    rw [ha]
    exact (canonical3361 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA26 + difference 4 1) (sourceB26 + difference 1 4) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 4 1) (sourceB26 + difference 1 4) sourceC26) = raw3362 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3362; decide +kernel
    rw [ha]
    exact (canonical3362 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA26 + difference 4 2) (sourceB26 + difference 2 4) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 4 2) (sourceB26 + difference 2 4) sourceC26) = raw3363 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3363; decide +kernel
    rw [ha]
    exact (canonical3363 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA26 + difference 4 3) (sourceB26 + difference 3 4) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 4 3) (sourceB26 + difference 3 4) sourceC26) = raw3364 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3364; decide +kernel
    rw [ha]
    exact (canonical3364 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA26 + difference 4 5) (sourceB26 + difference 5 4) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA26 + difference 4 5) (sourceB26 + difference 5 4) sourceC26) = raw3365 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3365; decide +kernel
    rw [ha]
    exact (canonical3365 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA26 + difference 5 0) (sourceB26 + difference 0 5) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 5 0) (sourceB26 + difference 0 5) sourceC26) = raw3366 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3366; decide +kernel
    rw [ha]
    exact (canonical3366 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA26 + difference 5 1) (sourceB26 + difference 1 5) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 5 1) (sourceB26 + difference 1 5) sourceC26) = raw3367 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3367; decide +kernel
    rw [ha]
    exact (canonical3367 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA26 + difference 5 2) (sourceB26 + difference 2 5) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 5 2) (sourceB26 + difference 2 5) sourceC26) = raw3368 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3368; decide +kernel
    rw [ha]
    exact (canonical3368 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA26 + difference 5 3) (sourceB26 + difference 3 5) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 5 3) (sourceB26 + difference 3 5) sourceC26) = raw3369 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3369; decide +kernel
    rw [ha]
    exact (canonical3369 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA26 + difference 5 4) (sourceB26 + difference 4 5) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA26 + difference 5 4) (sourceB26 + difference 4 5) sourceC26) = raw3370 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3370; decide +kernel
    rw [ha]
    exact (canonical3370 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA26 sourceB26 sourceC26
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm26, Integer.Sparse.eval]
  linarith only [hs]

def sourceA27 : Charge := ![-1, -1, 0, 0, 1, 1]
def sourceB27 : Charge := ![0, 1, -1, 1, -1, 0]
def sourceC27 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceForm27 : Integer.Sparse Master := [(Sum.inr 5423, 1), (Sum.inr 5424, 4), (Sum.inr 5433, 4), (Sum.inr 5477, 2), (Sum.inr 5478, 2), (Sum.inr 5482, 4), (Sum.inr 5490, 4), (Sum.inr 5497, 2), (Sum.inr 5499, 4), (Sum.inr 5500, 2), (Sum.inr 5501, 1)]

theorem sourceEq27 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm27 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA27 + difference 0 1) (sourceB27 + difference 1 0) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA27 + difference 0 1) (sourceB27 + difference 1 0) sourceC27) = raw3371 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3371; decide +kernel
    rw [ha]
    exact (canonical3371 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA27 + difference 0 2) (sourceB27 + difference 2 0) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA27 + difference 0 2) (sourceB27 + difference 2 0) sourceC27) = raw3372 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3372; decide +kernel
    rw [ha]
    exact (canonical3372 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA27 + difference 0 3) (sourceB27 + difference 3 0) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA27 + difference 0 3) (sourceB27 + difference 3 0) sourceC27) = raw3373 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3373; decide +kernel
    rw [ha]
    exact (canonical3373 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA27 + difference 0 4) (sourceB27 + difference 4 0) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA27 + difference 0 4) (sourceB27 + difference 4 0) sourceC27) = raw3374 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3374; decide +kernel
    rw [ha]
    exact (canonical3374 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA27 + difference 0 5) (sourceB27 + difference 5 0) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5497) := by
    have ha : (tripleCharges (sourceA27 + difference 0 5) (sourceB27 + difference 5 0) sourceC27) = raw3375 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3375; decide +kernel
    rw [ha]
    exact (canonical3375 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA27 + difference 1 0) (sourceB27 + difference 0 1) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA27 + difference 1 0) (sourceB27 + difference 0 1) sourceC27) = raw3376 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3376; decide +kernel
    rw [ha]
    exact (canonical3376 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA27 + difference 1 2) (sourceB27 + difference 2 1) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA27 + difference 1 2) (sourceB27 + difference 2 1) sourceC27) = raw3377 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3377; decide +kernel
    rw [ha]
    exact (canonical3377 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA27 + difference 1 3) (sourceB27 + difference 3 1) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA27 + difference 1 3) (sourceB27 + difference 3 1) sourceC27) = raw3378 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3378; decide +kernel
    rw [ha]
    exact (canonical3378 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA27 + difference 1 4) (sourceB27 + difference 4 1) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5501) := by
    have ha : (tripleCharges (sourceA27 + difference 1 4) (sourceB27 + difference 4 1) sourceC27) = raw3379 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3379; decide +kernel
    rw [ha]
    exact (canonical3379 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA27 + difference 1 5) (sourceB27 + difference 5 1) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA27 + difference 1 5) (sourceB27 + difference 5 1) sourceC27) = raw3380 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3380; decide +kernel
    rw [ha]
    exact (canonical3380 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA27 + difference 2 0) (sourceB27 + difference 0 2) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA27 + difference 2 0) (sourceB27 + difference 0 2) sourceC27) = raw3381 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3381; decide +kernel
    rw [ha]
    exact (canonical3381 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA27 + difference 2 1) (sourceB27 + difference 1 2) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA27 + difference 2 1) (sourceB27 + difference 1 2) sourceC27) = raw3382 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3382; decide +kernel
    rw [ha]
    exact (canonical3382 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA27 + difference 2 3) (sourceB27 + difference 3 2) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA27 + difference 2 3) (sourceB27 + difference 3 2) sourceC27) = raw3383 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3383; decide +kernel
    rw [ha]
    exact (canonical3383 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA27 + difference 2 4) (sourceB27 + difference 4 2) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA27 + difference 2 4) (sourceB27 + difference 4 2) sourceC27) = raw3384 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3384; decide +kernel
    rw [ha]
    exact (canonical3384 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA27 + difference 2 5) (sourceB27 + difference 5 2) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA27 + difference 2 5) (sourceB27 + difference 5 2) sourceC27) = raw3385 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3385; decide +kernel
    rw [ha]
    exact (canonical3385 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA27 + difference 3 0) (sourceB27 + difference 0 3) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA27 + difference 3 0) (sourceB27 + difference 0 3) sourceC27) = raw3386 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3386; decide +kernel
    rw [ha]
    exact (canonical3386 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA27 + difference 3 1) (sourceB27 + difference 1 3) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA27 + difference 3 1) (sourceB27 + difference 1 3) sourceC27) = raw3387 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3387; decide +kernel
    rw [ha]
    exact (canonical3387 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA27 + difference 3 2) (sourceB27 + difference 2 3) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5497) := by
    have ha : (tripleCharges (sourceA27 + difference 3 2) (sourceB27 + difference 2 3) sourceC27) = raw3388 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3388; decide +kernel
    rw [ha]
    exact (canonical3388 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA27 + difference 3 4) (sourceB27 + difference 4 3) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA27 + difference 3 4) (sourceB27 + difference 4 3) sourceC27) = raw3389 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3389; decide +kernel
    rw [ha]
    exact (canonical3389 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA27 + difference 3 5) (sourceB27 + difference 5 3) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA27 + difference 3 5) (sourceB27 + difference 5 3) sourceC27) = raw3390 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3390; decide +kernel
    rw [ha]
    exact (canonical3390 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA27 + difference 4 0) (sourceB27 + difference 0 4) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA27 + difference 4 0) (sourceB27 + difference 0 4) sourceC27) = raw3391 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3391; decide +kernel
    rw [ha]
    exact (canonical3391 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA27 + difference 4 1) (sourceB27 + difference 1 4) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA27 + difference 4 1) (sourceB27 + difference 1 4) sourceC27) = raw3392 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3392; decide +kernel
    rw [ha]
    exact (canonical3392 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA27 + difference 4 2) (sourceB27 + difference 2 4) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA27 + difference 4 2) (sourceB27 + difference 2 4) sourceC27) = raw3393 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3393; decide +kernel
    rw [ha]
    exact (canonical3393 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA27 + difference 4 3) (sourceB27 + difference 3 4) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA27 + difference 4 3) (sourceB27 + difference 3 4) sourceC27) = raw3394 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3394; decide +kernel
    rw [ha]
    exact (canonical3394 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA27 + difference 4 5) (sourceB27 + difference 5 4) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA27 + difference 4 5) (sourceB27 + difference 5 4) sourceC27) = raw3395 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3395; decide +kernel
    rw [ha]
    exact (canonical3395 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA27 + difference 5 0) (sourceB27 + difference 0 5) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA27 + difference 5 0) (sourceB27 + difference 0 5) sourceC27) = raw3396 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3396; decide +kernel
    rw [ha]
    exact (canonical3396 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA27 + difference 5 1) (sourceB27 + difference 1 5) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA27 + difference 5 1) (sourceB27 + difference 1 5) sourceC27) = raw3397 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3397; decide +kernel
    rw [ha]
    exact (canonical3397 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA27 + difference 5 2) (sourceB27 + difference 2 5) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA27 + difference 5 2) (sourceB27 + difference 2 5) sourceC27) = raw3398 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3398; decide +kernel
    rw [ha]
    exact (canonical3398 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA27 + difference 5 3) (sourceB27 + difference 3 5) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA27 + difference 5 3) (sourceB27 + difference 3 5) sourceC27) = raw3399 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3399; decide +kernel
    rw [ha]
    exact (canonical3399 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA27 + difference 5 4) (sourceB27 + difference 4 5) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA27 + difference 5 4) (sourceB27 + difference 4 5) sourceC27) = raw3400 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3400; decide +kernel
    rw [ha]
    exact (canonical3400 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA27 sourceB27 sourceC27
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm27, Integer.Sparse.eval]
  linarith only [hs]

def sourceA28 : Charge := ![-1, -1, 0, 0, 1, 1]
def sourceB28 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC28 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceForm28 : Integer.Sparse Master := [(Sum.inr 4096, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 2), (Sum.inr 5439, 1), (Sum.inr 5452, 1), (Sum.inr 5482, 3), (Sum.inr 5483, 2), (Sum.inr 5485, 1), (Sum.inr 5486, 2), (Sum.inr 5489, 1), (Sum.inr 5490, 4), (Sum.inr 5493, 1), (Sum.inr 5497, 1), (Sum.inr 5498, 1), (Sum.inr 5499, 4), (Sum.inr 5500, 2), (Sum.inr 5501, 2)]

theorem sourceEq28 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm28 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA28 + difference 0 1) (sourceB28 + difference 1 0) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA28 + difference 0 1) (sourceB28 + difference 1 0) sourceC28) = raw3401 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3401; decide +kernel
    rw [ha]
    exact (canonical3401 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA28 + difference 0 2) (sourceB28 + difference 2 0) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA28 + difference 0 2) (sourceB28 + difference 2 0) sourceC28) = raw3402 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3402; decide +kernel
    rw [ha]
    exact (canonical3402 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA28 + difference 0 3) (sourceB28 + difference 3 0) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA28 + difference 0 3) (sourceB28 + difference 3 0) sourceC28) = raw3403 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3403; decide +kernel
    rw [ha]
    exact (canonical3403 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA28 + difference 0 4) (sourceB28 + difference 4 0) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5501) := by
    have ha : (tripleCharges (sourceA28 + difference 0 4) (sourceB28 + difference 4 0) sourceC28) = raw3404 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3404; decide +kernel
    rw [ha]
    exact (canonical3404 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA28 + difference 0 5) (sourceB28 + difference 5 0) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5501) := by
    have ha : (tripleCharges (sourceA28 + difference 0 5) (sourceB28 + difference 5 0) sourceC28) = raw3405 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3405; decide +kernel
    rw [ha]
    exact (canonical3405 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA28 + difference 1 0) (sourceB28 + difference 0 1) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA28 + difference 1 0) (sourceB28 + difference 0 1) sourceC28) = raw3406 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3406; decide +kernel
    rw [ha]
    exact (canonical3406 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA28 + difference 1 2) (sourceB28 + difference 2 1) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5498) := by
    have ha : (tripleCharges (sourceA28 + difference 1 2) (sourceB28 + difference 2 1) sourceC28) = raw3407 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3407; decide +kernel
    rw [ha]
    exact (canonical3407 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA28 + difference 1 3) (sourceB28 + difference 3 1) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA28 + difference 1 3) (sourceB28 + difference 3 1) sourceC28) = raw3408 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3408; decide +kernel
    rw [ha]
    exact (canonical3408 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA28 + difference 1 4) (sourceB28 + difference 4 1) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA28 + difference 1 4) (sourceB28 + difference 4 1) sourceC28) = raw3409 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3409; decide +kernel
    rw [ha]
    exact (canonical3409 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA28 + difference 1 5) (sourceB28 + difference 5 1) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA28 + difference 1 5) (sourceB28 + difference 5 1) sourceC28) = raw3410 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3410; decide +kernel
    rw [ha]
    exact (canonical3410 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA28 + difference 2 0) (sourceB28 + difference 0 2) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA28 + difference 2 0) (sourceB28 + difference 0 2) sourceC28) = raw3411 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3411; decide +kernel
    rw [ha]
    exact (canonical3411 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA28 + difference 2 1) (sourceB28 + difference 1 2) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA28 + difference 2 1) (sourceB28 + difference 1 2) sourceC28) = raw3412 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3412; decide +kernel
    rw [ha]
    exact (canonical3412 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA28 + difference 2 3) (sourceB28 + difference 3 2) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5497) := by
    have ha : (tripleCharges (sourceA28 + difference 2 3) (sourceB28 + difference 3 2) sourceC28) = raw3413 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3413; decide +kernel
    rw [ha]
    exact (canonical3413 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA28 + difference 2 4) (sourceB28 + difference 4 2) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA28 + difference 2 4) (sourceB28 + difference 4 2) sourceC28) = raw3414 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3414; decide +kernel
    rw [ha]
    exact (canonical3414 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA28 + difference 2 5) (sourceB28 + difference 5 2) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA28 + difference 2 5) (sourceB28 + difference 5 2) sourceC28) = raw3415 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3415; decide +kernel
    rw [ha]
    exact (canonical3415 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA28 + difference 3 0) (sourceB28 + difference 0 3) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA28 + difference 3 0) (sourceB28 + difference 0 3) sourceC28) = raw3416 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3416; decide +kernel
    rw [ha]
    exact (canonical3416 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA28 + difference 3 1) (sourceB28 + difference 1 3) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA28 + difference 3 1) (sourceB28 + difference 1 3) sourceC28) = raw3417 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3417; decide +kernel
    rw [ha]
    exact (canonical3417 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA28 + difference 3 2) (sourceB28 + difference 2 3) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA28 + difference 3 2) (sourceB28 + difference 2 3) sourceC28) = raw3418 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3418; decide +kernel
    rw [ha]
    exact (canonical3418 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA28 + difference 3 4) (sourceB28 + difference 4 3) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA28 + difference 3 4) (sourceB28 + difference 4 3) sourceC28) = raw3419 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3419; decide +kernel
    rw [ha]
    exact (canonical3419 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA28 + difference 3 5) (sourceB28 + difference 5 3) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA28 + difference 3 5) (sourceB28 + difference 5 3) sourceC28) = raw3420 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3420; decide +kernel
    rw [ha]
    exact (canonical3420 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA28 + difference 4 0) (sourceB28 + difference 0 4) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA28 + difference 4 0) (sourceB28 + difference 0 4) sourceC28) = raw3421 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3421; decide +kernel
    rw [ha]
    exact (canonical3421 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA28 + difference 4 1) (sourceB28 + difference 1 4) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA28 + difference 4 1) (sourceB28 + difference 1 4) sourceC28) = raw3422 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3422; decide +kernel
    rw [ha]
    exact (canonical3422 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA28 + difference 4 2) (sourceB28 + difference 2 4) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA28 + difference 4 2) (sourceB28 + difference 2 4) sourceC28) = raw3423 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3423; decide +kernel
    rw [ha]
    exact (canonical3423 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA28 + difference 4 3) (sourceB28 + difference 3 4) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA28 + difference 4 3) (sourceB28 + difference 3 4) sourceC28) = raw3424 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3424; decide +kernel
    rw [ha]
    exact (canonical3424 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA28 + difference 4 5) (sourceB28 + difference 5 4) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA28 + difference 4 5) (sourceB28 + difference 5 4) sourceC28) = raw3425 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3425; decide +kernel
    rw [ha]
    exact (canonical3425 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA28 + difference 5 0) (sourceB28 + difference 0 5) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA28 + difference 5 0) (sourceB28 + difference 0 5) sourceC28) = raw3426 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3426; decide +kernel
    rw [ha]
    exact (canonical3426 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA28 + difference 5 1) (sourceB28 + difference 1 5) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA28 + difference 5 1) (sourceB28 + difference 1 5) sourceC28) = raw3427 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3427; decide +kernel
    rw [ha]
    exact (canonical3427 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA28 + difference 5 2) (sourceB28 + difference 2 5) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA28 + difference 5 2) (sourceB28 + difference 2 5) sourceC28) = raw3428 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3428; decide +kernel
    rw [ha]
    exact (canonical3428 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA28 + difference 5 3) (sourceB28 + difference 3 5) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA28 + difference 5 3) (sourceB28 + difference 3 5) sourceC28) = raw3429 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3429; decide +kernel
    rw [ha]
    exact (canonical3429 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA28 + difference 5 4) (sourceB28 + difference 4 5) sourceC28) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA28 + difference 5 4) (sourceB28 + difference 4 5) sourceC28) = raw3430 := by
      apply Matrix.ext; unfold tripleCharges sourceA28 sourceB28 sourceC28 difference raw3430; decide +kernel
    rw [ha]
    exact (canonical3430 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA28 sourceB28 sourceC28
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm28, Integer.Sparse.eval]
  linarith only [hs]

def sourceA29 : Charge := ![-1, -1, 0, 0, 1, 1]
def sourceB29 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC29 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm29 : Integer.Sparse Master := [(Sum.inr 4091, 8), (Sum.inr 4092, 4), (Sum.inr 4093, 4), (Sum.inr 4095, 2), (Sum.inr 4096, 8), (Sum.inr 4097, 4)]

theorem sourceEq29 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm29 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA29 + difference 0 1) (sourceB29 + difference 1 0) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA29 + difference 0 1) (sourceB29 + difference 1 0) sourceC29) = raw3431 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3431; decide +kernel
    rw [ha]
    exact (canonical3431 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA29 + difference 0 2) (sourceB29 + difference 2 0) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 0 2) (sourceB29 + difference 2 0) sourceC29) = raw3432 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3432; decide +kernel
    rw [ha]
    exact (canonical3432 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA29 + difference 0 3) (sourceB29 + difference 3 0) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 0 3) (sourceB29 + difference 3 0) sourceC29) = raw3433 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3433; decide +kernel
    rw [ha]
    exact (canonical3433 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA29 + difference 0 4) (sourceB29 + difference 4 0) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4097) := by
    have ha : (tripleCharges (sourceA29 + difference 0 4) (sourceB29 + difference 4 0) sourceC29) = raw3434 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3434; decide +kernel
    rw [ha]
    exact (canonical3434 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA29 + difference 0 5) (sourceB29 + difference 5 0) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4097) := by
    have ha : (tripleCharges (sourceA29 + difference 0 5) (sourceB29 + difference 5 0) sourceC29) = raw3435 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3435; decide +kernel
    rw [ha]
    exact (canonical3435 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA29 + difference 1 0) (sourceB29 + difference 0 1) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA29 + difference 1 0) (sourceB29 + difference 0 1) sourceC29) = raw2933 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw2933; decide +kernel
    rw [ha]
    exact (canonical2933 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA29 + difference 1 2) (sourceB29 + difference 2 1) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 1 2) (sourceB29 + difference 2 1) sourceC29) = raw3320 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3320; decide +kernel
    rw [ha]
    exact (canonical3320 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA29 + difference 1 3) (sourceB29 + difference 3 1) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 1 3) (sourceB29 + difference 3 1) sourceC29) = raw3321 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3321; decide +kernel
    rw [ha]
    exact (canonical3321 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA29 + difference 1 4) (sourceB29 + difference 4 1) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4097) := by
    have ha : (tripleCharges (sourceA29 + difference 1 4) (sourceB29 + difference 4 1) sourceC29) = raw2913 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw2913; decide +kernel
    rw [ha]
    exact (canonical2913 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA29 + difference 1 5) (sourceB29 + difference 5 1) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4097) := by
    have ha : (tripleCharges (sourceA29 + difference 1 5) (sourceB29 + difference 5 1) sourceC29) = raw3322 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3322; decide +kernel
    rw [ha]
    exact (canonical3322 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA29 + difference 2 0) (sourceB29 + difference 0 2) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 2 0) (sourceB29 + difference 0 2) sourceC29) = raw3328 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3328; decide +kernel
    rw [ha]
    exact (canonical3328 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA29 + difference 2 1) (sourceB29 + difference 1 2) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 2 1) (sourceB29 + difference 1 2) sourceC29) = raw3436 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3436; decide +kernel
    rw [ha]
    exact (canonical3436 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA29 + difference 2 3) (sourceB29 + difference 3 2) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4095) := by
    have ha : (tripleCharges (sourceA29 + difference 2 3) (sourceB29 + difference 3 2) sourceC29) = raw3437 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3437; decide +kernel
    rw [ha]
    exact (canonical3437 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA29 + difference 2 4) (sourceB29 + difference 4 2) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 2 4) (sourceB29 + difference 4 2) sourceC29) = raw3438 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3438; decide +kernel
    rw [ha]
    exact (canonical3438 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA29 + difference 2 5) (sourceB29 + difference 5 2) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 2 5) (sourceB29 + difference 5 2) sourceC29) = raw3439 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3439; decide +kernel
    rw [ha]
    exact (canonical3439 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA29 + difference 3 0) (sourceB29 + difference 0 3) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 3 0) (sourceB29 + difference 0 3) sourceC29) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA29 + difference 3 1) (sourceB29 + difference 1 3) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 3 1) (sourceB29 + difference 1 3) sourceC29) = raw3440 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3440; decide +kernel
    rw [ha]
    exact (canonical3440 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA29 + difference 3 2) (sourceB29 + difference 2 3) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4095) := by
    have ha : (tripleCharges (sourceA29 + difference 3 2) (sourceB29 + difference 2 3) sourceC29) = raw3441 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3441; decide +kernel
    rw [ha]
    exact (canonical3441 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA29 + difference 3 4) (sourceB29 + difference 4 3) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 3 4) (sourceB29 + difference 4 3) sourceC29) = raw3442 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3442; decide +kernel
    rw [ha]
    exact (canonical3442 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA29 + difference 3 5) (sourceB29 + difference 5 3) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 3 5) (sourceB29 + difference 5 3) sourceC29) = raw3443 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3443; decide +kernel
    rw [ha]
    exact (canonical3443 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA29 + difference 4 0) (sourceB29 + difference 0 4) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA29 + difference 4 0) (sourceB29 + difference 0 4) sourceC29) = raw3336 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3336; decide +kernel
    rw [ha]
    exact (canonical3336 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA29 + difference 4 1) (sourceB29 + difference 1 4) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA29 + difference 4 1) (sourceB29 + difference 1 4) sourceC29) = raw3444 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3444; decide +kernel
    rw [ha]
    exact (canonical3444 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA29 + difference 4 2) (sourceB29 + difference 2 4) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 4 2) (sourceB29 + difference 2 4) sourceC29) = raw3445 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3445; decide +kernel
    rw [ha]
    exact (canonical3445 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA29 + difference 4 3) (sourceB29 + difference 3 4) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 4 3) (sourceB29 + difference 3 4) sourceC29) = raw3446 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3446; decide +kernel
    rw [ha]
    exact (canonical3446 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA29 + difference 4 5) (sourceB29 + difference 5 4) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA29 + difference 4 5) (sourceB29 + difference 5 4) sourceC29) = raw3447 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3447; decide +kernel
    rw [ha]
    exact (canonical3447 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA29 + difference 5 0) (sourceB29 + difference 0 5) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA29 + difference 5 0) (sourceB29 + difference 0 5) sourceC29) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA29 + difference 5 1) (sourceB29 + difference 1 5) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA29 + difference 5 1) (sourceB29 + difference 1 5) sourceC29) = raw3448 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3448; decide +kernel
    rw [ha]
    exact (canonical3448 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA29 + difference 5 2) (sourceB29 + difference 2 5) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 5 2) (sourceB29 + difference 2 5) sourceC29) = raw3449 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3449; decide +kernel
    rw [ha]
    exact (canonical3449 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA29 + difference 5 3) (sourceB29 + difference 3 5) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 5 3) (sourceB29 + difference 3 5) sourceC29) = raw3450 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3450; decide +kernel
    rw [ha]
    exact (canonical3450 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA29 + difference 5 4) (sourceB29 + difference 4 5) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA29 + difference 5 4) (sourceB29 + difference 4 5) sourceC29) = raw2909 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw2909; decide +kernel
    rw [ha]
    exact (canonical2909 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA29 sourceB29 sourceC29
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm29, Integer.Sparse.eval]
  linarith only [hs]

def sourceA30 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB30 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC30 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm30 : Integer.Sparse Master := [(Sum.inr 4281, 3), (Sum.inr 4282, 2), (Sum.inr 4484, 6), (Sum.inr 4508, 2), (Sum.inr 4751, 6), (Sum.inr 4844, 6), (Sum.inr 4892, 3), (Sum.inr 4899, 2)]

theorem sourceEq30 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm30 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA30 + difference 0 1) (sourceB30 + difference 1 0) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA30 + difference 0 1) (sourceB30 + difference 1 0) sourceC30) = raw3451 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3451; decide +kernel
    rw [ha]
    exact (canonical3451 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA30 + difference 0 2) (sourceB30 + difference 2 0) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA30 + difference 0 2) (sourceB30 + difference 2 0) sourceC30) = raw3452 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3452; decide +kernel
    rw [ha]
    exact (canonical3452 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA30 + difference 0 3) (sourceB30 + difference 3 0) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA30 + difference 0 3) (sourceB30 + difference 3 0) sourceC30) = raw3453 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3453; decide +kernel
    rw [ha]
    exact (canonical3453 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA30 + difference 0 4) (sourceB30 + difference 4 0) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4508) := by
    have ha : (tripleCharges (sourceA30 + difference 0 4) (sourceB30 + difference 4 0) sourceC30) = raw3454 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3454; decide +kernel
    rw [ha]
    exact (canonical3454 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA30 + difference 0 5) (sourceB30 + difference 5 0) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA30 + difference 0 5) (sourceB30 + difference 5 0) sourceC30) = raw3455 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3455; decide +kernel
    rw [ha]
    exact (canonical3455 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA30 + difference 1 0) (sourceB30 + difference 0 1) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4484) := by
    have ha : (tripleCharges (sourceA30 + difference 1 0) (sourceB30 + difference 0 1) sourceC30) = raw3456 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3456; decide +kernel
    rw [ha]
    exact (canonical3456 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA30 + difference 1 2) (sourceB30 + difference 2 1) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4751) := by
    have ha : (tripleCharges (sourceA30 + difference 1 2) (sourceB30 + difference 2 1) sourceC30) = raw3457 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3457; decide +kernel
    rw [ha]
    exact (canonical3457 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA30 + difference 1 3) (sourceB30 + difference 3 1) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4751) := by
    have ha : (tripleCharges (sourceA30 + difference 1 3) (sourceB30 + difference 3 1) sourceC30) = raw3458 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3458; decide +kernel
    rw [ha]
    exact (canonical3458 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA30 + difference 1 4) (sourceB30 + difference 4 1) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4484) := by
    have ha : (tripleCharges (sourceA30 + difference 1 4) (sourceB30 + difference 4 1) sourceC30) = raw3459 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3459; decide +kernel
    rw [ha]
    exact (canonical3459 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA30 + difference 1 5) (sourceB30 + difference 5 1) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA30 + difference 1 5) (sourceB30 + difference 5 1) sourceC30) = raw3460 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3460; decide +kernel
    rw [ha]
    exact (canonical3460 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA30 + difference 2 0) (sourceB30 + difference 0 2) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4484) := by
    have ha : (tripleCharges (sourceA30 + difference 2 0) (sourceB30 + difference 0 2) sourceC30) = raw3461 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3461; decide +kernel
    rw [ha]
    exact (canonical3461 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA30 + difference 2 1) (sourceB30 + difference 1 2) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4751) := by
    have ha : (tripleCharges (sourceA30 + difference 2 1) (sourceB30 + difference 1 2) sourceC30) = raw3462 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3462; decide +kernel
    rw [ha]
    exact (canonical3462 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA30 + difference 2 3) (sourceB30 + difference 3 2) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4751) := by
    have ha : (tripleCharges (sourceA30 + difference 2 3) (sourceB30 + difference 3 2) sourceC30) = raw3463 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3463; decide +kernel
    rw [ha]
    exact (canonical3463 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA30 + difference 2 4) (sourceB30 + difference 4 2) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4484) := by
    have ha : (tripleCharges (sourceA30 + difference 2 4) (sourceB30 + difference 4 2) sourceC30) = raw3464 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3464; decide +kernel
    rw [ha]
    exact (canonical3464 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA30 + difference 2 5) (sourceB30 + difference 5 2) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA30 + difference 2 5) (sourceB30 + difference 5 2) sourceC30) = raw3465 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3465; decide +kernel
    rw [ha]
    exact (canonical3465 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA30 + difference 3 0) (sourceB30 + difference 0 3) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4484) := by
    have ha : (tripleCharges (sourceA30 + difference 3 0) (sourceB30 + difference 0 3) sourceC30) = raw3466 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3466; decide +kernel
    rw [ha]
    exact (canonical3466 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA30 + difference 3 1) (sourceB30 + difference 1 3) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4751) := by
    have ha : (tripleCharges (sourceA30 + difference 3 1) (sourceB30 + difference 1 3) sourceC30) = raw3467 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3467; decide +kernel
    rw [ha]
    exact (canonical3467 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA30 + difference 3 2) (sourceB30 + difference 2 3) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4751) := by
    have ha : (tripleCharges (sourceA30 + difference 3 2) (sourceB30 + difference 2 3) sourceC30) = raw3468 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3468; decide +kernel
    rw [ha]
    exact (canonical3468 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA30 + difference 3 4) (sourceB30 + difference 4 3) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4484) := by
    have ha : (tripleCharges (sourceA30 + difference 3 4) (sourceB30 + difference 4 3) sourceC30) = raw3469 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3469; decide +kernel
    rw [ha]
    exact (canonical3469 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA30 + difference 3 5) (sourceB30 + difference 5 3) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA30 + difference 3 5) (sourceB30 + difference 5 3) sourceC30) = raw3470 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3470; decide +kernel
    rw [ha]
    exact (canonical3470 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA30 + difference 4 0) (sourceB30 + difference 0 4) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4508) := by
    have ha : (tripleCharges (sourceA30 + difference 4 0) (sourceB30 + difference 0 4) sourceC30) = raw3471 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3471; decide +kernel
    rw [ha]
    exact (canonical3471 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA30 + difference 4 1) (sourceB30 + difference 1 4) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA30 + difference 4 1) (sourceB30 + difference 1 4) sourceC30) = raw3472 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3472; decide +kernel
    rw [ha]
    exact (canonical3472 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA30 + difference 4 2) (sourceB30 + difference 2 4) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA30 + difference 4 2) (sourceB30 + difference 2 4) sourceC30) = raw3473 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3473; decide +kernel
    rw [ha]
    exact (canonical3473 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA30 + difference 4 3) (sourceB30 + difference 3 4) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA30 + difference 4 3) (sourceB30 + difference 3 4) sourceC30) = raw3474 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3474; decide +kernel
    rw [ha]
    exact (canonical3474 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA30 + difference 4 5) (sourceB30 + difference 5 4) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA30 + difference 4 5) (sourceB30 + difference 5 4) sourceC30) = raw3475 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3475; decide +kernel
    rw [ha]
    exact (canonical3475 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA30 + difference 5 0) (sourceB30 + difference 0 5) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4282) := by
    have ha : (tripleCharges (sourceA30 + difference 5 0) (sourceB30 + difference 0 5) sourceC30) = raw3476 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3476; decide +kernel
    rw [ha]
    exact (canonical3476 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA30 + difference 5 1) (sourceB30 + difference 1 5) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4281) := by
    have ha : (tripleCharges (sourceA30 + difference 5 1) (sourceB30 + difference 1 5) sourceC30) = raw3477 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3477; decide +kernel
    rw [ha]
    exact (canonical3477 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA30 + difference 5 2) (sourceB30 + difference 2 5) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4281) := by
    have ha : (tripleCharges (sourceA30 + difference 5 2) (sourceB30 + difference 2 5) sourceC30) = raw3478 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3478; decide +kernel
    rw [ha]
    exact (canonical3478 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA30 + difference 5 3) (sourceB30 + difference 3 5) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4281) := by
    have ha : (tripleCharges (sourceA30 + difference 5 3) (sourceB30 + difference 3 5) sourceC30) = raw3479 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3479; decide +kernel
    rw [ha]
    exact (canonical3479 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA30 + difference 5 4) (sourceB30 + difference 4 5) sourceC30) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4282) := by
    have ha : (tripleCharges (sourceA30 + difference 5 4) (sourceB30 + difference 4 5) sourceC30) = raw3480 := by
      apply Matrix.ext; unfold tripleCharges sourceA30 sourceB30 sourceC30 difference raw3480; decide +kernel
    rw [ha]
    exact (canonical3480 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA30 sourceB30 sourceC30
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm30, Integer.Sparse.eval]
  linarith only [hs]

def sourceA31 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB31 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC31 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm31 : Integer.Sparse Master := [(Sum.inr 837, 3), (Sum.inr 839, 1), (Sum.inr 861, 1), (Sum.inr 1352, 3), (Sum.inr 1438, 1), (Sum.inr 1719, 3), (Sum.inr 1747, 1), (Sum.inr 1933, 6), (Sum.inr 2136, 3), (Sum.inr 2222, 3), (Sum.inr 2255, 3), (Sum.inr 2281, 1), (Sum.inr 2778, 1)]

theorem sourceEq31 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm31 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA31 + difference 0 1) (sourceB31 + difference 1 0) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA31 + difference 0 1) (sourceB31 + difference 1 0) sourceC31) = raw3481 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3481; decide +kernel
    rw [ha]
    exact (canonical3481 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA31 + difference 0 2) (sourceB31 + difference 2 0) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA31 + difference 0 2) (sourceB31 + difference 2 0) sourceC31) = raw3482 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3482; decide +kernel
    rw [ha]
    exact (canonical3482 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA31 + difference 0 3) (sourceB31 + difference 3 0) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA31 + difference 0 3) (sourceB31 + difference 3 0) sourceC31) = raw3483 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3483; decide +kernel
    rw [ha]
    exact (canonical3483 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA31 + difference 0 4) (sourceB31 + difference 4 0) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1747) := by
    have ha : (tripleCharges (sourceA31 + difference 0 4) (sourceB31 + difference 4 0) sourceC31) = raw3484 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3484; decide +kernel
    rw [ha]
    exact (canonical3484 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA31 + difference 0 5) (sourceB31 + difference 5 0) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA31 + difference 0 5) (sourceB31 + difference 5 0) sourceC31) = raw3485 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3485; decide +kernel
    rw [ha]
    exact (canonical3485 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA31 + difference 1 0) (sourceB31 + difference 0 1) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1352) := by
    have ha : (tripleCharges (sourceA31 + difference 1 0) (sourceB31 + difference 0 1) sourceC31) = raw3486 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3486; decide +kernel
    rw [ha]
    exact (canonical3486 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA31 + difference 1 2) (sourceB31 + difference 2 1) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1933) := by
    have ha : (tripleCharges (sourceA31 + difference 1 2) (sourceB31 + difference 2 1) sourceC31) = raw3487 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3487; decide +kernel
    rw [ha]
    exact (canonical3487 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA31 + difference 1 3) (sourceB31 + difference 3 1) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1933) := by
    have ha : (tripleCharges (sourceA31 + difference 1 3) (sourceB31 + difference 3 1) sourceC31) = raw3488 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3488; decide +kernel
    rw [ha]
    exact (canonical3488 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA31 + difference 1 4) (sourceB31 + difference 4 1) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1719) := by
    have ha : (tripleCharges (sourceA31 + difference 1 4) (sourceB31 + difference 4 1) sourceC31) = raw3489 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3489; decide +kernel
    rw [ha]
    exact (canonical3489 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA31 + difference 1 5) (sourceB31 + difference 5 1) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA31 + difference 1 5) (sourceB31 + difference 5 1) sourceC31) = raw3490 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3490; decide +kernel
    rw [ha]
    exact (canonical3490 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA31 + difference 2 0) (sourceB31 + difference 0 2) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1352) := by
    have ha : (tripleCharges (sourceA31 + difference 2 0) (sourceB31 + difference 0 2) sourceC31) = raw3491 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3491; decide +kernel
    rw [ha]
    exact (canonical3491 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA31 + difference 2 1) (sourceB31 + difference 1 2) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1933) := by
    have ha : (tripleCharges (sourceA31 + difference 2 1) (sourceB31 + difference 1 2) sourceC31) = raw3492 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3492; decide +kernel
    rw [ha]
    exact (canonical3492 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA31 + difference 2 3) (sourceB31 + difference 3 2) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1933) := by
    have ha : (tripleCharges (sourceA31 + difference 2 3) (sourceB31 + difference 3 2) sourceC31) = raw3493 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3493; decide +kernel
    rw [ha]
    exact (canonical3493 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA31 + difference 2 4) (sourceB31 + difference 4 2) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1719) := by
    have ha : (tripleCharges (sourceA31 + difference 2 4) (sourceB31 + difference 4 2) sourceC31) = raw3494 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3494; decide +kernel
    rw [ha]
    exact (canonical3494 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA31 + difference 2 5) (sourceB31 + difference 5 2) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA31 + difference 2 5) (sourceB31 + difference 5 2) sourceC31) = raw3495 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3495; decide +kernel
    rw [ha]
    exact (canonical3495 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA31 + difference 3 0) (sourceB31 + difference 0 3) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1352) := by
    have ha : (tripleCharges (sourceA31 + difference 3 0) (sourceB31 + difference 0 3) sourceC31) = raw3496 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3496; decide +kernel
    rw [ha]
    exact (canonical3496 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA31 + difference 3 1) (sourceB31 + difference 1 3) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1933) := by
    have ha : (tripleCharges (sourceA31 + difference 3 1) (sourceB31 + difference 1 3) sourceC31) = raw3497 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3497; decide +kernel
    rw [ha]
    exact (canonical3497 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA31 + difference 3 2) (sourceB31 + difference 2 3) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1933) := by
    have ha : (tripleCharges (sourceA31 + difference 3 2) (sourceB31 + difference 2 3) sourceC31) = raw3498 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3498; decide +kernel
    rw [ha]
    exact (canonical3498 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA31 + difference 3 4) (sourceB31 + difference 4 3) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1719) := by
    have ha : (tripleCharges (sourceA31 + difference 3 4) (sourceB31 + difference 4 3) sourceC31) = raw3499 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3499; decide +kernel
    rw [ha]
    exact (canonical3499 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA31 + difference 3 5) (sourceB31 + difference 5 3) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA31 + difference 3 5) (sourceB31 + difference 5 3) sourceC31) = raw3500 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3500; decide +kernel
    rw [ha]
    exact (canonical3500 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA31 + difference 4 0) (sourceB31 + difference 0 4) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1438) := by
    have ha : (tripleCharges (sourceA31 + difference 4 0) (sourceB31 + difference 0 4) sourceC31) = raw3501 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3501; decide +kernel
    rw [ha]
    exact (canonical3501 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA31 + difference 4 1) (sourceB31 + difference 1 4) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA31 + difference 4 1) (sourceB31 + difference 1 4) sourceC31) = raw3502 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3502; decide +kernel
    rw [ha]
    exact (canonical3502 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA31 + difference 4 2) (sourceB31 + difference 2 4) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA31 + difference 4 2) (sourceB31 + difference 2 4) sourceC31) = raw3503 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3503; decide +kernel
    rw [ha]
    exact (canonical3503 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA31 + difference 4 3) (sourceB31 + difference 3 4) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA31 + difference 4 3) (sourceB31 + difference 3 4) sourceC31) = raw3504 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3504; decide +kernel
    rw [ha]
    exact (canonical3504 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA31 + difference 4 5) (sourceB31 + difference 5 4) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2778) := by
    have ha : (tripleCharges (sourceA31 + difference 4 5) (sourceB31 + difference 5 4) sourceC31) = raw3505 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3505; decide +kernel
    rw [ha]
    exact (canonical3505 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA31 + difference 5 0) (sourceB31 + difference 0 5) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 839) := by
    have ha : (tripleCharges (sourceA31 + difference 5 0) (sourceB31 + difference 0 5) sourceC31) = raw3506 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3506; decide +kernel
    rw [ha]
    exact (canonical3506 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA31 + difference 5 1) (sourceB31 + difference 1 5) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 837) := by
    have ha : (tripleCharges (sourceA31 + difference 5 1) (sourceB31 + difference 1 5) sourceC31) = raw3507 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3507; decide +kernel
    rw [ha]
    exact (canonical3507 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA31 + difference 5 2) (sourceB31 + difference 2 5) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 837) := by
    have ha : (tripleCharges (sourceA31 + difference 5 2) (sourceB31 + difference 2 5) sourceC31) = raw3508 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3508; decide +kernel
    rw [ha]
    exact (canonical3508 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA31 + difference 5 3) (sourceB31 + difference 3 5) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 837) := by
    have ha : (tripleCharges (sourceA31 + difference 5 3) (sourceB31 + difference 3 5) sourceC31) = raw3509 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3509; decide +kernel
    rw [ha]
    exact (canonical3509 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA31 + difference 5 4) (sourceB31 + difference 4 5) sourceC31) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 861) := by
    have ha : (tripleCharges (sourceA31 + difference 5 4) (sourceB31 + difference 4 5) sourceC31) = raw3510 := by
      apply Matrix.ext; unfold tripleCharges sourceA31 sourceB31 sourceC31 difference raw3510; decide +kernel
    rw [ha]
    exact (canonical3510 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA31 sourceB31 sourceC31
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm31, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
