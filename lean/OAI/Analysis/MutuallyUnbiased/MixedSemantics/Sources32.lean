import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical115
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical117
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical118
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical122
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical123
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical124
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical129
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical130
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical131
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical132
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical133
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical134
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical135

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1024 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceB1024 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceC1024 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1024 : Integer.Sparse Master := [(Sum.inr 3023, 1), (Sum.inr 3024, 1), (Sum.inr 3025, 1), (Sum.inr 3051, 1), (Sum.inr 3097, 1), (Sum.inr 3461, 1), (Sum.inr 3464, 1), (Sum.inr 3471, 1), (Sum.inr 3472, 1), (Sum.inr 3480, 2), (Sum.inr 3535, 1), (Sum.inr 3626, 1), (Sum.inr 3759, 1), (Sum.inr 3762, 1), (Sum.inr 3767, 1), (Sum.inr 3772, 1), (Sum.inr 3794, 1), (Sum.inr 3801, 1), (Sum.inr 3808, 1), (Sum.inr 3809, 1), (Sum.inr 3814, 1), (Sum.inr 3817, 1), (Sum.inr 3839, 1), (Sum.inr 3853, 1), (Sum.inr 3862, 1), (Sum.inr 3959, 1), (Sum.inr 3972, 1), (Sum.inr 3982, 1), (Sum.inr 3987, 1)]

theorem sourceEq1024 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1024 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1024 + difference 0 1) (sourceB1024 + difference 1 0) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA1024 + difference 0 1) (sourceB1024 + difference 1 0) sourceC1024) = raw15144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw15144; decide +kernel
    rw [ha]
    exact (canonical15144 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1024 + difference 0 2) (sourceB1024 + difference 2 0) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA1024 + difference 0 2) (sourceB1024 + difference 2 0) sourceC1024) = raw16189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw16189; decide +kernel
    rw [ha]
    exact (canonical16189 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1024 + difference 0 3) (sourceB1024 + difference 3 0) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA1024 + difference 0 3) (sourceB1024 + difference 3 0) sourceC1024) = raw16727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw16727; decide +kernel
    rw [ha]
    exact (canonical16727 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1024 + difference 0 4) (sourceB1024 + difference 4 0) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA1024 + difference 0 4) (sourceB1024 + difference 4 0) sourceC1024) = raw16585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw16585; decide +kernel
    rw [ha]
    exact (canonical16585 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1024 + difference 0 5) (sourceB1024 + difference 5 0) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA1024 + difference 0 5) (sourceB1024 + difference 5 0) sourceC1024) = raw16728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw16728; decide +kernel
    rw [ha]
    exact (canonical16728 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1024 + difference 1 0) (sourceB1024 + difference 0 1) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA1024 + difference 1 0) (sourceB1024 + difference 0 1) sourceC1024) = raw16729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw16729; decide +kernel
    rw [ha]
    exact (canonical16729 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1024 + difference 1 2) (sourceB1024 + difference 2 1) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA1024 + difference 1 2) (sourceB1024 + difference 2 1) sourceC1024) = raw16194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw16194; decide +kernel
    rw [ha]
    exact (canonical16194 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1024 + difference 1 3) (sourceB1024 + difference 3 1) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA1024 + difference 1 3) (sourceB1024 + difference 3 1) sourceC1024) = raw16730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw16730; decide +kernel
    rw [ha]
    exact (canonical16730 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1024 + difference 1 4) (sourceB1024 + difference 4 1) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA1024 + difference 1 4) (sourceB1024 + difference 4 1) sourceC1024) = raw16589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw16589; decide +kernel
    rw [ha]
    exact (canonical16589 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1024 + difference 1 5) (sourceB1024 + difference 5 1) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA1024 + difference 1 5) (sourceB1024 + difference 5 1) sourceC1024) = raw16731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw16731; decide +kernel
    rw [ha]
    exact (canonical16731 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1024 + difference 2 0) (sourceB1024 + difference 0 2) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA1024 + difference 2 0) (sourceB1024 + difference 0 2) sourceC1024) = raw15895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw15895; decide +kernel
    rw [ha]
    exact (canonical15895 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1024 + difference 2 1) (sourceB1024 + difference 1 2) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA1024 + difference 2 1) (sourceB1024 + difference 1 2) sourceC1024) = raw15154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw15154; decide +kernel
    rw [ha]
    exact (canonical15154 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1024 + difference 2 3) (sourceB1024 + difference 3 2) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA1024 + difference 2 3) (sourceB1024 + difference 3 2) sourceC1024) = raw15896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw15896; decide +kernel
    rw [ha]
    exact (canonical15896 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1024 + difference 2 4) (sourceB1024 + difference 4 2) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3759) := by
    have ha : (tripleCharges (sourceA1024 + difference 2 4) (sourceB1024 + difference 4 2) sourceC1024) = raw15722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw15722; decide +kernel
    rw [ha]
    exact (canonical15722 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1024 + difference 2 5) (sourceB1024 + difference 5 2) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA1024 + difference 2 5) (sourceB1024 + difference 5 2) sourceC1024) = raw15897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw15897; decide +kernel
    rw [ha]
    exact (canonical15897 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1024 + difference 3 0) (sourceB1024 + difference 0 3) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA1024 + difference 3 0) (sourceB1024 + difference 0 3) sourceC1024) = raw16732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw16732; decide +kernel
    rw [ha]
    exact (canonical16732 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1024 + difference 3 1) (sourceB1024 + difference 1 3) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA1024 + difference 3 1) (sourceB1024 + difference 1 3) sourceC1024) = raw15159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw15159; decide +kernel
    rw [ha]
    exact (canonical15159 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1024 + difference 3 2) (sourceB1024 + difference 2 3) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA1024 + difference 3 2) (sourceB1024 + difference 2 3) sourceC1024) = raw16198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw16198; decide +kernel
    rw [ha]
    exact (canonical16198 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1024 + difference 3 4) (sourceB1024 + difference 4 3) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3772) := by
    have ha : (tripleCharges (sourceA1024 + difference 3 4) (sourceB1024 + difference 4 3) sourceC1024) = raw16592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw16592; decide +kernel
    rw [ha]
    exact (canonical16592 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1024 + difference 3 5) (sourceB1024 + difference 5 3) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA1024 + difference 3 5) (sourceB1024 + difference 5 3) sourceC1024) = raw16733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw16733; decide +kernel
    rw [ha]
    exact (canonical16733 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1024 + difference 4 0) (sourceB1024 + difference 0 4) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA1024 + difference 4 0) (sourceB1024 + difference 0 4) sourceC1024) = raw16734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw16734; decide +kernel
    rw [ha]
    exact (canonical16734 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1024 + difference 4 1) (sourceB1024 + difference 1 4) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA1024 + difference 4 1) (sourceB1024 + difference 1 4) sourceC1024) = raw14774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw14774; decide +kernel
    rw [ha]
    exact (canonical14774 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1024 + difference 4 2) (sourceB1024 + difference 2 4) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA1024 + difference 4 2) (sourceB1024 + difference 2 4) sourceC1024) = raw14769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw14769; decide +kernel
    rw [ha]
    exact (canonical14769 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1024 + difference 4 3) (sourceB1024 + difference 3 4) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA1024 + difference 4 3) (sourceB1024 + difference 3 4) sourceC1024) = raw15001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw15001; decide +kernel
    rw [ha]
    exact (canonical15001 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1024 + difference 4 5) (sourceB1024 + difference 5 4) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA1024 + difference 4 5) (sourceB1024 + difference 5 4) sourceC1024) = raw16735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw16735; decide +kernel
    rw [ha]
    exact (canonical16735 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1024 + difference 5 0) (sourceB1024 + difference 0 5) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA1024 + difference 5 0) (sourceB1024 + difference 0 5) sourceC1024) = raw15145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw15145; decide +kernel
    rw [ha]
    exact (canonical15145 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1024 + difference 5 1) (sourceB1024 + difference 1 5) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA1024 + difference 5 1) (sourceB1024 + difference 1 5) sourceC1024) = raw15732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw15732; decide +kernel
    rw [ha]
    exact (canonical15732 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1024 + difference 5 2) (sourceB1024 + difference 2 5) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA1024 + difference 5 2) (sourceB1024 + difference 2 5) sourceC1024) = raw15146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw15146; decide +kernel
    rw [ha]
    exact (canonical15146 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1024 + difference 5 3) (sourceB1024 + difference 3 5) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA1024 + difference 5 3) (sourceB1024 + difference 3 5) sourceC1024) = raw15147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw15147; decide +kernel
    rw [ha]
    exact (canonical15147 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1024 + difference 5 4) (sourceB1024 + difference 4 5) sourceC1024) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1024 + difference 5 4) (sourceB1024 + difference 4 5) sourceC1024) = raw15148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1024 sourceB1024 sourceC1024 difference raw15148; decide +kernel
    rw [ha]
    exact (canonical15148 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1024 sourceB1024 sourceC1024
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1024, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1025 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1025 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1025 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceForm1025 : Integer.Sparse Master := [(Sum.inr 5064, 1), (Sum.inr 5067, 1), (Sum.inr 5071, 2), (Sum.inr 5181, 1), (Sum.inr 5185, 2), (Sum.inr 5244, 1), (Sum.inr 5282, 1), (Sum.inr 5348, 1), (Sum.inr 5350, 2), (Sum.inr 5352, 2), (Sum.inr 5405, 1), (Sum.inr 5421, 2), (Sum.inr 5429, 1), (Sum.inr 5431, 1), (Sum.inr 5448, 1), (Sum.inr 5470, 2), (Sum.inr 5472, 2), (Sum.inr 5473, 2), (Sum.inr 5480, 2), (Sum.inr 5482, 1), (Sum.inr 5485, 1)]

theorem sourceEq1025 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1025 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1025 + difference 0 1) (sourceB1025 + difference 1 0) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1025 + difference 0 1) (sourceB1025 + difference 1 0) sourceC1025) = raw16736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16736; decide +kernel
    rw [ha]
    exact (canonical16736 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1025 + difference 0 2) (sourceB1025 + difference 2 0) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1025 + difference 0 2) (sourceB1025 + difference 2 0) sourceC1025) = raw16737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16737; decide +kernel
    rw [ha]
    exact (canonical16737 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1025 + difference 0 3) (sourceB1025 + difference 3 0) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1025 + difference 0 3) (sourceB1025 + difference 3 0) sourceC1025) = raw16738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16738; decide +kernel
    rw [ha]
    exact (canonical16738 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1025 + difference 0 4) (sourceB1025 + difference 4 0) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1025 + difference 0 4) (sourceB1025 + difference 4 0) sourceC1025) = raw16739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16739; decide +kernel
    rw [ha]
    exact (canonical16739 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1025 + difference 0 5) (sourceB1025 + difference 5 0) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1025 + difference 0 5) (sourceB1025 + difference 5 0) sourceC1025) = raw16740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16740; decide +kernel
    rw [ha]
    exact (canonical16740 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1025 + difference 1 0) (sourceB1025 + difference 0 1) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5244) := by
    have ha : (tripleCharges (sourceA1025 + difference 1 0) (sourceB1025 + difference 0 1) sourceC1025) = raw16741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16741; decide +kernel
    rw [ha]
    exact (canonical16741 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1025 + difference 1 2) (sourceB1025 + difference 2 1) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1025 + difference 1 2) (sourceB1025 + difference 2 1) sourceC1025) = raw16742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16742; decide +kernel
    rw [ha]
    exact (canonical16742 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1025 + difference 1 3) (sourceB1025 + difference 3 1) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1025 + difference 1 3) (sourceB1025 + difference 3 1) sourceC1025) = raw16743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16743; decide +kernel
    rw [ha]
    exact (canonical16743 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1025 + difference 1 4) (sourceB1025 + difference 4 1) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1025 + difference 1 4) (sourceB1025 + difference 4 1) sourceC1025) = raw16744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16744; decide +kernel
    rw [ha]
    exact (canonical16744 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1025 + difference 1 5) (sourceB1025 + difference 5 1) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1025 + difference 1 5) (sourceB1025 + difference 5 1) sourceC1025) = raw16745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16745; decide +kernel
    rw [ha]
    exact (canonical16745 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1025 + difference 2 0) (sourceB1025 + difference 0 2) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA1025 + difference 2 0) (sourceB1025 + difference 0 2) sourceC1025) = raw16746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16746; decide +kernel
    rw [ha]
    exact (canonical16746 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1025 + difference 2 1) (sourceB1025 + difference 1 2) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1025 + difference 2 1) (sourceB1025 + difference 1 2) sourceC1025) = raw16747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16747; decide +kernel
    rw [ha]
    exact (canonical16747 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1025 + difference 2 3) (sourceB1025 + difference 3 2) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA1025 + difference 2 3) (sourceB1025 + difference 3 2) sourceC1025) = raw16748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16748; decide +kernel
    rw [ha]
    exact (canonical16748 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1025 + difference 2 4) (sourceB1025 + difference 4 2) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1025 + difference 2 4) (sourceB1025 + difference 4 2) sourceC1025) = raw16749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16749; decide +kernel
    rw [ha]
    exact (canonical16749 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1025 + difference 2 5) (sourceB1025 + difference 5 2) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1025 + difference 2 5) (sourceB1025 + difference 5 2) sourceC1025) = raw16750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16750; decide +kernel
    rw [ha]
    exact (canonical16750 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1025 + difference 3 0) (sourceB1025 + difference 0 3) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA1025 + difference 3 0) (sourceB1025 + difference 0 3) sourceC1025) = raw16751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16751; decide +kernel
    rw [ha]
    exact (canonical16751 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1025 + difference 3 1) (sourceB1025 + difference 1 3) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1025 + difference 3 1) (sourceB1025 + difference 1 3) sourceC1025) = raw16752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16752; decide +kernel
    rw [ha]
    exact (canonical16752 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1025 + difference 3 2) (sourceB1025 + difference 2 3) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA1025 + difference 3 2) (sourceB1025 + difference 2 3) sourceC1025) = raw16753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16753; decide +kernel
    rw [ha]
    exact (canonical16753 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1025 + difference 3 4) (sourceB1025 + difference 4 3) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1025 + difference 3 4) (sourceB1025 + difference 4 3) sourceC1025) = raw16754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16754; decide +kernel
    rw [ha]
    exact (canonical16754 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1025 + difference 3 5) (sourceB1025 + difference 5 3) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1025 + difference 3 5) (sourceB1025 + difference 5 3) sourceC1025) = raw16755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16755; decide +kernel
    rw [ha]
    exact (canonical16755 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1025 + difference 4 0) (sourceB1025 + difference 0 4) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5181) := by
    have ha : (tripleCharges (sourceA1025 + difference 4 0) (sourceB1025 + difference 0 4) sourceC1025) = raw16756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16756; decide +kernel
    rw [ha]
    exact (canonical16756 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1025 + difference 4 1) (sourceB1025 + difference 1 4) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5348) := by
    have ha : (tripleCharges (sourceA1025 + difference 4 1) (sourceB1025 + difference 1 4) sourceC1025) = raw16757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16757; decide +kernel
    rw [ha]
    exact (canonical16757 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1025 + difference 4 2) (sourceB1025 + difference 2 4) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5350) := by
    have ha : (tripleCharges (sourceA1025 + difference 4 2) (sourceB1025 + difference 2 4) sourceC1025) = raw16758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16758; decide +kernel
    rw [ha]
    exact (canonical16758 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1025 + difference 4 3) (sourceB1025 + difference 3 4) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5350) := by
    have ha : (tripleCharges (sourceA1025 + difference 4 3) (sourceB1025 + difference 3 4) sourceC1025) = raw16759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16759; decide +kernel
    rw [ha]
    exact (canonical16759 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1025 + difference 4 5) (sourceB1025 + difference 5 4) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1025 + difference 4 5) (sourceB1025 + difference 5 4) sourceC1025) = raw16760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16760; decide +kernel
    rw [ha]
    exact (canonical16760 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1025 + difference 5 0) (sourceB1025 + difference 0 5) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5064) := by
    have ha : (tripleCharges (sourceA1025 + difference 5 0) (sourceB1025 + difference 0 5) sourceC1025) = raw16761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16761; decide +kernel
    rw [ha]
    exact (canonical16761 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1025 + difference 5 1) (sourceB1025 + difference 1 5) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA1025 + difference 5 1) (sourceB1025 + difference 1 5) sourceC1025) = raw16762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16762; decide +kernel
    rw [ha]
    exact (canonical16762 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1025 + difference 5 2) (sourceB1025 + difference 2 5) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5071) := by
    have ha : (tripleCharges (sourceA1025 + difference 5 2) (sourceB1025 + difference 2 5) sourceC1025) = raw16763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16763; decide +kernel
    rw [ha]
    exact (canonical16763 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1025 + difference 5 3) (sourceB1025 + difference 3 5) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5071) := by
    have ha : (tripleCharges (sourceA1025 + difference 5 3) (sourceB1025 + difference 3 5) sourceC1025) = raw16764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16764; decide +kernel
    rw [ha]
    exact (canonical16764 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1025 + difference 5 4) (sourceB1025 + difference 4 5) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA1025 + difference 5 4) (sourceB1025 + difference 4 5) sourceC1025) = raw16765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16765; decide +kernel
    rw [ha]
    exact (canonical16765 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1025 sourceB1025 sourceC1025
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1025, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1026 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1026 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1026 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceForm1026 : Integer.Sparse Master := [(Sum.inr 2469, 1), (Sum.inr 2473, 1), (Sum.inr 2478, 2), (Sum.inr 2609, 1), (Sum.inr 2615, 2), (Sum.inr 2698, 1), (Sum.inr 2751, 1), (Sum.inr 3685, 1), (Sum.inr 3688, 2), (Sum.inr 3846, 1), (Sum.inr 3873, 2), (Sum.inr 3875, 1), (Sum.inr 3885, 1), (Sum.inr 3936, 2), (Sum.inr 3947, 2), (Sum.inr 3977, 1), (Sum.inr 3978, 2), (Sum.inr 3992, 1), (Sum.inr 3995, 2), (Sum.inr 3998, 1), (Sum.inr 4002, 2)]

theorem sourceEq1026 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1026 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1026 + difference 0 1) (sourceB1026 + difference 1 0) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA1026 + difference 0 1) (sourceB1026 + difference 1 0) sourceC1026) = raw16766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16766; decide +kernel
    rw [ha]
    exact (canonical16766 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1026 + difference 0 2) (sourceB1026 + difference 2 0) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1026 + difference 0 2) (sourceB1026 + difference 2 0) sourceC1026) = raw16767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16767; decide +kernel
    rw [ha]
    exact (canonical16767 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1026 + difference 0 3) (sourceB1026 + difference 3 0) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1026 + difference 0 3) (sourceB1026 + difference 3 0) sourceC1026) = raw16768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16768; decide +kernel
    rw [ha]
    exact (canonical16768 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1026 + difference 0 4) (sourceB1026 + difference 4 0) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA1026 + difference 0 4) (sourceB1026 + difference 4 0) sourceC1026) = raw16769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16769; decide +kernel
    rw [ha]
    exact (canonical16769 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1026 + difference 0 5) (sourceB1026 + difference 5 0) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3992) := by
    have ha : (tripleCharges (sourceA1026 + difference 0 5) (sourceB1026 + difference 5 0) sourceC1026) = raw16770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16770; decide +kernel
    rw [ha]
    exact (canonical16770 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1026 + difference 1 0) (sourceB1026 + difference 0 1) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2698) := by
    have ha : (tripleCharges (sourceA1026 + difference 1 0) (sourceB1026 + difference 0 1) sourceC1026) = raw16771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16771; decide +kernel
    rw [ha]
    exact (canonical16771 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1026 + difference 1 2) (sourceB1026 + difference 2 1) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA1026 + difference 1 2) (sourceB1026 + difference 2 1) sourceC1026) = raw16772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16772; decide +kernel
    rw [ha]
    exact (canonical16772 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1026 + difference 1 3) (sourceB1026 + difference 3 1) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA1026 + difference 1 3) (sourceB1026 + difference 3 1) sourceC1026) = raw16773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16773; decide +kernel
    rw [ha]
    exact (canonical16773 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1026 + difference 1 4) (sourceB1026 + difference 4 1) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA1026 + difference 1 4) (sourceB1026 + difference 4 1) sourceC1026) = raw16774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16774; decide +kernel
    rw [ha]
    exact (canonical16774 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1026 + difference 1 5) (sourceB1026 + difference 5 1) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA1026 + difference 1 5) (sourceB1026 + difference 5 1) sourceC1026) = raw16775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16775; decide +kernel
    rw [ha]
    exact (canonical16775 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1026 + difference 2 0) (sourceB1026 + difference 0 2) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA1026 + difference 2 0) (sourceB1026 + difference 0 2) sourceC1026) = raw16776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16776; decide +kernel
    rw [ha]
    exact (canonical16776 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1026 + difference 2 1) (sourceB1026 + difference 1 2) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3936) := by
    have ha : (tripleCharges (sourceA1026 + difference 2 1) (sourceB1026 + difference 1 2) sourceC1026) = raw16777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16777; decide +kernel
    rw [ha]
    exact (canonical16777 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1026 + difference 2 3) (sourceB1026 + difference 3 2) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3947) := by
    have ha : (tripleCharges (sourceA1026 + difference 2 3) (sourceB1026 + difference 3 2) sourceC1026) = raw16778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16778; decide +kernel
    rw [ha]
    exact (canonical16778 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1026 + difference 2 4) (sourceB1026 + difference 4 2) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA1026 + difference 2 4) (sourceB1026 + difference 4 2) sourceC1026) = raw16779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16779; decide +kernel
    rw [ha]
    exact (canonical16779 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1026 + difference 2 5) (sourceB1026 + difference 5 2) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4002) := by
    have ha : (tripleCharges (sourceA1026 + difference 2 5) (sourceB1026 + difference 5 2) sourceC1026) = raw16780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16780; decide +kernel
    rw [ha]
    exact (canonical16780 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1026 + difference 3 0) (sourceB1026 + difference 0 3) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA1026 + difference 3 0) (sourceB1026 + difference 0 3) sourceC1026) = raw16781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16781; decide +kernel
    rw [ha]
    exact (canonical16781 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1026 + difference 3 1) (sourceB1026 + difference 1 3) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3936) := by
    have ha : (tripleCharges (sourceA1026 + difference 3 1) (sourceB1026 + difference 1 3) sourceC1026) = raw16782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16782; decide +kernel
    rw [ha]
    exact (canonical16782 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1026 + difference 3 2) (sourceB1026 + difference 2 3) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3947) := by
    have ha : (tripleCharges (sourceA1026 + difference 3 2) (sourceB1026 + difference 2 3) sourceC1026) = raw16783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16783; decide +kernel
    rw [ha]
    exact (canonical16783 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1026 + difference 3 4) (sourceB1026 + difference 4 3) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA1026 + difference 3 4) (sourceB1026 + difference 4 3) sourceC1026) = raw16784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16784; decide +kernel
    rw [ha]
    exact (canonical16784 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1026 + difference 3 5) (sourceB1026 + difference 5 3) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4002) := by
    have ha : (tripleCharges (sourceA1026 + difference 3 5) (sourceB1026 + difference 5 3) sourceC1026) = raw16785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16785; decide +kernel
    rw [ha]
    exact (canonical16785 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1026 + difference 4 0) (sourceB1026 + difference 0 4) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2609) := by
    have ha : (tripleCharges (sourceA1026 + difference 4 0) (sourceB1026 + difference 0 4) sourceC1026) = raw16786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16786; decide +kernel
    rw [ha]
    exact (canonical16786 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1026 + difference 4 1) (sourceB1026 + difference 1 4) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3685) := by
    have ha : (tripleCharges (sourceA1026 + difference 4 1) (sourceB1026 + difference 1 4) sourceC1026) = raw16787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16787; decide +kernel
    rw [ha]
    exact (canonical16787 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1026 + difference 4 2) (sourceB1026 + difference 2 4) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3688) := by
    have ha : (tripleCharges (sourceA1026 + difference 4 2) (sourceB1026 + difference 2 4) sourceC1026) = raw16788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16788; decide +kernel
    rw [ha]
    exact (canonical16788 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1026 + difference 4 3) (sourceB1026 + difference 3 4) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3688) := by
    have ha : (tripleCharges (sourceA1026 + difference 4 3) (sourceB1026 + difference 3 4) sourceC1026) = raw16789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16789; decide +kernel
    rw [ha]
    exact (canonical16789 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1026 + difference 4 5) (sourceB1026 + difference 5 4) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA1026 + difference 4 5) (sourceB1026 + difference 5 4) sourceC1026) = raw16790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16790; decide +kernel
    rw [ha]
    exact (canonical16790 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1026 + difference 5 0) (sourceB1026 + difference 0 5) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2469) := by
    have ha : (tripleCharges (sourceA1026 + difference 5 0) (sourceB1026 + difference 0 5) sourceC1026) = raw16791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16791; decide +kernel
    rw [ha]
    exact (canonical16791 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1026 + difference 5 1) (sourceB1026 + difference 1 5) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2473) := by
    have ha : (tripleCharges (sourceA1026 + difference 5 1) (sourceB1026 + difference 1 5) sourceC1026) = raw16792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16792; decide +kernel
    rw [ha]
    exact (canonical16792 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1026 + difference 5 2) (sourceB1026 + difference 2 5) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2478) := by
    have ha : (tripleCharges (sourceA1026 + difference 5 2) (sourceB1026 + difference 2 5) sourceC1026) = raw16793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16793; decide +kernel
    rw [ha]
    exact (canonical16793 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1026 + difference 5 3) (sourceB1026 + difference 3 5) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2478) := by
    have ha : (tripleCharges (sourceA1026 + difference 5 3) (sourceB1026 + difference 3 5) sourceC1026) = raw16794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16794; decide +kernel
    rw [ha]
    exact (canonical16794 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1026 + difference 5 4) (sourceB1026 + difference 4 5) sourceC1026) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA1026 + difference 5 4) (sourceB1026 + difference 4 5) sourceC1026) = raw16795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1026 sourceB1026 sourceC1026 difference raw16795; decide +kernel
    rw [ha]
    exact (canonical16795 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1026 sourceB1026 sourceC1026
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1026, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1027 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1027 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1027 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceForm1027 : Integer.Sparse Master := [(Sum.inr 3443, 1), (Sum.inr 3445, 2), (Sum.inr 3476, 1), (Sum.inr 3491, 1), (Sum.inr 3497, 1), (Sum.inr 3529, 2), (Sum.inr 3580, 1), (Sum.inr 3750, 2), (Sum.inr 3764, 2), (Sum.inr 3768, 1), (Sum.inr 3805, 1), (Sum.inr 3874, 1), (Sum.inr 3946, 2), (Sum.inr 3955, 2), (Sum.inr 3957, 2), (Sum.inr 3961, 2), (Sum.inr 3978, 2), (Sum.inr 3980, 1), (Sum.inr 3984, 1), (Sum.inr 4026, 1), (Sum.inr 4028, 1)]

theorem sourceEq1027 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1027 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1027 + difference 0 1) (sourceB1027 + difference 1 0) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA1027 + difference 0 1) (sourceB1027 + difference 1 0) sourceC1027) = raw16796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16796; decide +kernel
    rw [ha]
    exact (canonical16796 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1027 + difference 0 2) (sourceB1027 + difference 2 0) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1027 + difference 0 2) (sourceB1027 + difference 2 0) sourceC1027) = raw16797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16797; decide +kernel
    rw [ha]
    exact (canonical16797 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1027 + difference 0 3) (sourceB1027 + difference 3 0) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1027 + difference 0 3) (sourceB1027 + difference 3 0) sourceC1027) = raw16798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16798; decide +kernel
    rw [ha]
    exact (canonical16798 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1027 + difference 0 4) (sourceB1027 + difference 4 0) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA1027 + difference 0 4) (sourceB1027 + difference 4 0) sourceC1027) = raw16799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16799; decide +kernel
    rw [ha]
    exact (canonical16799 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1027 + difference 0 5) (sourceB1027 + difference 5 0) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA1027 + difference 0 5) (sourceB1027 + difference 5 0) sourceC1027) = raw16800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16800; decide +kernel
    rw [ha]
    exact (canonical16800 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1027 + difference 1 0) (sourceB1027 + difference 0 1) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3497) := by
    have ha : (tripleCharges (sourceA1027 + difference 1 0) (sourceB1027 + difference 0 1) sourceC1027) = raw16801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16801; decide +kernel
    rw [ha]
    exact (canonical16801 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1027 + difference 1 2) (sourceB1027 + difference 2 1) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA1027 + difference 1 2) (sourceB1027 + difference 2 1) sourceC1027) = raw16802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16802; decide +kernel
    rw [ha]
    exact (canonical16802 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1027 + difference 1 3) (sourceB1027 + difference 3 1) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA1027 + difference 1 3) (sourceB1027 + difference 3 1) sourceC1027) = raw16803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16803; decide +kernel
    rw [ha]
    exact (canonical16803 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1027 + difference 1 4) (sourceB1027 + difference 4 1) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4028) := by
    have ha : (tripleCharges (sourceA1027 + difference 1 4) (sourceB1027 + difference 4 1) sourceC1027) = raw16804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16804; decide +kernel
    rw [ha]
    exact (canonical16804 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1027 + difference 1 5) (sourceB1027 + difference 5 1) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA1027 + difference 1 5) (sourceB1027 + difference 5 1) sourceC1027) = raw16805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16805; decide +kernel
    rw [ha]
    exact (canonical16805 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1027 + difference 2 0) (sourceB1027 + difference 0 2) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA1027 + difference 2 0) (sourceB1027 + difference 0 2) sourceC1027) = raw16806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16806; decide +kernel
    rw [ha]
    exact (canonical16806 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1027 + difference 2 1) (sourceB1027 + difference 1 2) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA1027 + difference 2 1) (sourceB1027 + difference 1 2) sourceC1027) = raw16807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16807; decide +kernel
    rw [ha]
    exact (canonical16807 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1027 + difference 2 3) (sourceB1027 + difference 3 2) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3955) := by
    have ha : (tripleCharges (sourceA1027 + difference 2 3) (sourceB1027 + difference 3 2) sourceC1027) = raw16808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16808; decide +kernel
    rw [ha]
    exact (canonical16808 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1027 + difference 2 4) (sourceB1027 + difference 4 2) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA1027 + difference 2 4) (sourceB1027 + difference 4 2) sourceC1027) = raw16809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16809; decide +kernel
    rw [ha]
    exact (canonical16809 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1027 + difference 2 5) (sourceB1027 + difference 5 2) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA1027 + difference 2 5) (sourceB1027 + difference 5 2) sourceC1027) = raw16810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16810; decide +kernel
    rw [ha]
    exact (canonical16810 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1027 + difference 3 0) (sourceB1027 + difference 0 3) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA1027 + difference 3 0) (sourceB1027 + difference 0 3) sourceC1027) = raw16811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16811; decide +kernel
    rw [ha]
    exact (canonical16811 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1027 + difference 3 1) (sourceB1027 + difference 1 3) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA1027 + difference 3 1) (sourceB1027 + difference 1 3) sourceC1027) = raw16812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16812; decide +kernel
    rw [ha]
    exact (canonical16812 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1027 + difference 3 2) (sourceB1027 + difference 2 3) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3955) := by
    have ha : (tripleCharges (sourceA1027 + difference 3 2) (sourceB1027 + difference 2 3) sourceC1027) = raw16813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16813; decide +kernel
    rw [ha]
    exact (canonical16813 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1027 + difference 3 4) (sourceB1027 + difference 4 3) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA1027 + difference 3 4) (sourceB1027 + difference 4 3) sourceC1027) = raw16814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16814; decide +kernel
    rw [ha]
    exact (canonical16814 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1027 + difference 3 5) (sourceB1027 + difference 5 3) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA1027 + difference 3 5) (sourceB1027 + difference 5 3) sourceC1027) = raw16815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16815; decide +kernel
    rw [ha]
    exact (canonical16815 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1027 + difference 4 0) (sourceB1027 + difference 0 4) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3491) := by
    have ha : (tripleCharges (sourceA1027 + difference 4 0) (sourceB1027 + difference 0 4) sourceC1027) = raw16816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16816; decide +kernel
    rw [ha]
    exact (canonical16816 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1027 + difference 4 1) (sourceB1027 + difference 1 4) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3768) := by
    have ha : (tripleCharges (sourceA1027 + difference 4 1) (sourceB1027 + difference 1 4) sourceC1027) = raw16817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16817; decide +kernel
    rw [ha]
    exact (canonical16817 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1027 + difference 4 2) (sourceB1027 + difference 2 4) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3750) := by
    have ha : (tripleCharges (sourceA1027 + difference 4 2) (sourceB1027 + difference 2 4) sourceC1027) = raw16818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16818; decide +kernel
    rw [ha]
    exact (canonical16818 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1027 + difference 4 3) (sourceB1027 + difference 3 4) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3750) := by
    have ha : (tripleCharges (sourceA1027 + difference 4 3) (sourceB1027 + difference 3 4) sourceC1027) = raw16819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16819; decide +kernel
    rw [ha]
    exact (canonical16819 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1027 + difference 4 5) (sourceB1027 + difference 5 4) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA1027 + difference 4 5) (sourceB1027 + difference 5 4) sourceC1027) = raw16820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16820; decide +kernel
    rw [ha]
    exact (canonical16820 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1027 + difference 5 0) (sourceB1027 + difference 0 5) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3443) := by
    have ha : (tripleCharges (sourceA1027 + difference 5 0) (sourceB1027 + difference 0 5) sourceC1027) = raw16821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16821; decide +kernel
    rw [ha]
    exact (canonical16821 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1027 + difference 5 1) (sourceB1027 + difference 1 5) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA1027 + difference 5 1) (sourceB1027 + difference 1 5) sourceC1027) = raw16822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16822; decide +kernel
    rw [ha]
    exact (canonical16822 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1027 + difference 5 2) (sourceB1027 + difference 2 5) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3445) := by
    have ha : (tripleCharges (sourceA1027 + difference 5 2) (sourceB1027 + difference 2 5) sourceC1027) = raw16823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16823; decide +kernel
    rw [ha]
    exact (canonical16823 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1027 + difference 5 3) (sourceB1027 + difference 3 5) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3445) := by
    have ha : (tripleCharges (sourceA1027 + difference 5 3) (sourceB1027 + difference 3 5) sourceC1027) = raw16824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16824; decide +kernel
    rw [ha]
    exact (canonical16824 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1027 + difference 5 4) (sourceB1027 + difference 4 5) sourceC1027) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA1027 + difference 5 4) (sourceB1027 + difference 4 5) sourceC1027) = raw16825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1027 sourceB1027 sourceC1027 difference raw16825; decide +kernel
    rw [ha]
    exact (canonical16825 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1027 sourceB1027 sourceC1027
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1027, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1028 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1028 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1028 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceForm1028 : Integer.Sparse Master := [(Sum.inr 2857, 1), (Sum.inr 2859, 1), (Sum.inr 2862, 2), (Sum.inr 3029, 1), (Sum.inr 3953, 1), (Sum.inr 4091, -1)]

theorem sourceEq1028 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1028 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1028 + difference 0 0) (sourceB1028 + difference 0 0) sourceC1028) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA1028 + difference 0 0) (sourceB1028 + difference 0 0) sourceC1028) = raw16826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1028 sourceB1028 sourceC1028 difference raw16826; decide +kernel
    rw [ha]
    exact (canonical16826 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1028 + difference 1 0) (sourceB1028 + difference 0 1) sourceC1028) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3029) := by
    have ha : (tripleCharges (sourceA1028 + difference 1 0) (sourceB1028 + difference 0 1) sourceC1028) = raw16827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1028 sourceB1028 sourceC1028 difference raw16827; decide +kernel
    rw [ha]
    exact (canonical16827 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1028 + difference 2 0) (sourceB1028 + difference 0 2) sourceC1028) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA1028 + difference 2 0) (sourceB1028 + difference 0 2) sourceC1028) = raw16828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1028 sourceB1028 sourceC1028 difference raw16828; decide +kernel
    rw [ha]
    exact (canonical16828 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1028 + difference 3 0) (sourceB1028 + difference 0 3) sourceC1028) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA1028 + difference 3 0) (sourceB1028 + difference 0 3) sourceC1028) = raw16829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1028 sourceB1028 sourceC1028 difference raw16829; decide +kernel
    rw [ha]
    exact (canonical16829 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1028 + difference 4 0) (sourceB1028 + difference 0 4) sourceC1028) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2859) := by
    have ha : (tripleCharges (sourceA1028 + difference 4 0) (sourceB1028 + difference 0 4) sourceC1028) = raw16830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1028 sourceB1028 sourceC1028 difference raw16830; decide +kernel
    rw [ha]
    exact (canonical16830 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1028 + difference 5 0) (sourceB1028 + difference 0 5) sourceC1028) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2857) := by
    have ha : (tripleCharges (sourceA1028 + difference 5 0) (sourceB1028 + difference 0 5) sourceC1028) = raw16831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1028 sourceB1028 sourceC1028 difference raw16831; decide +kernel
    rw [ha]
    exact (canonical16831 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1028 + sourceB1028) sourceC1028) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1028 + sourceB1028) sourceC1028) = raw16832 := by
      apply Matrix.ext; unfold doubleCharges sourceA1028 sourceB1028 sourceC1028 raw16832; decide +kernel
    rw [ha]
    exact (canonical16832 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1028 sourceB1028 sourceC1028
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1028, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1029 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1029 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1029 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceForm1029 : Integer.Sparse Master := [(Sum.inr 2981, 1), (Sum.inr 3685, 1), (Sum.inr 3690, 2), (Sum.inr 3800, 1), (Sum.inr 3953, 1), (Sum.inr 4091, -1)]

theorem sourceEq1029 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1029 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1029 + difference 0 1) (sourceB1029 + difference 1 0) sourceC1029) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA1029 + difference 0 1) (sourceB1029 + difference 1 0) sourceC1029) = raw16833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1029 sourceB1029 sourceC1029 difference raw16833; decide +kernel
    rw [ha]
    exact (canonical16833 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1029 + difference 1 1) (sourceB1029 + difference 1 1) sourceC1029) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA1029 + difference 1 1) (sourceB1029 + difference 1 1) sourceC1029) = raw16826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1029 sourceB1029 sourceC1029 difference raw16826; decide +kernel
    rw [ha]
    exact (canonical16826 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1029 + difference 2 1) (sourceB1029 + difference 1 2) sourceC1029) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA1029 + difference 2 1) (sourceB1029 + difference 1 2) sourceC1029) = raw16834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1029 sourceB1029 sourceC1029 difference raw16834; decide +kernel
    rw [ha]
    exact (canonical16834 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1029 + difference 3 1) (sourceB1029 + difference 1 3) sourceC1029) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA1029 + difference 3 1) (sourceB1029 + difference 1 3) sourceC1029) = raw16835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1029 sourceB1029 sourceC1029 difference raw16835; decide +kernel
    rw [ha]
    exact (canonical16835 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1029 + difference 4 1) (sourceB1029 + difference 1 4) sourceC1029) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3685) := by
    have ha : (tripleCharges (sourceA1029 + difference 4 1) (sourceB1029 + difference 1 4) sourceC1029) = raw16836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1029 sourceB1029 sourceC1029 difference raw16836; decide +kernel
    rw [ha]
    exact (canonical16836 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1029 + difference 5 1) (sourceB1029 + difference 1 5) sourceC1029) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2981) := by
    have ha : (tripleCharges (sourceA1029 + difference 5 1) (sourceB1029 + difference 1 5) sourceC1029) = raw16837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1029 sourceB1029 sourceC1029 difference raw16837; decide +kernel
    rw [ha]
    exact (canonical16837 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1029 + sourceB1029) sourceC1029) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1029 + sourceB1029) sourceC1029) = raw16832 := by
      apply Matrix.ext; unfold doubleCharges sourceA1029 sourceB1029 sourceC1029 raw16832; decide +kernel
    rw [ha]
    exact (canonical16832 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1029 sourceB1029 sourceC1029
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1029, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1030 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB1030 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC1030 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1030 : Integer.Sparse Master := [(Sum.inr 5183, 2), (Sum.inr 5187, 1), (Sum.inr 5197, 1), (Sum.inr 5263, 1), (Sum.inr 5351, 1), (Sum.inr 5353, 2), (Sum.inr 5365, 1), (Sum.inr 5399, 2), (Sum.inr 5400, 1), (Sum.inr 5402, 2), (Sum.inr 5405, 2), (Sum.inr 5414, 2), (Sum.inr 5428, 2), (Sum.inr 5429, 1), (Sum.inr 5438, 2), (Sum.inr 5446, 2), (Sum.inr 5471, 1), (Sum.inr 5473, 2), (Sum.inr 5483, 2)]

theorem sourceEq1030 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1030 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1030 + difference 0 1) (sourceB1030 + difference 1 0) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA1030 + difference 0 1) (sourceB1030 + difference 1 0) sourceC1030) = raw16838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16838; decide +kernel
    rw [ha]
    exact (canonical16838 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1030 + difference 0 2) (sourceB1030 + difference 2 0) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1030 + difference 0 2) (sourceB1030 + difference 2 0) sourceC1030) = raw16839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16839; decide +kernel
    rw [ha]
    exact (canonical16839 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1030 + difference 0 3) (sourceB1030 + difference 3 0) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1030 + difference 0 3) (sourceB1030 + difference 3 0) sourceC1030) = raw16840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16840; decide +kernel
    rw [ha]
    exact (canonical16840 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1030 + difference 0 4) (sourceB1030 + difference 4 0) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA1030 + difference 0 4) (sourceB1030 + difference 4 0) sourceC1030) = raw16841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16841; decide +kernel
    rw [ha]
    exact (canonical16841 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1030 + difference 0 5) (sourceB1030 + difference 5 0) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1030 + difference 0 5) (sourceB1030 + difference 5 0) sourceC1030) = raw16842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16842; decide +kernel
    rw [ha]
    exact (canonical16842 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1030 + difference 1 0) (sourceB1030 + difference 0 1) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1030 + difference 1 0) (sourceB1030 + difference 0 1) sourceC1030) = raw15124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw15124; decide +kernel
    rw [ha]
    exact (canonical15124 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1030 + difference 1 2) (sourceB1030 + difference 2 1) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1030 + difference 1 2) (sourceB1030 + difference 2 1) sourceC1030) = raw15113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw15113; decide +kernel
    rw [ha]
    exact (canonical15113 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1030 + difference 1 3) (sourceB1030 + difference 3 1) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1030 + difference 1 3) (sourceB1030 + difference 3 1) sourceC1030) = raw16843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16843; decide +kernel
    rw [ha]
    exact (canonical16843 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1030 + difference 1 4) (sourceB1030 + difference 4 1) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1030 + difference 1 4) (sourceB1030 + difference 4 1) sourceC1030) = raw15664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw15664; decide +kernel
    rw [ha]
    exact (canonical15664 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1030 + difference 1 5) (sourceB1030 + difference 5 1) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1030 + difference 1 5) (sourceB1030 + difference 5 1) sourceC1030) = raw15858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw15858; decide +kernel
    rw [ha]
    exact (canonical15858 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1030 + difference 2 0) (sourceB1030 + difference 0 2) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA1030 + difference 2 0) (sourceB1030 + difference 0 2) sourceC1030) = raw16844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16844; decide +kernel
    rw [ha]
    exact (canonical16844 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1030 + difference 2 1) (sourceB1030 + difference 1 2) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5183) := by
    have ha : (tripleCharges (sourceA1030 + difference 2 1) (sourceB1030 + difference 1 2) sourceC1030) = raw16845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16845; decide +kernel
    rw [ha]
    exact (canonical16845 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1030 + difference 2 3) (sourceB1030 + difference 3 2) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1030 + difference 2 3) (sourceB1030 + difference 3 2) sourceC1030) = raw16846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16846; decide +kernel
    rw [ha]
    exact (canonical16846 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1030 + difference 2 4) (sourceB1030 + difference 4 2) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5399) := by
    have ha : (tripleCharges (sourceA1030 + difference 2 4) (sourceB1030 + difference 4 2) sourceC1030) = raw16847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16847; decide +kernel
    rw [ha]
    exact (canonical16847 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1030 + difference 2 5) (sourceB1030 + difference 5 2) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5402) := by
    have ha : (tripleCharges (sourceA1030 + difference 2 5) (sourceB1030 + difference 5 2) sourceC1030) = raw16848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16848; decide +kernel
    rw [ha]
    exact (canonical16848 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1030 + difference 3 0) (sourceB1030 + difference 0 3) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA1030 + difference 3 0) (sourceB1030 + difference 0 3) sourceC1030) = raw16849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16849; decide +kernel
    rw [ha]
    exact (canonical16849 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1030 + difference 3 1) (sourceB1030 + difference 1 3) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5183) := by
    have ha : (tripleCharges (sourceA1030 + difference 3 1) (sourceB1030 + difference 1 3) sourceC1030) = raw16850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16850; decide +kernel
    rw [ha]
    exact (canonical16850 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1030 + difference 3 2) (sourceB1030 + difference 2 3) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1030 + difference 3 2) (sourceB1030 + difference 2 3) sourceC1030) = raw16851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16851; decide +kernel
    rw [ha]
    exact (canonical16851 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1030 + difference 3 4) (sourceB1030 + difference 4 3) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5399) := by
    have ha : (tripleCharges (sourceA1030 + difference 3 4) (sourceB1030 + difference 4 3) sourceC1030) = raw16852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16852; decide +kernel
    rw [ha]
    exact (canonical16852 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1030 + difference 3 5) (sourceB1030 + difference 5 3) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5402) := by
    have ha : (tripleCharges (sourceA1030 + difference 3 5) (sourceB1030 + difference 5 3) sourceC1030) = raw16853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16853; decide +kernel
    rw [ha]
    exact (canonical16853 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1030 + difference 4 0) (sourceB1030 + difference 0 4) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA1030 + difference 4 0) (sourceB1030 + difference 0 4) sourceC1030) = raw16854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16854; decide +kernel
    rw [ha]
    exact (canonical16854 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1030 + difference 4 1) (sourceB1030 + difference 1 4) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA1030 + difference 4 1) (sourceB1030 + difference 1 4) sourceC1030) = raw16855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16855; decide +kernel
    rw [ha]
    exact (canonical16855 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1030 + difference 4 2) (sourceB1030 + difference 2 4) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1030 + difference 4 2) (sourceB1030 + difference 2 4) sourceC1030) = raw16856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16856; decide +kernel
    rw [ha]
    exact (canonical16856 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1030 + difference 4 3) (sourceB1030 + difference 3 4) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1030 + difference 4 3) (sourceB1030 + difference 3 4) sourceC1030) = raw16857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16857; decide +kernel
    rw [ha]
    exact (canonical16857 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1030 + difference 4 5) (sourceB1030 + difference 5 4) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1030 + difference 4 5) (sourceB1030 + difference 5 4) sourceC1030) = raw16858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16858; decide +kernel
    rw [ha]
    exact (canonical16858 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1030 + difference 5 0) (sourceB1030 + difference 0 5) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1030 + difference 5 0) (sourceB1030 + difference 0 5) sourceC1030) = raw16859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16859; decide +kernel
    rw [ha]
    exact (canonical16859 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1030 + difference 5 1) (sourceB1030 + difference 1 5) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA1030 + difference 5 1) (sourceB1030 + difference 1 5) sourceC1030) = raw16860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16860; decide +kernel
    rw [ha]
    exact (canonical16860 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1030 + difference 5 2) (sourceB1030 + difference 2 5) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1030 + difference 5 2) (sourceB1030 + difference 2 5) sourceC1030) = raw16861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16861; decide +kernel
    rw [ha]
    exact (canonical16861 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1030 + difference 5 3) (sourceB1030 + difference 3 5) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1030 + difference 5 3) (sourceB1030 + difference 3 5) sourceC1030) = raw16862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16862; decide +kernel
    rw [ha]
    exact (canonical16862 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1030 + difference 5 4) (sourceB1030 + difference 4 5) sourceC1030) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA1030 + difference 5 4) (sourceB1030 + difference 4 5) sourceC1030) = raw16863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1030 sourceB1030 sourceC1030 difference raw16863; decide +kernel
    rw [ha]
    exact (canonical16863 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1030 sourceB1030 sourceC1030
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1030, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1031 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB1031 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC1031 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1031 : Integer.Sparse Master := [(Sum.inr 3501, 2), (Sum.inr 3505, 1), (Sum.inr 3537, 1), (Sum.inr 3569, 1), (Sum.inr 3757, 1), (Sum.inr 3758, 1), (Sum.inr 3761, 2), (Sum.inr 3785, 2), (Sum.inr 3788, 2), (Sum.inr 3800, 1), (Sum.inr 3845, 2), (Sum.inr 3869, 1), (Sum.inr 3884, 2), (Sum.inr 3949, 1), (Sum.inr 3954, 1), (Sum.inr 3958, 2), (Sum.inr 3976, 1), (Sum.inr 3977, 1), (Sum.inr 3981, 2), (Sum.inr 3993, 2), (Sum.inr 4023, 1)]

theorem sourceEq1031 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1031 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1031 + difference 0 1) (sourceB1031 + difference 1 0) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3505) := by
    have ha : (tripleCharges (sourceA1031 + difference 0 1) (sourceB1031 + difference 1 0) sourceC1031) = raw16864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16864; decide +kernel
    rw [ha]
    exact (canonical16864 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1031 + difference 0 2) (sourceB1031 + difference 2 0) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA1031 + difference 0 2) (sourceB1031 + difference 2 0) sourceC1031) = raw16865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16865; decide +kernel
    rw [ha]
    exact (canonical16865 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1031 + difference 0 3) (sourceB1031 + difference 3 0) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA1031 + difference 0 3) (sourceB1031 + difference 3 0) sourceC1031) = raw16866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16866; decide +kernel
    rw [ha]
    exact (canonical16866 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1031 + difference 0 4) (sourceB1031 + difference 4 0) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3949) := by
    have ha : (tripleCharges (sourceA1031 + difference 0 4) (sourceB1031 + difference 4 0) sourceC1031) = raw16867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16867; decide +kernel
    rw [ha]
    exact (canonical16867 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1031 + difference 0 5) (sourceB1031 + difference 5 0) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4023) := by
    have ha : (tripleCharges (sourceA1031 + difference 0 5) (sourceB1031 + difference 5 0) sourceC1031) = raw16868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16868; decide +kernel
    rw [ha]
    exact (canonical16868 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1031 + difference 1 0) (sourceB1031 + difference 0 1) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA1031 + difference 1 0) (sourceB1031 + difference 0 1) sourceC1031) = raw15706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw15706; decide +kernel
    rw [ha]
    exact (canonical15706 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1031 + difference 1 2) (sourceB1031 + difference 2 1) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1031 + difference 1 2) (sourceB1031 + difference 2 1) sourceC1031) = raw16869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16869; decide +kernel
    rw [ha]
    exact (canonical16869 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1031 + difference 1 3) (sourceB1031 + difference 3 1) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1031 + difference 1 3) (sourceB1031 + difference 3 1) sourceC1031) = raw16870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16870; decide +kernel
    rw [ha]
    exact (canonical16870 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1031 + difference 1 4) (sourceB1031 + difference 4 1) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3976) := by
    have ha : (tripleCharges (sourceA1031 + difference 1 4) (sourceB1031 + difference 4 1) sourceC1031) = raw15685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw15685; decide +kernel
    rw [ha]
    exact (canonical15685 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1031 + difference 1 5) (sourceB1031 + difference 5 1) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA1031 + difference 1 5) (sourceB1031 + difference 5 1) sourceC1031) = raw15871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw15871; decide +kernel
    rw [ha]
    exact (canonical15871 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1031 + difference 2 0) (sourceB1031 + difference 0 2) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA1031 + difference 2 0) (sourceB1031 + difference 0 2) sourceC1031) = raw16871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16871; decide +kernel
    rw [ha]
    exact (canonical16871 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1031 + difference 2 1) (sourceB1031 + difference 1 2) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3501) := by
    have ha : (tripleCharges (sourceA1031 + difference 2 1) (sourceB1031 + difference 1 2) sourceC1031) = raw16872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16872; decide +kernel
    rw [ha]
    exact (canonical16872 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1031 + difference 2 3) (sourceB1031 + difference 3 2) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA1031 + difference 2 3) (sourceB1031 + difference 3 2) sourceC1031) = raw16873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16873; decide +kernel
    rw [ha]
    exact (canonical16873 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1031 + difference 2 4) (sourceB1031 + difference 4 2) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3785) := by
    have ha : (tripleCharges (sourceA1031 + difference 2 4) (sourceB1031 + difference 4 2) sourceC1031) = raw16874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16874; decide +kernel
    rw [ha]
    exact (canonical16874 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1031 + difference 2 5) (sourceB1031 + difference 5 2) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA1031 + difference 2 5) (sourceB1031 + difference 5 2) sourceC1031) = raw16875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16875; decide +kernel
    rw [ha]
    exact (canonical16875 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1031 + difference 3 0) (sourceB1031 + difference 0 3) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA1031 + difference 3 0) (sourceB1031 + difference 0 3) sourceC1031) = raw16876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16876; decide +kernel
    rw [ha]
    exact (canonical16876 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1031 + difference 3 1) (sourceB1031 + difference 1 3) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3501) := by
    have ha : (tripleCharges (sourceA1031 + difference 3 1) (sourceB1031 + difference 1 3) sourceC1031) = raw16877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16877; decide +kernel
    rw [ha]
    exact (canonical16877 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1031 + difference 3 2) (sourceB1031 + difference 2 3) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA1031 + difference 3 2) (sourceB1031 + difference 2 3) sourceC1031) = raw16878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16878; decide +kernel
    rw [ha]
    exact (canonical16878 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1031 + difference 3 4) (sourceB1031 + difference 4 3) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3785) := by
    have ha : (tripleCharges (sourceA1031 + difference 3 4) (sourceB1031 + difference 4 3) sourceC1031) = raw16879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16879; decide +kernel
    rw [ha]
    exact (canonical16879 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1031 + difference 3 5) (sourceB1031 + difference 5 3) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA1031 + difference 3 5) (sourceB1031 + difference 5 3) sourceC1031) = raw16880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16880; decide +kernel
    rw [ha]
    exact (canonical16880 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1031 + difference 4 0) (sourceB1031 + difference 0 4) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA1031 + difference 4 0) (sourceB1031 + difference 0 4) sourceC1031) = raw16881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16881; decide +kernel
    rw [ha]
    exact (canonical16881 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1031 + difference 4 1) (sourceB1031 + difference 1 4) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3569) := by
    have ha : (tripleCharges (sourceA1031 + difference 4 1) (sourceB1031 + difference 1 4) sourceC1031) = raw16882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16882; decide +kernel
    rw [ha]
    exact (canonical16882 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1031 + difference 4 2) (sourceB1031 + difference 2 4) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1031 + difference 4 2) (sourceB1031 + difference 2 4) sourceC1031) = raw16883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16883; decide +kernel
    rw [ha]
    exact (canonical16883 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1031 + difference 4 3) (sourceB1031 + difference 3 4) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1031 + difference 4 3) (sourceB1031 + difference 3 4) sourceC1031) = raw16884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16884; decide +kernel
    rw [ha]
    exact (canonical16884 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1031 + difference 4 5) (sourceB1031 + difference 5 4) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA1031 + difference 4 5) (sourceB1031 + difference 5 4) sourceC1031) = raw16885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16885; decide +kernel
    rw [ha]
    exact (canonical16885 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1031 + difference 5 0) (sourceB1031 + difference 0 5) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA1031 + difference 5 0) (sourceB1031 + difference 0 5) sourceC1031) = raw16886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16886; decide +kernel
    rw [ha]
    exact (canonical16886 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1031 + difference 5 1) (sourceB1031 + difference 1 5) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA1031 + difference 5 1) (sourceB1031 + difference 1 5) sourceC1031) = raw16887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16887; decide +kernel
    rw [ha]
    exact (canonical16887 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1031 + difference 5 2) (sourceB1031 + difference 2 5) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA1031 + difference 5 2) (sourceB1031 + difference 2 5) sourceC1031) = raw16888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16888; decide +kernel
    rw [ha]
    exact (canonical16888 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1031 + difference 5 3) (sourceB1031 + difference 3 5) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA1031 + difference 5 3) (sourceB1031 + difference 3 5) sourceC1031) = raw16889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16889; decide +kernel
    rw [ha]
    exact (canonical16889 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1031 + difference 5 4) (sourceB1031 + difference 4 5) sourceC1031) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA1031 + difference 5 4) (sourceB1031 + difference 4 5) sourceC1031) = raw16890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1031 sourceB1031 sourceC1031 difference raw16890; decide +kernel
    rw [ha]
    exact (canonical16890 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1031 sourceB1031 sourceC1031
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1031, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1032 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB1032 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC1032 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1032 : Integer.Sparse Master := [(Sum.inr 2613, 2), (Sum.inr 2617, 1), (Sum.inr 2631, 1), (Sum.inr 2728, 1), (Sum.inr 3783, 2), (Sum.inr 3785, 2), (Sum.inr 3799, 1), (Sum.inr 3800, 1), (Sum.inr 3802, 2), (Sum.inr 3846, 1), (Sum.inr 3869, 1), (Sum.inr 3876, 2), (Sum.inr 3881, 2), (Sum.inr 3937, 1), (Sum.inr 3938, 1), (Sum.inr 3949, 1), (Sum.inr 3953, 1), (Sum.inr 3977, 1), (Sum.inr 3981, 2), (Sum.inr 3995, 2), (Sum.inr 4003, 2)]

theorem sourceEq1032 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1032 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1032 + difference 0 1) (sourceB1032 + difference 1 0) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA1032 + difference 0 1) (sourceB1032 + difference 1 0) sourceC1032) = raw16891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16891; decide +kernel
    rw [ha]
    exact (canonical16891 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1032 + difference 0 2) (sourceB1032 + difference 2 0) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1032 + difference 0 2) (sourceB1032 + difference 2 0) sourceC1032) = raw16892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16892; decide +kernel
    rw [ha]
    exact (canonical16892 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1032 + difference 0 3) (sourceB1032 + difference 3 0) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1032 + difference 0 3) (sourceB1032 + difference 3 0) sourceC1032) = raw16893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16893; decide +kernel
    rw [ha]
    exact (canonical16893 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1032 + difference 0 4) (sourceB1032 + difference 4 0) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA1032 + difference 0 4) (sourceB1032 + difference 4 0) sourceC1032) = raw16894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16894; decide +kernel
    rw [ha]
    exact (canonical16894 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1032 + difference 0 5) (sourceB1032 + difference 5 0) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA1032 + difference 0 5) (sourceB1032 + difference 5 0) sourceC1032) = raw16895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16895; decide +kernel
    rw [ha]
    exact (canonical16895 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1032 + difference 1 0) (sourceB1032 + difference 0 1) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA1032 + difference 1 0) (sourceB1032 + difference 0 1) sourceC1032) = raw15151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw15151; decide +kernel
    rw [ha]
    exact (canonical15151 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1032 + difference 1 2) (sourceB1032 + difference 2 1) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1032 + difference 1 2) (sourceB1032 + difference 2 1) sourceC1032) = raw15140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw15140; decide +kernel
    rw [ha]
    exact (canonical15140 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1032 + difference 1 3) (sourceB1032 + difference 3 1) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1032 + difference 1 3) (sourceB1032 + difference 3 1) sourceC1032) = raw16896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16896; decide +kernel
    rw [ha]
    exact (canonical16896 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1032 + difference 1 4) (sourceB1032 + difference 4 1) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA1032 + difference 1 4) (sourceB1032 + difference 4 1) sourceC1032) = raw15715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw15715; decide +kernel
    rw [ha]
    exact (canonical15715 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1032 + difference 1 5) (sourceB1032 + difference 5 1) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA1032 + difference 1 5) (sourceB1032 + difference 5 1) sourceC1032) = raw15892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw15892; decide +kernel
    rw [ha]
    exact (canonical15892 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1032 + difference 2 0) (sourceB1032 + difference 0 2) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3783) := by
    have ha : (tripleCharges (sourceA1032 + difference 2 0) (sourceB1032 + difference 0 2) sourceC1032) = raw16897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16897; decide +kernel
    rw [ha]
    exact (canonical16897 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1032 + difference 2 1) (sourceB1032 + difference 1 2) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2613) := by
    have ha : (tripleCharges (sourceA1032 + difference 2 1) (sourceB1032 + difference 1 2) sourceC1032) = raw16898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16898; decide +kernel
    rw [ha]
    exact (canonical16898 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1032 + difference 2 3) (sourceB1032 + difference 3 2) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1032 + difference 2 3) (sourceB1032 + difference 3 2) sourceC1032) = raw16899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16899; decide +kernel
    rw [ha]
    exact (canonical16899 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1032 + difference 2 4) (sourceB1032 + difference 4 2) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3785) := by
    have ha : (tripleCharges (sourceA1032 + difference 2 4) (sourceB1032 + difference 4 2) sourceC1032) = raw16900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16900; decide +kernel
    rw [ha]
    exact (canonical16900 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1032 + difference 2 5) (sourceB1032 + difference 5 2) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA1032 + difference 2 5) (sourceB1032 + difference 5 2) sourceC1032) = raw16901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16901; decide +kernel
    rw [ha]
    exact (canonical16901 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1032 + difference 3 0) (sourceB1032 + difference 0 3) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3783) := by
    have ha : (tripleCharges (sourceA1032 + difference 3 0) (sourceB1032 + difference 0 3) sourceC1032) = raw16902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16902; decide +kernel
    rw [ha]
    exact (canonical16902 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1032 + difference 3 1) (sourceB1032 + difference 1 3) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2613) := by
    have ha : (tripleCharges (sourceA1032 + difference 3 1) (sourceB1032 + difference 1 3) sourceC1032) = raw16903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16903; decide +kernel
    rw [ha]
    exact (canonical16903 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1032 + difference 3 2) (sourceB1032 + difference 2 3) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1032 + difference 3 2) (sourceB1032 + difference 2 3) sourceC1032) = raw16904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16904; decide +kernel
    rw [ha]
    exact (canonical16904 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1032 + difference 3 4) (sourceB1032 + difference 4 3) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3785) := by
    have ha : (tripleCharges (sourceA1032 + difference 3 4) (sourceB1032 + difference 4 3) sourceC1032) = raw16905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16905; decide +kernel
    rw [ha]
    exact (canonical16905 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1032 + difference 3 5) (sourceB1032 + difference 5 3) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA1032 + difference 3 5) (sourceB1032 + difference 5 3) sourceC1032) = raw16906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16906; decide +kernel
    rw [ha]
    exact (canonical16906 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1032 + difference 4 0) (sourceB1032 + difference 0 4) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3938) := by
    have ha : (tripleCharges (sourceA1032 + difference 4 0) (sourceB1032 + difference 0 4) sourceC1032) = raw16907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16907; decide +kernel
    rw [ha]
    exact (canonical16907 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1032 + difference 4 1) (sourceB1032 + difference 1 4) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2631) := by
    have ha : (tripleCharges (sourceA1032 + difference 4 1) (sourceB1032 + difference 1 4) sourceC1032) = raw16908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16908; decide +kernel
    rw [ha]
    exact (canonical16908 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1032 + difference 4 2) (sourceB1032 + difference 2 4) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA1032 + difference 4 2) (sourceB1032 + difference 2 4) sourceC1032) = raw16909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16909; decide +kernel
    rw [ha]
    exact (canonical16909 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1032 + difference 4 3) (sourceB1032 + difference 3 4) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA1032 + difference 4 3) (sourceB1032 + difference 3 4) sourceC1032) = raw16910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16910; decide +kernel
    rw [ha]
    exact (canonical16910 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1032 + difference 4 5) (sourceB1032 + difference 5 4) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA1032 + difference 4 5) (sourceB1032 + difference 5 4) sourceC1032) = raw16911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16911; decide +kernel
    rw [ha]
    exact (canonical16911 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1032 + difference 5 0) (sourceB1032 + difference 0 5) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3937) := by
    have ha : (tripleCharges (sourceA1032 + difference 5 0) (sourceB1032 + difference 0 5) sourceC1032) = raw16912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16912; decide +kernel
    rw [ha]
    exact (canonical16912 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1032 + difference 5 1) (sourceB1032 + difference 1 5) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2617) := by
    have ha : (tripleCharges (sourceA1032 + difference 5 1) (sourceB1032 + difference 1 5) sourceC1032) = raw16913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16913; decide +kernel
    rw [ha]
    exact (canonical16913 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1032 + difference 5 2) (sourceB1032 + difference 2 5) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA1032 + difference 5 2) (sourceB1032 + difference 2 5) sourceC1032) = raw16914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16914; decide +kernel
    rw [ha]
    exact (canonical16914 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1032 + difference 5 3) (sourceB1032 + difference 3 5) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA1032 + difference 5 3) (sourceB1032 + difference 3 5) sourceC1032) = raw16915 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16915; decide +kernel
    rw [ha]
    exact (canonical16915 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1032 + difference 5 4) (sourceB1032 + difference 4 5) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3949) := by
    have ha : (tripleCharges (sourceA1032 + difference 5 4) (sourceB1032 + difference 4 5) sourceC1032) = raw16916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16916; decide +kernel
    rw [ha]
    exact (canonical16916 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1032 sourceB1032 sourceC1032
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1032, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1033 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB1033 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC1033 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1033 : Integer.Sparse Master := [(Sum.inr 3689, 1), (Sum.inr 3691, 2), (Sum.inr 3703, 1), (Sum.inr 3805, 1), (Sum.inr 3956, 1), (Sum.inr 4092, -1)]

theorem sourceEq1033 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1033 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1033 + difference 0 0) (sourceB1033 + difference 0 0) sourceC1033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA1033 + difference 0 0) (sourceB1033 + difference 0 0) sourceC1033) = raw16917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1033 sourceB1033 sourceC1033 difference raw16917; decide +kernel
    rw [ha]
    exact (canonical16917 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1033 + difference 1 0) (sourceB1033 + difference 0 1) sourceC1033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA1033 + difference 1 0) (sourceB1033 + difference 0 1) sourceC1033) = raw15750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1033 sourceB1033 sourceC1033 difference raw15750; decide +kernel
    rw [ha]
    exact (canonical15750 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1033 + difference 2 0) (sourceB1033 + difference 0 2) sourceC1033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA1033 + difference 2 0) (sourceB1033 + difference 0 2) sourceC1033) = raw16918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1033 sourceB1033 sourceC1033 difference raw16918; decide +kernel
    rw [ha]
    exact (canonical16918 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1033 + difference 3 0) (sourceB1033 + difference 0 3) sourceC1033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA1033 + difference 3 0) (sourceB1033 + difference 0 3) sourceC1033) = raw16919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1033 sourceB1033 sourceC1033 difference raw16919; decide +kernel
    rw [ha]
    exact (canonical16919 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1033 + difference 4 0) (sourceB1033 + difference 0 4) sourceC1033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3703) := by
    have ha : (tripleCharges (sourceA1033 + difference 4 0) (sourceB1033 + difference 0 4) sourceC1033) = raw16920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1033 sourceB1033 sourceC1033 difference raw16920; decide +kernel
    rw [ha]
    exact (canonical16920 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1033 + difference 5 0) (sourceB1033 + difference 0 5) sourceC1033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3689) := by
    have ha : (tripleCharges (sourceA1033 + difference 5 0) (sourceB1033 + difference 0 5) sourceC1033) = raw16921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1033 sourceB1033 sourceC1033 difference raw16921; decide +kernel
    rw [ha]
    exact (canonical16921 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1033 + sourceB1033) sourceC1033) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1033 + sourceB1033) sourceC1033) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA1033 sourceB1033 sourceC1033 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1033 sourceB1033 sourceC1033
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1033, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1034 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB1034 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC1034 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1034 : Integer.Sparse Master := [(Sum.inr 2861, 1), (Sum.inr 2863, 2), (Sum.inr 2878, 1), (Sum.inr 3036, 1), (Sum.inr 3956, 1), (Sum.inr 4092, -1)]

theorem sourceEq1034 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1034 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1034 + difference 0 1) (sourceB1034 + difference 1 0) sourceC1034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3036) := by
    have ha : (tripleCharges (sourceA1034 + difference 0 1) (sourceB1034 + difference 1 0) sourceC1034) = raw16922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1034 sourceB1034 sourceC1034 difference raw16922; decide +kernel
    rw [ha]
    exact (canonical16922 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1034 + difference 1 1) (sourceB1034 + difference 1 1) sourceC1034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA1034 + difference 1 1) (sourceB1034 + difference 1 1) sourceC1034) = raw16917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1034 sourceB1034 sourceC1034 difference raw16917; decide +kernel
    rw [ha]
    exact (canonical16917 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1034 + difference 2 1) (sourceB1034 + difference 1 2) sourceC1034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2863) := by
    have ha : (tripleCharges (sourceA1034 + difference 2 1) (sourceB1034 + difference 1 2) sourceC1034) = raw16923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1034 sourceB1034 sourceC1034 difference raw16923; decide +kernel
    rw [ha]
    exact (canonical16923 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1034 + difference 3 1) (sourceB1034 + difference 1 3) sourceC1034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2863) := by
    have ha : (tripleCharges (sourceA1034 + difference 3 1) (sourceB1034 + difference 1 3) sourceC1034) = raw16924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1034 sourceB1034 sourceC1034 difference raw16924; decide +kernel
    rw [ha]
    exact (canonical16924 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1034 + difference 4 1) (sourceB1034 + difference 1 4) sourceC1034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2878) := by
    have ha : (tripleCharges (sourceA1034 + difference 4 1) (sourceB1034 + difference 1 4) sourceC1034) = raw16925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1034 sourceB1034 sourceC1034 difference raw16925; decide +kernel
    rw [ha]
    exact (canonical16925 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1034 + difference 5 1) (sourceB1034 + difference 1 5) sourceC1034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2861) := by
    have ha : (tripleCharges (sourceA1034 + difference 5 1) (sourceB1034 + difference 1 5) sourceC1034) = raw16926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1034 sourceB1034 sourceC1034 difference raw16926; decide +kernel
    rw [ha]
    exact (canonical16926 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1034 + sourceB1034) sourceC1034) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1034 + sourceB1034) sourceC1034) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA1034 sourceB1034 sourceC1034 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1034 sourceB1034 sourceC1034
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1034, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1035 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1035 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceC1035 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceForm1035 : Integer.Sparse Master := [(Sum.inr 5051, 1), (Sum.inr 5054, 1), (Sum.inr 5057, 1), (Sum.inr 5085, 1), (Sum.inr 5121, 1), (Sum.inr 5124, 1), (Sum.inr 5145, 1), (Sum.inr 5190, 1), (Sum.inr 5191, 1), (Sum.inr 5197, 1), (Sum.inr 5220, 1), (Sum.inr 5266, 1), (Sum.inr 5281, 1), (Sum.inr 5343, 1), (Sum.inr 5359, 1), (Sum.inr 5425, 1), (Sum.inr 5430, 1), (Sum.inr 5431, 1), (Sum.inr 5433, 1), (Sum.inr 5444, 1), (Sum.inr 5445, 2), (Sum.inr 5446, 1), (Sum.inr 5447, 1), (Sum.inr 5448, 1), (Sum.inr 5450, 1), (Sum.inr 5459, 1), (Sum.inr 5469, 1), (Sum.inr 5473, 1), (Sum.inr 5478, 1)]

theorem sourceEq1035 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1035 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1035 + difference 0 1) (sourceB1035 + difference 1 0) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1035 + difference 0 1) (sourceB1035 + difference 1 0) sourceC1035) = raw16927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16927; decide +kernel
    rw [ha]
    exact (canonical16927 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1035 + difference 0 2) (sourceB1035 + difference 2 0) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1035 + difference 0 2) (sourceB1035 + difference 2 0) sourceC1035) = raw16928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16928; decide +kernel
    rw [ha]
    exact (canonical16928 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1035 + difference 0 3) (sourceB1035 + difference 3 0) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA1035 + difference 0 3) (sourceB1035 + difference 3 0) sourceC1035) = raw16929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16929; decide +kernel
    rw [ha]
    exact (canonical16929 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1035 + difference 0 4) (sourceB1035 + difference 4 0) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1035 + difference 0 4) (sourceB1035 + difference 4 0) sourceC1035) = raw16930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16930; decide +kernel
    rw [ha]
    exact (canonical16930 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1035 + difference 0 5) (sourceB1035 + difference 5 0) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1035 + difference 0 5) (sourceB1035 + difference 5 0) sourceC1035) = raw16931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16931; decide +kernel
    rw [ha]
    exact (canonical16931 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1035 + difference 1 0) (sourceB1035 + difference 0 1) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5220) := by
    have ha : (tripleCharges (sourceA1035 + difference 1 0) (sourceB1035 + difference 0 1) sourceC1035) = raw16932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16932; decide +kernel
    rw [ha]
    exact (canonical16932 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1035 + difference 1 2) (sourceB1035 + difference 2 1) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1035 + difference 1 2) (sourceB1035 + difference 2 1) sourceC1035) = raw16933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16933; decide +kernel
    rw [ha]
    exact (canonical16933 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1035 + difference 1 3) (sourceB1035 + difference 3 1) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA1035 + difference 1 3) (sourceB1035 + difference 3 1) sourceC1035) = raw16934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16934; decide +kernel
    rw [ha]
    exact (canonical16934 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1035 + difference 1 4) (sourceB1035 + difference 4 1) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1035 + difference 1 4) (sourceB1035 + difference 4 1) sourceC1035) = raw16935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16935; decide +kernel
    rw [ha]
    exact (canonical16935 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1035 + difference 1 5) (sourceB1035 + difference 5 1) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1035 + difference 1 5) (sourceB1035 + difference 5 1) sourceC1035) = raw16936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16936; decide +kernel
    rw [ha]
    exact (canonical16936 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1035 + difference 2 0) (sourceB1035 + difference 0 2) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5124) := by
    have ha : (tripleCharges (sourceA1035 + difference 2 0) (sourceB1035 + difference 0 2) sourceC1035) = raw16937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16937; decide +kernel
    rw [ha]
    exact (canonical16937 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1035 + difference 2 1) (sourceB1035 + difference 1 2) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5444) := by
    have ha : (tripleCharges (sourceA1035 + difference 2 1) (sourceB1035 + difference 1 2) sourceC1035) = raw16938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16938; decide +kernel
    rw [ha]
    exact (canonical16938 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1035 + difference 2 3) (sourceB1035 + difference 3 2) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5190) := by
    have ha : (tripleCharges (sourceA1035 + difference 2 3) (sourceB1035 + difference 3 2) sourceC1035) = raw16939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16939; decide +kernel
    rw [ha]
    exact (canonical16939 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1035 + difference 2 4) (sourceB1035 + difference 4 2) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1035 + difference 2 4) (sourceB1035 + difference 4 2) sourceC1035) = raw16940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16940; decide +kernel
    rw [ha]
    exact (canonical16940 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1035 + difference 2 5) (sourceB1035 + difference 5 2) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1035 + difference 2 5) (sourceB1035 + difference 5 2) sourceC1035) = raw16941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16941; decide +kernel
    rw [ha]
    exact (canonical16941 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1035 + difference 3 0) (sourceB1035 + difference 0 3) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA1035 + difference 3 0) (sourceB1035 + difference 0 3) sourceC1035) = raw16942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16942; decide +kernel
    rw [ha]
    exact (canonical16942 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1035 + difference 3 1) (sourceB1035 + difference 1 3) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5459) := by
    have ha : (tripleCharges (sourceA1035 + difference 3 1) (sourceB1035 + difference 1 3) sourceC1035) = raw16943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16943; decide +kernel
    rw [ha]
    exact (canonical16943 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1035 + difference 3 2) (sourceB1035 + difference 2 3) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1035 + difference 3 2) (sourceB1035 + difference 2 3) sourceC1035) = raw16944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16944; decide +kernel
    rw [ha]
    exact (canonical16944 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1035 + difference 3 4) (sourceB1035 + difference 4 3) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1035 + difference 3 4) (sourceB1035 + difference 4 3) sourceC1035) = raw16945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16945; decide +kernel
    rw [ha]
    exact (canonical16945 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1035 + difference 3 5) (sourceB1035 + difference 5 3) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1035 + difference 3 5) (sourceB1035 + difference 5 3) sourceC1035) = raw16946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16946; decide +kernel
    rw [ha]
    exact (canonical16946 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1035 + difference 4 0) (sourceB1035 + difference 0 4) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5121) := by
    have ha : (tripleCharges (sourceA1035 + difference 4 0) (sourceB1035 + difference 0 4) sourceC1035) = raw16947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16947; decide +kernel
    rw [ha]
    exact (canonical16947 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1035 + difference 4 1) (sourceB1035 + difference 1 4) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5343) := by
    have ha : (tripleCharges (sourceA1035 + difference 4 1) (sourceB1035 + difference 1 4) sourceC1035) = raw16948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16948; decide +kernel
    rw [ha]
    exact (canonical16948 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1035 + difference 4 2) (sourceB1035 + difference 2 4) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA1035 + difference 4 2) (sourceB1035 + difference 2 4) sourceC1035) = raw16949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16949; decide +kernel
    rw [ha]
    exact (canonical16949 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1035 + difference 4 3) (sourceB1035 + difference 3 4) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5191) := by
    have ha : (tripleCharges (sourceA1035 + difference 4 3) (sourceB1035 + difference 3 4) sourceC1035) = raw16950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16950; decide +kernel
    rw [ha]
    exact (canonical16950 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1035 + difference 4 5) (sourceB1035 + difference 5 4) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1035 + difference 4 5) (sourceB1035 + difference 5 4) sourceC1035) = raw16951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16951; decide +kernel
    rw [ha]
    exact (canonical16951 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1035 + difference 5 0) (sourceB1035 + difference 0 5) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5051) := by
    have ha : (tripleCharges (sourceA1035 + difference 5 0) (sourceB1035 + difference 0 5) sourceC1035) = raw16952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16952; decide +kernel
    rw [ha]
    exact (canonical16952 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1035 + difference 5 1) (sourceB1035 + difference 1 5) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5054) := by
    have ha : (tripleCharges (sourceA1035 + difference 5 1) (sourceB1035 + difference 1 5) sourceC1035) = raw16953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16953; decide +kernel
    rw [ha]
    exact (canonical16953 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1035 + difference 5 2) (sourceB1035 + difference 2 5) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA1035 + difference 5 2) (sourceB1035 + difference 2 5) sourceC1035) = raw16954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16954; decide +kernel
    rw [ha]
    exact (canonical16954 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1035 + difference 5 3) (sourceB1035 + difference 3 5) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5057) := by
    have ha : (tripleCharges (sourceA1035 + difference 5 3) (sourceB1035 + difference 3 5) sourceC1035) = raw16955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16955; decide +kernel
    rw [ha]
    exact (canonical16955 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1035 + difference 5 4) (sourceB1035 + difference 4 5) sourceC1035) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA1035 + difference 5 4) (sourceB1035 + difference 4 5) sourceC1035) = raw16956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1035 sourceB1035 sourceC1035 difference raw16956; decide +kernel
    rw [ha]
    exact (canonical16956 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1035 sourceB1035 sourceC1035
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1035, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1036 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1036 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceC1036 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceForm1036 : Integer.Sparse Master := [(Sum.inr 2453, 1), (Sum.inr 2456, 1), (Sum.inr 2460, 1), (Sum.inr 2493, 1), (Sum.inr 2533, 1), (Sum.inr 2537, 1), (Sum.inr 2567, 1), (Sum.inr 2662, 1), (Sum.inr 2731, 1), (Sum.inr 3568, 1), (Sum.inr 3569, 1), (Sum.inr 3571, 1), (Sum.inr 3574, 1), (Sum.inr 3680, 1), (Sum.inr 3697, 1), (Sum.inr 3840, 1), (Sum.inr 3848, 1), (Sum.inr 3849, 1), (Sum.inr 3851, 1), (Sum.inr 3879, 1), (Sum.inr 3880, 2), (Sum.inr 3882, 1), (Sum.inr 3884, 1), (Sum.inr 3885, 1), (Sum.inr 3887, 1), (Sum.inr 3923, 1), (Sum.inr 3969, 1), (Sum.inr 3994, 1), (Sum.inr 3995, 1)]

theorem sourceEq1036 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1036 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1036 + difference 0 1) (sourceB1036 + difference 1 0) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1036 + difference 0 1) (sourceB1036 + difference 1 0) sourceC1036) = raw16957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16957; decide +kernel
    rw [ha]
    exact (canonical16957 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1036 + difference 0 2) (sourceB1036 + difference 2 0) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3882) := by
    have ha : (tripleCharges (sourceA1036 + difference 0 2) (sourceB1036 + difference 2 0) sourceC1036) = raw16958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16958; decide +kernel
    rw [ha]
    exact (canonical16958 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1036 + difference 0 3) (sourceB1036 + difference 3 0) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA1036 + difference 0 3) (sourceB1036 + difference 3 0) sourceC1036) = raw16959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16959; decide +kernel
    rw [ha]
    exact (canonical16959 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1036 + difference 0 4) (sourceB1036 + difference 4 0) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA1036 + difference 0 4) (sourceB1036 + difference 4 0) sourceC1036) = raw16960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16960; decide +kernel
    rw [ha]
    exact (canonical16960 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1036 + difference 0 5) (sourceB1036 + difference 5 0) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA1036 + difference 0 5) (sourceB1036 + difference 5 0) sourceC1036) = raw16961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16961; decide +kernel
    rw [ha]
    exact (canonical16961 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1036 + difference 1 0) (sourceB1036 + difference 0 1) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA1036 + difference 1 0) (sourceB1036 + difference 0 1) sourceC1036) = raw16962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16962; decide +kernel
    rw [ha]
    exact (canonical16962 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1036 + difference 1 2) (sourceB1036 + difference 2 1) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1036 + difference 1 2) (sourceB1036 + difference 2 1) sourceC1036) = raw16963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16963; decide +kernel
    rw [ha]
    exact (canonical16963 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1036 + difference 1 3) (sourceB1036 + difference 3 1) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3569) := by
    have ha : (tripleCharges (sourceA1036 + difference 1 3) (sourceB1036 + difference 3 1) sourceC1036) = raw16964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16964; decide +kernel
    rw [ha]
    exact (canonical16964 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1036 + difference 1 4) (sourceB1036 + difference 4 1) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA1036 + difference 1 4) (sourceB1036 + difference 4 1) sourceC1036) = raw16965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16965; decide +kernel
    rw [ha]
    exact (canonical16965 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1036 + difference 1 5) (sourceB1036 + difference 5 1) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA1036 + difference 1 5) (sourceB1036 + difference 5 1) sourceC1036) = raw16966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16966; decide +kernel
    rw [ha]
    exact (canonical16966 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1036 + difference 2 0) (sourceB1036 + difference 0 2) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2537) := by
    have ha : (tripleCharges (sourceA1036 + difference 2 0) (sourceB1036 + difference 0 2) sourceC1036) = raw16967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16967; decide +kernel
    rw [ha]
    exact (canonical16967 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1036 + difference 2 1) (sourceB1036 + difference 1 2) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3879) := by
    have ha : (tripleCharges (sourceA1036 + difference 2 1) (sourceB1036 + difference 1 2) sourceC1036) = raw16968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16968; decide +kernel
    rw [ha]
    exact (canonical16968 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1036 + difference 2 3) (sourceB1036 + difference 3 2) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3568) := by
    have ha : (tripleCharges (sourceA1036 + difference 2 3) (sourceB1036 + difference 3 2) sourceC1036) = raw16969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16969; decide +kernel
    rw [ha]
    exact (canonical16969 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1036 + difference 2 4) (sourceB1036 + difference 4 2) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA1036 + difference 2 4) (sourceB1036 + difference 4 2) sourceC1036) = raw16970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16970; decide +kernel
    rw [ha]
    exact (canonical16970 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1036 + difference 2 5) (sourceB1036 + difference 5 2) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA1036 + difference 2 5) (sourceB1036 + difference 5 2) sourceC1036) = raw16971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16971; decide +kernel
    rw [ha]
    exact (canonical16971 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1036 + difference 3 0) (sourceB1036 + difference 0 3) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA1036 + difference 3 0) (sourceB1036 + difference 0 3) sourceC1036) = raw16972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16972; decide +kernel
    rw [ha]
    exact (canonical16972 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1036 + difference 3 1) (sourceB1036 + difference 1 3) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3923) := by
    have ha : (tripleCharges (sourceA1036 + difference 3 1) (sourceB1036 + difference 1 3) sourceC1036) = raw16973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16973; decide +kernel
    rw [ha]
    exact (canonical16973 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1036 + difference 3 2) (sourceB1036 + difference 2 3) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3969) := by
    have ha : (tripleCharges (sourceA1036 + difference 3 2) (sourceB1036 + difference 2 3) sourceC1036) = raw16974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16974; decide +kernel
    rw [ha]
    exact (canonical16974 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1036 + difference 3 4) (sourceB1036 + difference 4 3) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA1036 + difference 3 4) (sourceB1036 + difference 4 3) sourceC1036) = raw16975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16975; decide +kernel
    rw [ha]
    exact (canonical16975 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1036 + difference 3 5) (sourceB1036 + difference 5 3) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3994) := by
    have ha : (tripleCharges (sourceA1036 + difference 3 5) (sourceB1036 + difference 5 3) sourceC1036) = raw16976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16976; decide +kernel
    rw [ha]
    exact (canonical16976 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1036 + difference 4 0) (sourceB1036 + difference 0 4) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2533) := by
    have ha : (tripleCharges (sourceA1036 + difference 4 0) (sourceB1036 + difference 0 4) sourceC1036) = raw16977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16977; decide +kernel
    rw [ha]
    exact (canonical16977 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1036 + difference 4 1) (sourceB1036 + difference 1 4) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3680) := by
    have ha : (tripleCharges (sourceA1036 + difference 4 1) (sourceB1036 + difference 1 4) sourceC1036) = raw16978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16978; decide +kernel
    rw [ha]
    exact (canonical16978 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1036 + difference 4 2) (sourceB1036 + difference 2 4) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3697) := by
    have ha : (tripleCharges (sourceA1036 + difference 4 2) (sourceB1036 + difference 2 4) sourceC1036) = raw16979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16979; decide +kernel
    rw [ha]
    exact (canonical16979 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1036 + difference 4 3) (sourceB1036 + difference 3 4) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3574) := by
    have ha : (tripleCharges (sourceA1036 + difference 4 3) (sourceB1036 + difference 3 4) sourceC1036) = raw16980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16980; decide +kernel
    rw [ha]
    exact (canonical16980 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1036 + difference 4 5) (sourceB1036 + difference 5 4) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA1036 + difference 4 5) (sourceB1036 + difference 5 4) sourceC1036) = raw16981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16981; decide +kernel
    rw [ha]
    exact (canonical16981 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1036 + difference 5 0) (sourceB1036 + difference 0 5) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2453) := by
    have ha : (tripleCharges (sourceA1036 + difference 5 0) (sourceB1036 + difference 0 5) sourceC1036) = raw16982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16982; decide +kernel
    rw [ha]
    exact (canonical16982 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1036 + difference 5 1) (sourceB1036 + difference 1 5) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2456) := by
    have ha : (tripleCharges (sourceA1036 + difference 5 1) (sourceB1036 + difference 1 5) sourceC1036) = raw16983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16983; decide +kernel
    rw [ha]
    exact (canonical16983 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1036 + difference 5 2) (sourceB1036 + difference 2 5) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2493) := by
    have ha : (tripleCharges (sourceA1036 + difference 5 2) (sourceB1036 + difference 2 5) sourceC1036) = raw16984 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16984; decide +kernel
    rw [ha]
    exact (canonical16984 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1036 + difference 5 3) (sourceB1036 + difference 3 5) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2460) := by
    have ha : (tripleCharges (sourceA1036 + difference 5 3) (sourceB1036 + difference 3 5) sourceC1036) = raw16985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16985; decide +kernel
    rw [ha]
    exact (canonical16985 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1036 + difference 5 4) (sourceB1036 + difference 4 5) sourceC1036) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA1036 + difference 5 4) (sourceB1036 + difference 4 5) sourceC1036) = raw16986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1036 sourceB1036 sourceC1036 difference raw16986; decide +kernel
    rw [ha]
    exact (canonical16986 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1036 sourceB1036 sourceC1036
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1036, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1037 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1037 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceC1037 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceForm1037 : Integer.Sparse Master := [(Sum.inr 2851, 1), (Sum.inr 2852, 1), (Sum.inr 2854, 1), (Sum.inr 2878, 1), (Sum.inr 3074, 1), (Sum.inr 3368, 1), (Sum.inr 3369, 1), (Sum.inr 3371, 1), (Sum.inr 3388, 1), (Sum.inr 3438, 1), (Sum.inr 3461, 1), (Sum.inr 3535, 1), (Sum.inr 3562, 1), (Sum.inr 3747, 1), (Sum.inr 3759, 1), (Sum.inr 3839, 1), (Sum.inr 3943, 1), (Sum.inr 3951, 1), (Sum.inr 3952, 1), (Sum.inr 3959, 1), (Sum.inr 3961, 1), (Sum.inr 3972, 1), (Sum.inr 3974, 1), (Sum.inr 4024, 2), (Sum.inr 4025, 1), (Sum.inr 4026, 1), (Sum.inr 4028, 1), (Sum.inr 4029, 1), (Sum.inr 4033, 1)]

theorem sourceEq1037 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1037 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1037 + difference 0 1) (sourceB1037 + difference 1 0) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA1037 + difference 0 1) (sourceB1037 + difference 1 0) sourceC1037) = raw16987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw16987; decide +kernel
    rw [ha]
    exact (canonical16987 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1037 + difference 0 2) (sourceB1037 + difference 2 0) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4025) := by
    have ha : (tripleCharges (sourceA1037 + difference 0 2) (sourceB1037 + difference 2 0) sourceC1037) = raw16988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw16988; decide +kernel
    rw [ha]
    exact (canonical16988 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1037 + difference 0 3) (sourceB1037 + difference 3 0) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA1037 + difference 0 3) (sourceB1037 + difference 3 0) sourceC1037) = raw16989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw16989; decide +kernel
    rw [ha]
    exact (canonical16989 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1037 + difference 0 4) (sourceB1037 + difference 4 0) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA1037 + difference 0 4) (sourceB1037 + difference 4 0) sourceC1037) = raw16990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw16990; decide +kernel
    rw [ha]
    exact (canonical16990 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1037 + difference 0 5) (sourceB1037 + difference 5 0) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA1037 + difference 0 5) (sourceB1037 + difference 5 0) sourceC1037) = raw16991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw16991; decide +kernel
    rw [ha]
    exact (canonical16991 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1037 + difference 1 0) (sourceB1037 + difference 0 1) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3388) := by
    have ha : (tripleCharges (sourceA1037 + difference 1 0) (sourceB1037 + difference 0 1) sourceC1037) = raw16992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw16992; decide +kernel
    rw [ha]
    exact (canonical16992 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1037 + difference 1 2) (sourceB1037 + difference 2 1) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA1037 + difference 1 2) (sourceB1037 + difference 2 1) sourceC1037) = raw16993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw16993; decide +kernel
    rw [ha]
    exact (canonical16993 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1037 + difference 1 3) (sourceB1037 + difference 3 1) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2878) := by
    have ha : (tripleCharges (sourceA1037 + difference 1 3) (sourceB1037 + difference 3 1) sourceC1037) = raw16994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw16994; decide +kernel
    rw [ha]
    exact (canonical16994 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1037 + difference 1 4) (sourceB1037 + difference 4 1) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4028) := by
    have ha : (tripleCharges (sourceA1037 + difference 1 4) (sourceB1037 + difference 4 1) sourceC1037) = raw16995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw16995; decide +kernel
    rw [ha]
    exact (canonical16995 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1037 + difference 1 5) (sourceB1037 + difference 5 1) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA1037 + difference 1 5) (sourceB1037 + difference 5 1) sourceC1037) = raw16996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw16996; decide +kernel
    rw [ha]
    exact (canonical16996 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1037 + difference 2 0) (sourceB1037 + difference 0 2) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3371) := by
    have ha : (tripleCharges (sourceA1037 + difference 2 0) (sourceB1037 + difference 0 2) sourceC1037) = raw16997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw16997; decide +kernel
    rw [ha]
    exact (canonical16997 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1037 + difference 2 1) (sourceB1037 + difference 1 2) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3943) := by
    have ha : (tripleCharges (sourceA1037 + difference 2 1) (sourceB1037 + difference 1 2) sourceC1037) = raw16998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw16998; decide +kernel
    rw [ha]
    exact (canonical16998 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1037 + difference 2 3) (sourceB1037 + difference 3 2) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2854) := by
    have ha : (tripleCharges (sourceA1037 + difference 2 3) (sourceB1037 + difference 3 2) sourceC1037) = raw16999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw16999; decide +kernel
    rw [ha]
    exact (canonical16999 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1037 + difference 2 4) (sourceB1037 + difference 4 2) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1037 + difference 2 4) (sourceB1037 + difference 4 2) sourceC1037) = raw17000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17000; decide +kernel
    rw [ha]
    exact (canonical17000 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1037 + difference 2 5) (sourceB1037 + difference 5 2) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA1037 + difference 2 5) (sourceB1037 + difference 5 2) sourceC1037) = raw17001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17001; decide +kernel
    rw [ha]
    exact (canonical17001 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1037 + difference 3 0) (sourceB1037 + difference 0 3) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA1037 + difference 3 0) (sourceB1037 + difference 0 3) sourceC1037) = raw17002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17002; decide +kernel
    rw [ha]
    exact (canonical17002 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1037 + difference 3 1) (sourceB1037 + difference 1 3) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3951) := by
    have ha : (tripleCharges (sourceA1037 + difference 3 1) (sourceB1037 + difference 1 3) sourceC1037) = raw17003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17003; decide +kernel
    rw [ha]
    exact (canonical17003 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1037 + difference 3 2) (sourceB1037 + difference 2 3) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3952) := by
    have ha : (tripleCharges (sourceA1037 + difference 3 2) (sourceB1037 + difference 2 3) sourceC1037) = raw17004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17004; decide +kernel
    rw [ha]
    exact (canonical17004 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1037 + difference 3 4) (sourceB1037 + difference 4 3) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA1037 + difference 3 4) (sourceB1037 + difference 4 3) sourceC1037) = raw17005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17005; decide +kernel
    rw [ha]
    exact (canonical17005 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1037 + difference 3 5) (sourceB1037 + difference 5 3) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA1037 + difference 3 5) (sourceB1037 + difference 5 3) sourceC1037) = raw17006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17006; decide +kernel
    rw [ha]
    exact (canonical17006 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1037 + difference 4 0) (sourceB1037 + difference 0 4) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3369) := by
    have ha : (tripleCharges (sourceA1037 + difference 4 0) (sourceB1037 + difference 0 4) sourceC1037) = raw17007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17007; decide +kernel
    rw [ha]
    exact (canonical17007 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1037 + difference 4 1) (sourceB1037 + difference 1 4) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3747) := by
    have ha : (tripleCharges (sourceA1037 + difference 4 1) (sourceB1037 + difference 1 4) sourceC1037) = raw17008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17008; decide +kernel
    rw [ha]
    exact (canonical17008 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1037 + difference 4 2) (sourceB1037 + difference 2 4) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3759) := by
    have ha : (tripleCharges (sourceA1037 + difference 4 2) (sourceB1037 + difference 2 4) sourceC1037) = raw17009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17009; decide +kernel
    rw [ha]
    exact (canonical17009 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1037 + difference 4 3) (sourceB1037 + difference 3 4) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2852) := by
    have ha : (tripleCharges (sourceA1037 + difference 4 3) (sourceB1037 + difference 3 4) sourceC1037) = raw17010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17010; decide +kernel
    rw [ha]
    exact (canonical17010 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1037 + difference 4 5) (sourceB1037 + difference 5 4) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA1037 + difference 4 5) (sourceB1037 + difference 5 4) sourceC1037) = raw17011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17011; decide +kernel
    rw [ha]
    exact (canonical17011 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1037 + difference 5 0) (sourceB1037 + difference 0 5) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3368) := by
    have ha : (tripleCharges (sourceA1037 + difference 5 0) (sourceB1037 + difference 0 5) sourceC1037) = raw17012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17012; decide +kernel
    rw [ha]
    exact (canonical17012 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1037 + difference 5 1) (sourceB1037 + difference 1 5) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3438) := by
    have ha : (tripleCharges (sourceA1037 + difference 5 1) (sourceB1037 + difference 1 5) sourceC1037) = raw17013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17013; decide +kernel
    rw [ha]
    exact (canonical17013 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1037 + difference 5 2) (sourceB1037 + difference 2 5) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA1037 + difference 5 2) (sourceB1037 + difference 2 5) sourceC1037) = raw17014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17014; decide +kernel
    rw [ha]
    exact (canonical17014 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1037 + difference 5 3) (sourceB1037 + difference 3 5) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2851) := by
    have ha : (tripleCharges (sourceA1037 + difference 5 3) (sourceB1037 + difference 3 5) sourceC1037) = raw17015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17015; decide +kernel
    rw [ha]
    exact (canonical17015 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1037 + difference 5 4) (sourceB1037 + difference 4 5) sourceC1037) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA1037 + difference 5 4) (sourceB1037 + difference 4 5) sourceC1037) = raw17016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1037 sourceB1037 sourceC1037 difference raw17016; decide +kernel
    rw [ha]
    exact (canonical17016 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1037 sourceB1037 sourceC1037
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1037, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1038 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1038 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceC1038 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceForm1038 : Integer.Sparse Master := [(Sum.inr 2918, 1), (Sum.inr 2920, 1), (Sum.inr 2925, 1), (Sum.inr 2944, 1), (Sum.inr 3068, 1), (Sum.inr 3880, 1), (Sum.inr 4091, -1)]

theorem sourceEq1038 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1038 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1038 + difference 0 0) (sourceB1038 + difference 0 0) sourceC1038) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1038 + difference 0 0) (sourceB1038 + difference 0 0) sourceC1038) = raw17017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1038 sourceB1038 sourceC1038 difference raw17017; decide +kernel
    rw [ha]
    exact (canonical17017 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1038 + difference 1 0) (sourceB1038 + difference 0 1) sourceC1038) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3068) := by
    have ha : (tripleCharges (sourceA1038 + difference 1 0) (sourceB1038 + difference 0 1) sourceC1038) = raw17018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1038 sourceB1038 sourceC1038 difference raw17018; decide +kernel
    rw [ha]
    exact (canonical17018 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1038 + difference 2 0) (sourceB1038 + difference 0 2) sourceC1038) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2944) := by
    have ha : (tripleCharges (sourceA1038 + difference 2 0) (sourceB1038 + difference 0 2) sourceC1038) = raw17019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1038 sourceB1038 sourceC1038 difference raw17019; decide +kernel
    rw [ha]
    exact (canonical17019 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1038 + difference 3 0) (sourceB1038 + difference 0 3) sourceC1038) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA1038 + difference 3 0) (sourceB1038 + difference 0 3) sourceC1038) = raw17020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1038 sourceB1038 sourceC1038 difference raw17020; decide +kernel
    rw [ha]
    exact (canonical17020 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1038 + difference 4 0) (sourceB1038 + difference 0 4) sourceC1038) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2920) := by
    have ha : (tripleCharges (sourceA1038 + difference 4 0) (sourceB1038 + difference 0 4) sourceC1038) = raw17021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1038 sourceB1038 sourceC1038 difference raw17021; decide +kernel
    rw [ha]
    exact (canonical17021 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1038 + difference 5 0) (sourceB1038 + difference 0 5) sourceC1038) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2918) := by
    have ha : (tripleCharges (sourceA1038 + difference 5 0) (sourceB1038 + difference 0 5) sourceC1038) = raw17022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1038 sourceB1038 sourceC1038 difference raw17022; decide +kernel
    rw [ha]
    exact (canonical17022 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1038 + sourceB1038) sourceC1038) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1038 + sourceB1038) sourceC1038) = raw17023 := by
      apply Matrix.ext; unfold doubleCharges sourceA1038 sourceB1038 sourceC1038 raw17023; decide +kernel
    rw [ha]
    exact (canonical17023 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1038 sourceB1038 sourceC1038
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1038, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1039 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1039 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceC1039 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceForm1039 : Integer.Sparse Master := [(Sum.inr 2976, 1), (Sum.inr 3878, 1), (Sum.inr 3880, 2), (Sum.inr 3909, 1), (Sum.inr 3945, 1), (Sum.inr 4091, -1)]

theorem sourceEq1039 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1039 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1039 + difference 0 2) (sourceB1039 + difference 2 0) sourceC1039) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA1039 + difference 0 2) (sourceB1039 + difference 2 0) sourceC1039) = raw17024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1039 sourceB1039 sourceC1039 difference raw17024; decide +kernel
    rw [ha]
    exact (canonical17024 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1039 + difference 1 2) (sourceB1039 + difference 2 1) sourceC1039) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1039 + difference 1 2) (sourceB1039 + difference 2 1) sourceC1039) = raw17025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1039 sourceB1039 sourceC1039 difference raw17025; decide +kernel
    rw [ha]
    exact (canonical17025 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1039 + difference 2 2) (sourceB1039 + difference 2 2) sourceC1039) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1039 + difference 2 2) (sourceB1039 + difference 2 2) sourceC1039) = raw17017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1039 sourceB1039 sourceC1039 difference raw17017; decide +kernel
    rw [ha]
    exact (canonical17017 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1039 + difference 3 2) (sourceB1039 + difference 2 3) sourceC1039) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3945) := by
    have ha : (tripleCharges (sourceA1039 + difference 3 2) (sourceB1039 + difference 2 3) sourceC1039) = raw17026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1039 sourceB1039 sourceC1039 difference raw17026; decide +kernel
    rw [ha]
    exact (canonical17026 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1039 + difference 4 2) (sourceB1039 + difference 2 4) sourceC1039) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3878) := by
    have ha : (tripleCharges (sourceA1039 + difference 4 2) (sourceB1039 + difference 2 4) sourceC1039) = raw17027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1039 sourceB1039 sourceC1039 difference raw17027; decide +kernel
    rw [ha]
    exact (canonical17027 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1039 + difference 5 2) (sourceB1039 + difference 2 5) sourceC1039) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA1039 + difference 5 2) (sourceB1039 + difference 2 5) sourceC1039) = raw17028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1039 sourceB1039 sourceC1039 difference raw17028; decide +kernel
    rw [ha]
    exact (canonical17028 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1039 + sourceB1039) sourceC1039) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1039 + sourceB1039) sourceC1039) = raw17023 := by
      apply Matrix.ext; unfold doubleCharges sourceA1039 sourceB1039 sourceC1039 raw17023; decide +kernel
    rw [ha]
    exact (canonical17023 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1039 sourceB1039 sourceC1039
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1039, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1040 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceB1040 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC1040 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1040 : Integer.Sparse Master := [(Sum.inr 4848, 1), (Sum.inr 4849, 2), (Sum.inr 4852, 2), (Sum.inr 5378, 2), (Sum.inr 5379, 2), (Sum.inr 5381, 2), (Sum.inr 5382, 2), (Sum.inr 5397, 2), (Sum.inr 5411, 2), (Sum.inr 5420, 2), (Sum.inr 5421, 2), (Sum.inr 5424, 2), (Sum.inr 5425, 2), (Sum.inr 5446, 2), (Sum.inr 5477, 2), (Sum.inr 5483, 1)]

theorem sourceEq1040 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1040 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1040 + difference 0 1) (sourceB1040 + difference 1 0) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5382) := by
    have ha : (tripleCharges (sourceA1040 + difference 0 1) (sourceB1040 + difference 1 0) sourceC1040) = raw17029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17029; decide +kernel
    rw [ha]
    exact (canonical17029 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1040 + difference 0 2) (sourceB1040 + difference 2 0) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA1040 + difference 0 2) (sourceB1040 + difference 2 0) sourceC1040) = raw17030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17030; decide +kernel
    rw [ha]
    exact (canonical17030 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1040 + difference 0 3) (sourceB1040 + difference 3 0) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1040 + difference 0 3) (sourceB1040 + difference 3 0) sourceC1040) = raw17031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17031; decide +kernel
    rw [ha]
    exact (canonical17031 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1040 + difference 0 4) (sourceB1040 + difference 4 0) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA1040 + difference 0 4) (sourceB1040 + difference 4 0) sourceC1040) = raw17032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17032; decide +kernel
    rw [ha]
    exact (canonical17032 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1040 + difference 0 5) (sourceB1040 + difference 5 0) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1040 + difference 0 5) (sourceB1040 + difference 5 0) sourceC1040) = raw17033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17033; decide +kernel
    rw [ha]
    exact (canonical17033 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1040 + difference 1 0) (sourceB1040 + difference 0 1) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1040 + difference 1 0) (sourceB1040 + difference 0 1) sourceC1040) = raw15130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw15130; decide +kernel
    rw [ha]
    exact (canonical15130 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1040 + difference 1 2) (sourceB1040 + difference 2 1) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5420) := by
    have ha : (tripleCharges (sourceA1040 + difference 1 2) (sourceB1040 + difference 2 1) sourceC1040) = raw17034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17034; decide +kernel
    rw [ha]
    exact (canonical17034 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1040 + difference 1 3) (sourceB1040 + difference 3 1) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1040 + difference 1 3) (sourceB1040 + difference 3 1) sourceC1040) = raw15114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw15114; decide +kernel
    rw [ha]
    exact (canonical15114 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1040 + difference 1 4) (sourceB1040 + difference 4 1) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1040 + difference 1 4) (sourceB1040 + difference 4 1) sourceC1040) = raw17035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17035; decide +kernel
    rw [ha]
    exact (canonical17035 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1040 + difference 1 5) (sourceB1040 + difference 5 1) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1040 + difference 1 5) (sourceB1040 + difference 5 1) sourceC1040) = raw17036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17036; decide +kernel
    rw [ha]
    exact (canonical17036 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1040 + difference 2 0) (sourceB1040 + difference 0 2) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1040 + difference 2 0) (sourceB1040 + difference 0 2) sourceC1040) = raw15129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw15129; decide +kernel
    rw [ha]
    exact (canonical15129 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1040 + difference 2 1) (sourceB1040 + difference 1 2) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1040 + difference 2 1) (sourceB1040 + difference 1 2) sourceC1040) = raw16851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw16851; decide +kernel
    rw [ha]
    exact (canonical16851 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1040 + difference 2 3) (sourceB1040 + difference 3 2) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1040 + difference 2 3) (sourceB1040 + difference 3 2) sourceC1040) = raw15113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw15113; decide +kernel
    rw [ha]
    exact (canonical15113 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1040 + difference 2 4) (sourceB1040 + difference 4 2) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1040 + difference 2 4) (sourceB1040 + difference 4 2) sourceC1040) = raw17037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17037; decide +kernel
    rw [ha]
    exact (canonical17037 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1040 + difference 2 5) (sourceB1040 + difference 5 2) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1040 + difference 2 5) (sourceB1040 + difference 5 2) sourceC1040) = raw17038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17038; decide +kernel
    rw [ha]
    exact (canonical17038 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1040 + difference 3 0) (sourceB1040 + difference 0 3) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA1040 + difference 3 0) (sourceB1040 + difference 0 3) sourceC1040) = raw17039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17039; decide +kernel
    rw [ha]
    exact (canonical17039 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1040 + difference 3 1) (sourceB1040 + difference 1 3) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4849) := by
    have ha : (tripleCharges (sourceA1040 + difference 3 1) (sourceB1040 + difference 1 3) sourceC1040) = raw17040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17040; decide +kernel
    rw [ha]
    exact (canonical17040 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1040 + difference 3 2) (sourceB1040 + difference 2 3) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4848) := by
    have ha : (tripleCharges (sourceA1040 + difference 3 2) (sourceB1040 + difference 2 3) sourceC1040) = raw17041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17041; decide +kernel
    rw [ha]
    exact (canonical17041 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1040 + difference 3 4) (sourceB1040 + difference 4 3) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4849) := by
    have ha : (tripleCharges (sourceA1040 + difference 3 4) (sourceB1040 + difference 4 3) sourceC1040) = raw17042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17042; decide +kernel
    rw [ha]
    exact (canonical17042 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1040 + difference 3 5) (sourceB1040 + difference 5 3) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA1040 + difference 3 5) (sourceB1040 + difference 5 3) sourceC1040) = raw17043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17043; decide +kernel
    rw [ha]
    exact (canonical17043 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1040 + difference 4 0) (sourceB1040 + difference 0 4) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1040 + difference 4 0) (sourceB1040 + difference 0 4) sourceC1040) = raw17044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17044; decide +kernel
    rw [ha]
    exact (canonical17044 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1040 + difference 4 1) (sourceB1040 + difference 1 4) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1040 + difference 4 1) (sourceB1040 + difference 1 4) sourceC1040) = raw17045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17045; decide +kernel
    rw [ha]
    exact (canonical17045 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1040 + difference 4 2) (sourceB1040 + difference 2 4) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5420) := by
    have ha : (tripleCharges (sourceA1040 + difference 4 2) (sourceB1040 + difference 2 4) sourceC1040) = raw17046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17046; decide +kernel
    rw [ha]
    exact (canonical17046 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1040 + difference 4 3) (sourceB1040 + difference 3 4) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1040 + difference 4 3) (sourceB1040 + difference 3 4) sourceC1040) = raw17047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17047; decide +kernel
    rw [ha]
    exact (canonical17047 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1040 + difference 4 5) (sourceB1040 + difference 5 4) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1040 + difference 4 5) (sourceB1040 + difference 5 4) sourceC1040) = raw17048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17048; decide +kernel
    rw [ha]
    exact (canonical17048 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1040 + difference 5 0) (sourceB1040 + difference 0 5) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1040 + difference 5 0) (sourceB1040 + difference 0 5) sourceC1040) = raw17049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17049; decide +kernel
    rw [ha]
    exact (canonical17049 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1040 + difference 5 1) (sourceB1040 + difference 1 5) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA1040 + difference 5 1) (sourceB1040 + difference 1 5) sourceC1040) = raw17050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17050; decide +kernel
    rw [ha]
    exact (canonical17050 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1040 + difference 5 2) (sourceB1040 + difference 2 5) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA1040 + difference 5 2) (sourceB1040 + difference 2 5) sourceC1040) = raw17051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17051; decide +kernel
    rw [ha]
    exact (canonical17051 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1040 + difference 5 3) (sourceB1040 + difference 3 5) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1040 + difference 5 3) (sourceB1040 + difference 3 5) sourceC1040) = raw17052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17052; decide +kernel
    rw [ha]
    exact (canonical17052 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1040 + difference 5 4) (sourceB1040 + difference 4 5) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5382) := by
    have ha : (tripleCharges (sourceA1040 + difference 5 4) (sourceB1040 + difference 4 5) sourceC1040) = raw17053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17053; decide +kernel
    rw [ha]
    exact (canonical17053 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1040 sourceB1040 sourceC1040
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1040, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1041 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceB1041 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC1041 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1041 : Integer.Sparse Master := [(Sum.inr 2085, 1), (Sum.inr 2086, 1), (Sum.inr 2089, 1), (Sum.inr 2098, 1), (Sum.inr 2250, 1), (Sum.inr 3723, 1), (Sum.inr 3724, 1), (Sum.inr 3727, 1), (Sum.inr 3730, 1), (Sum.inr 3795, 1), (Sum.inr 3796, 1), (Sum.inr 3813, 1), (Sum.inr 3826, 1), (Sum.inr 3827, 1), (Sum.inr 3830, 1), (Sum.inr 3832, 1), (Sum.inr 3834, 1), (Sum.inr 3838, 1), (Sum.inr 3840, 1), (Sum.inr 3866, 1), (Sum.inr 3870, 1), (Sum.inr 3872, 1), (Sum.inr 3873, 1), (Sum.inr 3881, 1), (Sum.inr 3883, 1), (Sum.inr 3884, 1), (Sum.inr 3971, 1), (Sum.inr 3981, 1), (Sum.inr 3989, 1), (Sum.inr 3990, 1)]

theorem sourceEq1041 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1041 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1041 + difference 0 1) (sourceB1041 + difference 1 0) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3730) := by
    have ha : (tripleCharges (sourceA1041 + difference 0 1) (sourceB1041 + difference 1 0) sourceC1041) = raw17054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17054; decide +kernel
    rw [ha]
    exact (canonical17054 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1041 + difference 0 2) (sourceB1041 + difference 2 0) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3723) := by
    have ha : (tripleCharges (sourceA1041 + difference 0 2) (sourceB1041 + difference 2 0) sourceC1041) = raw17055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17055; decide +kernel
    rw [ha]
    exact (canonical17055 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1041 + difference 0 3) (sourceB1041 + difference 3 0) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA1041 + difference 0 3) (sourceB1041 + difference 3 0) sourceC1041) = raw17056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17056; decide +kernel
    rw [ha]
    exact (canonical17056 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1041 + difference 0 4) (sourceB1041 + difference 4 0) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA1041 + difference 0 4) (sourceB1041 + difference 4 0) sourceC1041) = raw17057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17057; decide +kernel
    rw [ha]
    exact (canonical17057 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1041 + difference 0 5) (sourceB1041 + difference 5 0) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3727) := by
    have ha : (tripleCharges (sourceA1041 + difference 0 5) (sourceB1041 + difference 5 0) sourceC1041) = raw17058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17058; decide +kernel
    rw [ha]
    exact (canonical17058 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1041 + difference 1 0) (sourceB1041 + difference 0 1) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA1041 + difference 1 0) (sourceB1041 + difference 0 1) sourceC1041) = raw16174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw16174; decide +kernel
    rw [ha]
    exact (canonical16174 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1041 + difference 1 2) (sourceB1041 + difference 2 1) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3826) := by
    have ha : (tripleCharges (sourceA1041 + difference 1 2) (sourceB1041 + difference 2 1) sourceC1041) = raw17059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17059; decide +kernel
    rw [ha]
    exact (canonical17059 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1041 + difference 1 3) (sourceB1041 + difference 3 1) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3989) := by
    have ha : (tripleCharges (sourceA1041 + difference 1 3) (sourceB1041 + difference 3 1) sourceC1041) = raw16161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw16161; decide +kernel
    rw [ha]
    exact (canonical16161 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1041 + difference 1 4) (sourceB1041 + difference 4 1) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3827) := by
    have ha : (tripleCharges (sourceA1041 + difference 1 4) (sourceB1041 + difference 4 1) sourceC1041) = raw17060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17060; decide +kernel
    rw [ha]
    exact (canonical17060 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1041 + difference 1 5) (sourceB1041 + difference 5 1) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3830) := by
    have ha : (tripleCharges (sourceA1041 + difference 1 5) (sourceB1041 + difference 5 1) sourceC1041) = raw17061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17061; decide +kernel
    rw [ha]
    exact (canonical17061 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1041 + difference 2 0) (sourceB1041 + difference 0 2) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA1041 + difference 2 0) (sourceB1041 + difference 0 2) sourceC1041) = raw17062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17062; decide +kernel
    rw [ha]
    exact (canonical17062 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1041 + difference 2 1) (sourceB1041 + difference 1 2) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA1041 + difference 2 1) (sourceB1041 + difference 1 2) sourceC1041) = raw16878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw16878; decide +kernel
    rw [ha]
    exact (canonical16878 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1041 + difference 2 3) (sourceB1041 + difference 3 2) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1041 + difference 2 3) (sourceB1041 + difference 3 2) sourceC1041) = raw16869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw16869; decide +kernel
    rw [ha]
    exact (canonical16869 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1041 + difference 2 4) (sourceB1041 + difference 4 2) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1041 + difference 2 4) (sourceB1041 + difference 4 2) sourceC1041) = raw17063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17063; decide +kernel
    rw [ha]
    exact (canonical17063 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1041 + difference 2 5) (sourceB1041 + difference 5 2) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA1041 + difference 2 5) (sourceB1041 + difference 5 2) sourceC1041) = raw17064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17064; decide +kernel
    rw [ha]
    exact (canonical17064 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1041 + difference 3 0) (sourceB1041 + difference 0 3) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA1041 + difference 3 0) (sourceB1041 + difference 0 3) sourceC1041) = raw17065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17065; decide +kernel
    rw [ha]
    exact (canonical17065 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1041 + difference 3 1) (sourceB1041 + difference 1 3) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2098) := by
    have ha : (tripleCharges (sourceA1041 + difference 3 1) (sourceB1041 + difference 1 3) sourceC1041) = raw17066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17066; decide +kernel
    rw [ha]
    exact (canonical17066 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1041 + difference 3 2) (sourceB1041 + difference 2 3) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2085) := by
    have ha : (tripleCharges (sourceA1041 + difference 3 2) (sourceB1041 + difference 2 3) sourceC1041) = raw17067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17067; decide +kernel
    rw [ha]
    exact (canonical17067 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1041 + difference 3 4) (sourceB1041 + difference 4 3) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2086) := by
    have ha : (tripleCharges (sourceA1041 + difference 3 4) (sourceB1041 + difference 4 3) sourceC1041) = raw17068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17068; decide +kernel
    rw [ha]
    exact (canonical17068 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1041 + difference 3 5) (sourceB1041 + difference 5 3) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA1041 + difference 3 5) (sourceB1041 + difference 5 3) sourceC1041) = raw17069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17069; decide +kernel
    rw [ha]
    exact (canonical17069 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1041 + difference 4 0) (sourceB1041 + difference 0 4) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA1041 + difference 4 0) (sourceB1041 + difference 0 4) sourceC1041) = raw17070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17070; decide +kernel
    rw [ha]
    exact (canonical17070 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1041 + difference 4 1) (sourceB1041 + difference 1 4) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA1041 + difference 4 1) (sourceB1041 + difference 1 4) sourceC1041) = raw17071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17071; decide +kernel
    rw [ha]
    exact (canonical17071 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1041 + difference 4 2) (sourceB1041 + difference 2 4) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3870) := by
    have ha : (tripleCharges (sourceA1041 + difference 4 2) (sourceB1041 + difference 2 4) sourceC1041) = raw17072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17072; decide +kernel
    rw [ha]
    exact (canonical17072 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1041 + difference 4 3) (sourceB1041 + difference 3 4) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3971) := by
    have ha : (tripleCharges (sourceA1041 + difference 4 3) (sourceB1041 + difference 3 4) sourceC1041) = raw17073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17073; decide +kernel
    rw [ha]
    exact (canonical17073 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1041 + difference 4 5) (sourceB1041 + difference 5 4) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA1041 + difference 4 5) (sourceB1041 + difference 5 4) sourceC1041) = raw17074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17074; decide +kernel
    rw [ha]
    exact (canonical17074 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1041 + difference 5 0) (sourceB1041 + difference 0 5) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA1041 + difference 5 0) (sourceB1041 + difference 0 5) sourceC1041) = raw17075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17075; decide +kernel
    rw [ha]
    exact (canonical17075 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1041 + difference 5 1) (sourceB1041 + difference 1 5) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA1041 + difference 5 1) (sourceB1041 + difference 1 5) sourceC1041) = raw17076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17076; decide +kernel
    rw [ha]
    exact (canonical17076 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1041 + difference 5 2) (sourceB1041 + difference 2 5) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA1041 + difference 5 2) (sourceB1041 + difference 2 5) sourceC1041) = raw17077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17077; decide +kernel
    rw [ha]
    exact (canonical17077 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1041 + difference 5 3) (sourceB1041 + difference 3 5) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA1041 + difference 5 3) (sourceB1041 + difference 3 5) sourceC1041) = raw17078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17078; decide +kernel
    rw [ha]
    exact (canonical17078 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1041 + difference 5 4) (sourceB1041 + difference 4 5) sourceC1041) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA1041 + difference 5 4) (sourceB1041 + difference 4 5) sourceC1041) = raw17079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1041 sourceB1041 sourceC1041 difference raw17079; decide +kernel
    rw [ha]
    exact (canonical17079 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1041 sourceB1041 sourceC1041
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1041, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1042 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceB1042 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC1042 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1042 : Integer.Sparse Master := [(Sum.inr 3173, 1), (Sum.inr 3722, 2), (Sum.inr 4022, 2), (Sum.inr 4024, 1), (Sum.inr 4092, -1)]

theorem sourceEq1042 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1042 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1042 + difference 0 2) (sourceB1042 + difference 2 0) sourceC1042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3722) := by
    have ha : (tripleCharges (sourceA1042 + difference 0 2) (sourceB1042 + difference 2 0) sourceC1042) = raw17080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1042 sourceB1042 sourceC1042 difference raw17080; decide +kernel
    rw [ha]
    exact (canonical17080 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1042 + difference 1 2) (sourceB1042 + difference 2 1) sourceC1042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4022) := by
    have ha : (tripleCharges (sourceA1042 + difference 1 2) (sourceB1042 + difference 2 1) sourceC1042) = raw17081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1042 sourceB1042 sourceC1042 difference raw17081; decide +kernel
    rw [ha]
    exact (canonical17081 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1042 + difference 2 2) (sourceB1042 + difference 2 2) sourceC1042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA1042 + difference 2 2) (sourceB1042 + difference 2 2) sourceC1042) = raw17082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1042 sourceB1042 sourceC1042 difference raw17082; decide +kernel
    rw [ha]
    exact (canonical17082 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1042 + difference 3 2) (sourceB1042 + difference 2 3) sourceC1042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3173) := by
    have ha : (tripleCharges (sourceA1042 + difference 3 2) (sourceB1042 + difference 2 3) sourceC1042) = raw17083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1042 sourceB1042 sourceC1042 difference raw17083; decide +kernel
    rw [ha]
    exact (canonical17083 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1042 + difference 4 2) (sourceB1042 + difference 2 4) sourceC1042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4022) := by
    have ha : (tripleCharges (sourceA1042 + difference 4 2) (sourceB1042 + difference 2 4) sourceC1042) = raw17084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1042 sourceB1042 sourceC1042 difference raw17084; decide +kernel
    rw [ha]
    exact (canonical17084 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1042 + difference 5 2) (sourceB1042 + difference 2 5) sourceC1042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3722) := by
    have ha : (tripleCharges (sourceA1042 + difference 5 2) (sourceB1042 + difference 2 5) sourceC1042) = raw17085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1042 sourceB1042 sourceC1042 difference raw17085; decide +kernel
    rw [ha]
    exact (canonical17085 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1042 + sourceB1042) sourceC1042) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1042 + sourceB1042) sourceC1042) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA1042 sourceB1042 sourceC1042 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1042 sourceB1042 sourceC1042
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1042, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1043 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1043 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC1043 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceForm1043 : Integer.Sparse Master := [(Sum.inr 5073, 1), (Sum.inr 5075, 1), (Sum.inr 5081, 1), (Sum.inr 5102, 1), (Sum.inr 5137, 1), (Sum.inr 5141, 1), (Sum.inr 5169, 1), (Sum.inr 5259, 1), (Sum.inr 5293, 1), (Sum.inr 5352, 1), (Sum.inr 5356, 1), (Sum.inr 5368, 1), (Sum.inr 5434, 1), (Sum.inr 5460, 1), (Sum.inr 5465, 1), (Sum.inr 5469, 1), (Sum.inr 5473, 1), (Sum.inr 5476, 1), (Sum.inr 5477, 1), (Sum.inr 5482, 2), (Sum.inr 5483, 2), (Sum.inr 5485, 1), (Sum.inr 5486, 1), (Sum.inr 5487, 1), (Sum.inr 5490, 1), (Sum.inr 5491, 1), (Sum.inr 5493, 1), (Sum.inr 5499, 1)]

theorem sourceEq1043 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1043 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1043 + difference 0 1) (sourceB1043 + difference 1 0) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1043 + difference 0 1) (sourceB1043 + difference 1 0) sourceC1043) = raw17086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17086; decide +kernel
    rw [ha]
    exact (canonical17086 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1043 + difference 0 2) (sourceB1043 + difference 2 0) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1043 + difference 0 2) (sourceB1043 + difference 2 0) sourceC1043) = raw17087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17087; decide +kernel
    rw [ha]
    exact (canonical17087 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1043 + difference 0 3) (sourceB1043 + difference 3 0) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1043 + difference 0 3) (sourceB1043 + difference 3 0) sourceC1043) = raw17088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17088; decide +kernel
    rw [ha]
    exact (canonical17088 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1043 + difference 0 4) (sourceB1043 + difference 4 0) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA1043 + difference 0 4) (sourceB1043 + difference 4 0) sourceC1043) = raw17089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17089; decide +kernel
    rw [ha]
    exact (canonical17089 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1043 + difference 0 5) (sourceB1043 + difference 5 0) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA1043 + difference 0 5) (sourceB1043 + difference 5 0) sourceC1043) = raw3119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw3119; decide +kernel
    rw [ha]
    exact (canonical3119 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1043 + difference 1 0) (sourceB1043 + difference 0 1) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA1043 + difference 1 0) (sourceB1043 + difference 0 1) sourceC1043) = raw3144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw3144; decide +kernel
    rw [ha]
    exact (canonical3144 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1043 + difference 1 2) (sourceB1043 + difference 2 1) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1043 + difference 1 2) (sourceB1043 + difference 2 1) sourceC1043) = raw3146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw3146; decide +kernel
    rw [ha]
    exact (canonical3146 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1043 + difference 1 3) (sourceB1043 + difference 3 1) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1043 + difference 1 3) (sourceB1043 + difference 3 1) sourceC1043) = raw3147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw3147; decide +kernel
    rw [ha]
    exact (canonical3147 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1043 + difference 1 4) (sourceB1043 + difference 4 1) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1043 + difference 1 4) (sourceB1043 + difference 4 1) sourceC1043) = raw3148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw3148; decide +kernel
    rw [ha]
    exact (canonical3148 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1043 + difference 1 5) (sourceB1043 + difference 5 1) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1043 + difference 1 5) (sourceB1043 + difference 5 1) sourceC1043) = raw9847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw9847; decide +kernel
    rw [ha]
    exact (canonical9847 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1043 + difference 2 0) (sourceB1043 + difference 0 2) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA1043 + difference 2 0) (sourceB1043 + difference 0 2) sourceC1043) = raw9853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw9853; decide +kernel
    rw [ha]
    exact (canonical9853 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1043 + difference 2 1) (sourceB1043 + difference 1 2) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA1043 + difference 2 1) (sourceB1043 + difference 1 2) sourceC1043) = raw17090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17090; decide +kernel
    rw [ha]
    exact (canonical17090 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1043 + difference 2 3) (sourceB1043 + difference 3 2) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1043 + difference 2 3) (sourceB1043 + difference 3 2) sourceC1043) = raw17091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17091; decide +kernel
    rw [ha]
    exact (canonical17091 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1043 + difference 2 4) (sourceB1043 + difference 4 2) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1043 + difference 2 4) (sourceB1043 + difference 4 2) sourceC1043) = raw17092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17092; decide +kernel
    rw [ha]
    exact (canonical17092 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1043 + difference 2 5) (sourceB1043 + difference 5 2) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1043 + difference 2 5) (sourceB1043 + difference 5 2) sourceC1043) = raw3130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw3130; decide +kernel
    rw [ha]
    exact (canonical3130 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1043 + difference 3 0) (sourceB1043 + difference 0 3) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1043 + difference 3 0) (sourceB1043 + difference 0 3) sourceC1043) = raw9857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw9857; decide +kernel
    rw [ha]
    exact (canonical9857 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1043 + difference 3 1) (sourceB1043 + difference 1 3) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA1043 + difference 3 1) (sourceB1043 + difference 1 3) sourceC1043) = raw17093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17093; decide +kernel
    rw [ha]
    exact (canonical17093 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1043 + difference 3 2) (sourceB1043 + difference 2 3) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5476) := by
    have ha : (tripleCharges (sourceA1043 + difference 3 2) (sourceB1043 + difference 2 3) sourceC1043) = raw17094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17094; decide +kernel
    rw [ha]
    exact (canonical17094 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1043 + difference 3 4) (sourceB1043 + difference 4 3) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA1043 + difference 3 4) (sourceB1043 + difference 4 3) sourceC1043) = raw17095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17095; decide +kernel
    rw [ha]
    exact (canonical17095 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1043 + difference 3 5) (sourceB1043 + difference 5 3) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1043 + difference 3 5) (sourceB1043 + difference 5 3) sourceC1043) = raw3135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw3135; decide +kernel
    rw [ha]
    exact (canonical3135 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1043 + difference 4 0) (sourceB1043 + difference 0 4) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA1043 + difference 4 0) (sourceB1043 + difference 0 4) sourceC1043) = raw9861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw9861; decide +kernel
    rw [ha]
    exact (canonical9861 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1043 + difference 4 1) (sourceB1043 + difference 1 4) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA1043 + difference 4 1) (sourceB1043 + difference 1 4) sourceC1043) = raw17096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17096; decide +kernel
    rw [ha]
    exact (canonical17096 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1043 + difference 4 2) (sourceB1043 + difference 2 4) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1043 + difference 4 2) (sourceB1043 + difference 2 4) sourceC1043) = raw17097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17097; decide +kernel
    rw [ha]
    exact (canonical17097 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1043 + difference 4 3) (sourceB1043 + difference 3 4) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1043 + difference 4 3) (sourceB1043 + difference 3 4) sourceC1043) = raw17098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17098; decide +kernel
    rw [ha]
    exact (canonical17098 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1043 + difference 4 5) (sourceB1043 + difference 5 4) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1043 + difference 4 5) (sourceB1043 + difference 5 4) sourceC1043) = raw3140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw3140; decide +kernel
    rw [ha]
    exact (canonical3140 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1043 + difference 5 0) (sourceB1043 + difference 0 5) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1043 + difference 5 0) (sourceB1043 + difference 0 5) sourceC1043) = raw9865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw9865; decide +kernel
    rw [ha]
    exact (canonical9865 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1043 + difference 5 1) (sourceB1043 + difference 1 5) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA1043 + difference 5 1) (sourceB1043 + difference 1 5) sourceC1043) = raw17099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17099; decide +kernel
    rw [ha]
    exact (canonical17099 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1043 + difference 5 2) (sourceB1043 + difference 2 5) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1043 + difference 5 2) (sourceB1043 + difference 2 5) sourceC1043) = raw17100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17100; decide +kernel
    rw [ha]
    exact (canonical17100 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1043 + difference 5 3) (sourceB1043 + difference 3 5) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA1043 + difference 5 3) (sourceB1043 + difference 3 5) sourceC1043) = raw17101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17101; decide +kernel
    rw [ha]
    exact (canonical17101 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1043 + difference 5 4) (sourceB1043 + difference 4 5) sourceC1043) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1043 + difference 5 4) (sourceB1043 + difference 4 5) sourceC1043) = raw17102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1043 sourceB1043 sourceC1043 difference raw17102; decide +kernel
    rw [ha]
    exact (canonical17102 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1043 sourceB1043 sourceC1043
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1043, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1044 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1044 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC1044 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceForm1044 : Integer.Sparse Master := [(Sum.inr 2480, 1), (Sum.inr 2482, 1), (Sum.inr 2489, 1), (Sum.inr 2512, 1), (Sum.inr 2556, 1), (Sum.inr 2561, 1), (Sum.inr 2595, 1), (Sum.inr 2723, 1), (Sum.inr 2767, 1), (Sum.inr 3690, 1), (Sum.inr 3694, 1), (Sum.inr 3705, 1), (Sum.inr 3852, 1), (Sum.inr 3921, 1), (Sum.inr 3931, 1), (Sum.inr 3945, 1), (Sum.inr 3958, 1), (Sum.inr 3965, 1), (Sum.inr 3971, 1), (Sum.inr 3980, 1), (Sum.inr 3981, 2), (Sum.inr 3984, 1), (Sum.inr 3992, 1), (Sum.inr 3999, 1), (Sum.inr 4000, 1), (Sum.inr 4013, 1), (Sum.inr 4014, 1), (Sum.inr 4018, 1), (Sum.inr 4054, 1)]

theorem sourceEq1044 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1044 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1044 + difference 0 1) (sourceB1044 + difference 1 0) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1044 + difference 0 1) (sourceB1044 + difference 1 0) sourceC1044) = raw17103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17103; decide +kernel
    rw [ha]
    exact (canonical17103 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1044 + difference 0 2) (sourceB1044 + difference 2 0) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA1044 + difference 0 2) (sourceB1044 + difference 2 0) sourceC1044) = raw17104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17104; decide +kernel
    rw [ha]
    exact (canonical17104 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1044 + difference 0 3) (sourceB1044 + difference 3 0) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA1044 + difference 0 3) (sourceB1044 + difference 3 0) sourceC1044) = raw17105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17105; decide +kernel
    rw [ha]
    exact (canonical17105 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1044 + difference 0 4) (sourceB1044 + difference 4 0) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4018) := by
    have ha : (tripleCharges (sourceA1044 + difference 0 4) (sourceB1044 + difference 4 0) sourceC1044) = raw17106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17106; decide +kernel
    rw [ha]
    exact (canonical17106 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1044 + difference 0 5) (sourceB1044 + difference 5 0) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4054) := by
    have ha : (tripleCharges (sourceA1044 + difference 0 5) (sourceB1044 + difference 5 0) sourceC1044) = raw3149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw3149; decide +kernel
    rw [ha]
    exact (canonical3149 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1044 + difference 1 0) (sourceB1044 + difference 0 1) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA1044 + difference 1 0) (sourceB1044 + difference 0 1) sourceC1044) = raw3174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw3174; decide +kernel
    rw [ha]
    exact (canonical3174 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1044 + difference 1 2) (sourceB1044 + difference 2 1) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3971) := by
    have ha : (tripleCharges (sourceA1044 + difference 1 2) (sourceB1044 + difference 2 1) sourceC1044) = raw3176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw3176; decide +kernel
    rw [ha]
    exact (canonical3176 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1044 + difference 1 3) (sourceB1044 + difference 3 1) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1044 + difference 1 3) (sourceB1044 + difference 3 1) sourceC1044) = raw3177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw3177; decide +kernel
    rw [ha]
    exact (canonical3177 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1044 + difference 1 4) (sourceB1044 + difference 4 1) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4014) := by
    have ha : (tripleCharges (sourceA1044 + difference 1 4) (sourceB1044 + difference 4 1) sourceC1044) = raw3178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw3178; decide +kernel
    rw [ha]
    exact (canonical3178 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1044 + difference 1 5) (sourceB1044 + difference 5 1) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA1044 + difference 1 5) (sourceB1044 + difference 5 1) sourceC1044) = raw9869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw9869; decide +kernel
    rw [ha]
    exact (canonical9869 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1044 + difference 2 0) (sourceB1044 + difference 0 2) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA1044 + difference 2 0) (sourceB1044 + difference 0 2) sourceC1044) = raw9875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw9875; decide +kernel
    rw [ha]
    exact (canonical9875 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1044 + difference 2 1) (sourceB1044 + difference 1 2) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3921) := by
    have ha : (tripleCharges (sourceA1044 + difference 2 1) (sourceB1044 + difference 1 2) sourceC1044) = raw17107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17107; decide +kernel
    rw [ha]
    exact (canonical17107 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1044 + difference 2 3) (sourceB1044 + difference 3 2) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3945) := by
    have ha : (tripleCharges (sourceA1044 + difference 2 3) (sourceB1044 + difference 3 2) sourceC1044) = raw17108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17108; decide +kernel
    rw [ha]
    exact (canonical17108 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1044 + difference 2 4) (sourceB1044 + difference 4 2) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1044 + difference 2 4) (sourceB1044 + difference 4 2) sourceC1044) = raw17109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17109; decide +kernel
    rw [ha]
    exact (canonical17109 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1044 + difference 2 5) (sourceB1044 + difference 5 2) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3992) := by
    have ha : (tripleCharges (sourceA1044 + difference 2 5) (sourceB1044 + difference 5 2) sourceC1044) = raw3160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw3160; decide +kernel
    rw [ha]
    exact (canonical3160 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1044 + difference 3 0) (sourceB1044 + difference 0 3) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA1044 + difference 3 0) (sourceB1044 + difference 0 3) sourceC1044) = raw9879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw9879; decide +kernel
    rw [ha]
    exact (canonical9879 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1044 + difference 3 1) (sourceB1044 + difference 1 3) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA1044 + difference 3 1) (sourceB1044 + difference 1 3) sourceC1044) = raw17110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17110; decide +kernel
    rw [ha]
    exact (canonical17110 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1044 + difference 3 2) (sourceB1044 + difference 2 3) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3965) := by
    have ha : (tripleCharges (sourceA1044 + difference 3 2) (sourceB1044 + difference 2 3) sourceC1044) = raw17111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17111; decide +kernel
    rw [ha]
    exact (canonical17111 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1044 + difference 3 4) (sourceB1044 + difference 4 3) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4000) := by
    have ha : (tripleCharges (sourceA1044 + difference 3 4) (sourceB1044 + difference 4 3) sourceC1044) = raw17112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17112; decide +kernel
    rw [ha]
    exact (canonical17112 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1044 + difference 3 5) (sourceB1044 + difference 5 3) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3999) := by
    have ha : (tripleCharges (sourceA1044 + difference 3 5) (sourceB1044 + difference 5 3) sourceC1044) = raw3165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw3165; decide +kernel
    rw [ha]
    exact (canonical3165 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1044 + difference 4 0) (sourceB1044 + difference 0 4) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA1044 + difference 4 0) (sourceB1044 + difference 0 4) sourceC1044) = raw9883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw9883; decide +kernel
    rw [ha]
    exact (canonical9883 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1044 + difference 4 1) (sourceB1044 + difference 1 4) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA1044 + difference 4 1) (sourceB1044 + difference 1 4) sourceC1044) = raw17113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17113; decide +kernel
    rw [ha]
    exact (canonical17113 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1044 + difference 4 2) (sourceB1044 + difference 2 4) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA1044 + difference 4 2) (sourceB1044 + difference 2 4) sourceC1044) = raw17114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17114; decide +kernel
    rw [ha]
    exact (canonical17114 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1044 + difference 4 3) (sourceB1044 + difference 3 4) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3705) := by
    have ha : (tripleCharges (sourceA1044 + difference 4 3) (sourceB1044 + difference 3 4) sourceC1044) = raw17115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17115; decide +kernel
    rw [ha]
    exact (canonical17115 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1044 + difference 4 5) (sourceB1044 + difference 5 4) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1044 + difference 4 5) (sourceB1044 + difference 5 4) sourceC1044) = raw3170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw3170; decide +kernel
    rw [ha]
    exact (canonical3170 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1044 + difference 5 0) (sourceB1044 + difference 0 5) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1044 + difference 5 0) (sourceB1044 + difference 0 5) sourceC1044) = raw9887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw9887; decide +kernel
    rw [ha]
    exact (canonical9887 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1044 + difference 5 1) (sourceB1044 + difference 1 5) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA1044 + difference 5 1) (sourceB1044 + difference 1 5) sourceC1044) = raw17116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17116; decide +kernel
    rw [ha]
    exact (canonical17116 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1044 + difference 5 2) (sourceB1044 + difference 2 5) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA1044 + difference 5 2) (sourceB1044 + difference 2 5) sourceC1044) = raw17117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17117; decide +kernel
    rw [ha]
    exact (canonical17117 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1044 + difference 5 3) (sourceB1044 + difference 3 5) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA1044 + difference 5 3) (sourceB1044 + difference 3 5) sourceC1044) = raw17118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17118; decide +kernel
    rw [ha]
    exact (canonical17118 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1044 + difference 5 4) (sourceB1044 + difference 4 5) sourceC1044) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA1044 + difference 5 4) (sourceB1044 + difference 4 5) sourceC1044) = raw17119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1044 sourceB1044 sourceC1044 difference raw17119; decide +kernel
    rw [ha]
    exact (canonical17119 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1044 sourceB1044 sourceC1044
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1044, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1045 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB1045 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1045 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1045 : Integer.Sparse Master := [(Sum.inr 5405, 2), (Sum.inr 5409, 2), (Sum.inr 5410, 2), (Sum.inr 5411, 2), (Sum.inr 5424, 2), (Sum.inr 5428, 2), (Sum.inr 5434, 2), (Sum.inr 5438, 2), (Sum.inr 5442, 2), (Sum.inr 5445, 1), (Sum.inr 5446, 2), (Sum.inr 5471, 2), (Sum.inr 5473, 2), (Sum.inr 5477, 2), (Sum.inr 5483, 1), (Sum.inr 5487, 2)]

theorem sourceEq1045 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1045 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1045 + difference 0 1) (sourceB1045 + difference 1 0) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1045 + difference 0 1) (sourceB1045 + difference 1 0) sourceC1045) = raw16839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw16839; decide +kernel
    rw [ha]
    exact (canonical16839 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1045 + difference 0 2) (sourceB1045 + difference 2 0) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1045 + difference 0 2) (sourceB1045 + difference 2 0) sourceC1045) = raw17031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw17031; decide +kernel
    rw [ha]
    exact (canonical17031 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1045 + difference 0 3) (sourceB1045 + difference 3 0) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1045 + difference 0 3) (sourceB1045 + difference 3 0) sourceC1045) = raw17120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw17120; decide +kernel
    rw [ha]
    exact (canonical17120 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1045 + difference 0 4) (sourceB1045 + difference 4 0) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1045 + difference 0 4) (sourceB1045 + difference 4 0) sourceC1045) = raw17121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw17121; decide +kernel
    rw [ha]
    exact (canonical17121 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1045 + difference 0 5) (sourceB1045 + difference 5 0) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1045 + difference 0 5) (sourceB1045 + difference 5 0) sourceC1045) = raw17122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw17122; decide +kernel
    rw [ha]
    exact (canonical17122 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1045 + difference 1 0) (sourceB1045 + difference 0 1) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1045 + difference 1 0) (sourceB1045 + difference 0 1) sourceC1045) = raw15210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw15210; decide +kernel
    rw [ha]
    exact (canonical15210 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1045 + difference 1 2) (sourceB1045 + difference 2 1) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1045 + difference 1 2) (sourceB1045 + difference 2 1) sourceC1045) = raw15114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw15114; decide +kernel
    rw [ha]
    exact (canonical15114 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1045 + difference 1 3) (sourceB1045 + difference 3 1) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA1045 + difference 1 3) (sourceB1045 + difference 3 1) sourceC1045) = raw15115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw15115; decide +kernel
    rw [ha]
    exact (canonical15115 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1045 + difference 1 4) (sourceB1045 + difference 4 1) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1045 + difference 1 4) (sourceB1045 + difference 4 1) sourceC1045) = raw15116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw15116; decide +kernel
    rw [ha]
    exact (canonical15116 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1045 + difference 1 5) (sourceB1045 + difference 5 1) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1045 + difference 1 5) (sourceB1045 + difference 5 1) sourceC1045) = raw15117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw15117; decide +kernel
    rw [ha]
    exact (canonical15117 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1045 + difference 2 0) (sourceB1045 + difference 0 2) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1045 + difference 2 0) (sourceB1045 + difference 0 2) sourceC1045) = raw15124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw15124; decide +kernel
    rw [ha]
    exact (canonical15124 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1045 + difference 2 1) (sourceB1045 + difference 1 2) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1045 + difference 2 1) (sourceB1045 + difference 1 2) sourceC1045) = raw17123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw17123; decide +kernel
    rw [ha]
    exact (canonical17123 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1045 + difference 2 3) (sourceB1045 + difference 3 2) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1045 + difference 2 3) (sourceB1045 + difference 3 2) sourceC1045) = raw16843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw16843; decide +kernel
    rw [ha]
    exact (canonical16843 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1045 + difference 2 4) (sourceB1045 + difference 4 2) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1045 + difference 2 4) (sourceB1045 + difference 4 2) sourceC1045) = raw15664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw15664; decide +kernel
    rw [ha]
    exact (canonical15664 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1045 + difference 2 5) (sourceB1045 + difference 5 2) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1045 + difference 2 5) (sourceB1045 + difference 5 2) sourceC1045) = raw15858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw15858; decide +kernel
    rw [ha]
    exact (canonical15858 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1045 + difference 3 0) (sourceB1045 + difference 0 3) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1045 + difference 3 0) (sourceB1045 + difference 0 3) sourceC1045) = raw15129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw15129; decide +kernel
    rw [ha]
    exact (canonical15129 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1045 + difference 3 1) (sourceB1045 + difference 1 3) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1045 + difference 3 1) (sourceB1045 + difference 1 3) sourceC1045) = raw16851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw16851; decide +kernel
    rw [ha]
    exact (canonical16851 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1045 + difference 3 2) (sourceB1045 + difference 2 3) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1045 + difference 3 2) (sourceB1045 + difference 2 3) sourceC1045) = raw17124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw17124; decide +kernel
    rw [ha]
    exact (canonical17124 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1045 + difference 3 4) (sourceB1045 + difference 4 3) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1045 + difference 3 4) (sourceB1045 + difference 4 3) sourceC1045) = raw17037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw17037; decide +kernel
    rw [ha]
    exact (canonical17037 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1045 + difference 3 5) (sourceB1045 + difference 5 3) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1045 + difference 3 5) (sourceB1045 + difference 5 3) sourceC1045) = raw17038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw17038; decide +kernel
    rw [ha]
    exact (canonical17038 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1045 + difference 4 0) (sourceB1045 + difference 0 4) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1045 + difference 4 0) (sourceB1045 + difference 0 4) sourceC1045) = raw15134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw15134; decide +kernel
    rw [ha]
    exact (canonical15134 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1045 + difference 4 1) (sourceB1045 + difference 1 4) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1045 + difference 4 1) (sourceB1045 + difference 1 4) sourceC1045) = raw16856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw16856; decide +kernel
    rw [ha]
    exact (canonical16856 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1045 + difference 4 2) (sourceB1045 + difference 2 4) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1045 + difference 4 2) (sourceB1045 + difference 2 4) sourceC1045) = raw17047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw17047; decide +kernel
    rw [ha]
    exact (canonical17047 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1045 + difference 4 3) (sourceB1045 + difference 3 4) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA1045 + difference 4 3) (sourceB1045 + difference 3 4) sourceC1045) = raw17125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw17125; decide +kernel
    rw [ha]
    exact (canonical17125 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1045 + difference 4 5) (sourceB1045 + difference 5 4) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1045 + difference 4 5) (sourceB1045 + difference 5 4) sourceC1045) = raw15200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw15200; decide +kernel
    rw [ha]
    exact (canonical15200 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1045 + difference 5 0) (sourceB1045 + difference 0 5) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1045 + difference 5 0) (sourceB1045 + difference 0 5) sourceC1045) = raw15136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw15136; decide +kernel
    rw [ha]
    exact (canonical15136 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1045 + difference 5 1) (sourceB1045 + difference 1 5) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1045 + difference 5 1) (sourceB1045 + difference 1 5) sourceC1045) = raw16861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw16861; decide +kernel
    rw [ha]
    exact (canonical16861 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1045 + difference 5 2) (sourceB1045 + difference 2 5) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1045 + difference 5 2) (sourceB1045 + difference 2 5) sourceC1045) = raw17052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw17052; decide +kernel
    rw [ha]
    exact (canonical17052 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1045 + difference 5 3) (sourceB1045 + difference 3 5) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1045 + difference 5 3) (sourceB1045 + difference 3 5) sourceC1045) = raw17126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw17126; decide +kernel
    rw [ha]
    exact (canonical17126 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1045 + difference 5 4) (sourceB1045 + difference 4 5) sourceC1045) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1045 + difference 5 4) (sourceB1045 + difference 4 5) sourceC1045) = raw17127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1045 sourceB1045 sourceC1045 difference raw17127; decide +kernel
    rw [ha]
    exact (canonical17127 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1045 sourceB1045 sourceC1045
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1045, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1046 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1046 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC1046 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceForm1046 : Integer.Sparse Master := [(Sum.inr 4728, 1), (Sum.inr 4732, 1), (Sum.inr 4737, 2), (Sum.inr 4888, 1), (Sum.inr 5126, 1), (Sum.inr 5134, 2), (Sum.inr 5241, 1), (Sum.inr 5321, 1), (Sum.inr 5324, 2), (Sum.inr 5393, 2), (Sum.inr 5395, 4), (Sum.inr 5405, 4), (Sum.inr 5434, 2), (Sum.inr 5439, 1), (Sum.inr 5452, 1), (Sum.inr 5482, 2), (Sum.inr 5489, 1), (Sum.inr 5498, 1)]

theorem sourceEq1046 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1046 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1046 + difference 0 1) (sourceB1046 + difference 1 0) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1046 + difference 0 1) (sourceB1046 + difference 1 0) sourceC1046) = raw3367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw3367; decide +kernel
    rw [ha]
    exact (canonical3367 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1046 + difference 0 2) (sourceB1046 + difference 2 0) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1046 + difference 0 2) (sourceB1046 + difference 2 0) sourceC1046) = raw3368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw3368; decide +kernel
    rw [ha]
    exact (canonical3368 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1046 + difference 0 3) (sourceB1046 + difference 3 0) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1046 + difference 0 3) (sourceB1046 + difference 3 0) sourceC1046) = raw3369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw3369; decide +kernel
    rw [ha]
    exact (canonical3369 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1046 + difference 0 4) (sourceB1046 + difference 4 0) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA1046 + difference 0 4) (sourceB1046 + difference 4 0) sourceC1046) = raw3370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw3370; decide +kernel
    rw [ha]
    exact (canonical3370 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1046 + difference 0 5) (sourceB1046 + difference 5 0) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5498) := by
    have ha : (tripleCharges (sourceA1046 + difference 0 5) (sourceB1046 + difference 5 0) sourceC1046) = raw2625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw2625; decide +kernel
    rw [ha]
    exact (canonical2625 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1046 + difference 1 0) (sourceB1046 + difference 0 1) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA1046 + difference 1 0) (sourceB1046 + difference 0 1) sourceC1046) = raw17128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17128; decide +kernel
    rw [ha]
    exact (canonical17128 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1046 + difference 1 2) (sourceB1046 + difference 2 1) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1046 + difference 1 2) (sourceB1046 + difference 2 1) sourceC1046) = raw17129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17129; decide +kernel
    rw [ha]
    exact (canonical17129 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1046 + difference 1 3) (sourceB1046 + difference 3 1) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1046 + difference 1 3) (sourceB1046 + difference 3 1) sourceC1046) = raw17130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17130; decide +kernel
    rw [ha]
    exact (canonical17130 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1046 + difference 1 4) (sourceB1046 + difference 4 1) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1046 + difference 1 4) (sourceB1046 + difference 4 1) sourceC1046) = raw17131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17131; decide +kernel
    rw [ha]
    exact (canonical17131 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1046 + difference 1 5) (sourceB1046 + difference 5 1) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1046 + difference 1 5) (sourceB1046 + difference 5 1) sourceC1046) = raw3346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw3346; decide +kernel
    rw [ha]
    exact (canonical3346 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1046 + difference 2 0) (sourceB1046 + difference 0 2) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA1046 + difference 2 0) (sourceB1046 + difference 0 2) sourceC1046) = raw17132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17132; decide +kernel
    rw [ha]
    exact (canonical17132 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1046 + difference 2 1) (sourceB1046 + difference 1 2) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA1046 + difference 2 1) (sourceB1046 + difference 1 2) sourceC1046) = raw17133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17133; decide +kernel
    rw [ha]
    exact (canonical17133 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1046 + difference 2 3) (sourceB1046 + difference 3 2) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1046 + difference 2 3) (sourceB1046 + difference 3 2) sourceC1046) = raw17134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17134; decide +kernel
    rw [ha]
    exact (canonical17134 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1046 + difference 2 4) (sourceB1046 + difference 4 2) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1046 + difference 2 4) (sourceB1046 + difference 4 2) sourceC1046) = raw17135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17135; decide +kernel
    rw [ha]
    exact (canonical17135 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1046 + difference 2 5) (sourceB1046 + difference 5 2) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1046 + difference 2 5) (sourceB1046 + difference 5 2) sourceC1046) = raw3351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw3351; decide +kernel
    rw [ha]
    exact (canonical3351 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1046 + difference 3 0) (sourceB1046 + difference 0 3) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA1046 + difference 3 0) (sourceB1046 + difference 0 3) sourceC1046) = raw17136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17136; decide +kernel
    rw [ha]
    exact (canonical17136 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1046 + difference 3 1) (sourceB1046 + difference 1 3) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA1046 + difference 3 1) (sourceB1046 + difference 1 3) sourceC1046) = raw17137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17137; decide +kernel
    rw [ha]
    exact (canonical17137 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1046 + difference 3 2) (sourceB1046 + difference 2 3) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1046 + difference 3 2) (sourceB1046 + difference 2 3) sourceC1046) = raw17138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17138; decide +kernel
    rw [ha]
    exact (canonical17138 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1046 + difference 3 4) (sourceB1046 + difference 4 3) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1046 + difference 3 4) (sourceB1046 + difference 4 3) sourceC1046) = raw17139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17139; decide +kernel
    rw [ha]
    exact (canonical17139 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1046 + difference 3 5) (sourceB1046 + difference 5 3) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1046 + difference 3 5) (sourceB1046 + difference 5 3) sourceC1046) = raw3356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw3356; decide +kernel
    rw [ha]
    exact (canonical3356 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1046 + difference 4 0) (sourceB1046 + difference 0 4) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5126) := by
    have ha : (tripleCharges (sourceA1046 + difference 4 0) (sourceB1046 + difference 0 4) sourceC1046) = raw17140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17140; decide +kernel
    rw [ha]
    exact (canonical17140 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1046 + difference 4 1) (sourceB1046 + difference 1 4) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5321) := by
    have ha : (tripleCharges (sourceA1046 + difference 4 1) (sourceB1046 + difference 1 4) sourceC1046) = raw17141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17141; decide +kernel
    rw [ha]
    exact (canonical17141 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1046 + difference 4 2) (sourceB1046 + difference 2 4) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5324) := by
    have ha : (tripleCharges (sourceA1046 + difference 4 2) (sourceB1046 + difference 2 4) sourceC1046) = raw17142 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17142; decide +kernel
    rw [ha]
    exact (canonical17142 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1046 + difference 4 3) (sourceB1046 + difference 3 4) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5324) := by
    have ha : (tripleCharges (sourceA1046 + difference 4 3) (sourceB1046 + difference 3 4) sourceC1046) = raw17143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17143; decide +kernel
    rw [ha]
    exact (canonical17143 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1046 + difference 4 5) (sourceB1046 + difference 5 4) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1046 + difference 4 5) (sourceB1046 + difference 5 4) sourceC1046) = raw3361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw3361; decide +kernel
    rw [ha]
    exact (canonical3361 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1046 + difference 5 0) (sourceB1046 + difference 0 5) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4728) := by
    have ha : (tripleCharges (sourceA1046 + difference 5 0) (sourceB1046 + difference 0 5) sourceC1046) = raw17144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17144; decide +kernel
    rw [ha]
    exact (canonical17144 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1046 + difference 5 1) (sourceB1046 + difference 1 5) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4732) := by
    have ha : (tripleCharges (sourceA1046 + difference 5 1) (sourceB1046 + difference 1 5) sourceC1046) = raw17145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17145; decide +kernel
    rw [ha]
    exact (canonical17145 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1046 + difference 5 2) (sourceB1046 + difference 2 5) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA1046 + difference 5 2) (sourceB1046 + difference 2 5) sourceC1046) = raw17146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17146; decide +kernel
    rw [ha]
    exact (canonical17146 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1046 + difference 5 3) (sourceB1046 + difference 3 5) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA1046 + difference 5 3) (sourceB1046 + difference 3 5) sourceC1046) = raw17147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17147; decide +kernel
    rw [ha]
    exact (canonical17147 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1046 + difference 5 4) (sourceB1046 + difference 4 5) sourceC1046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA1046 + difference 5 4) (sourceB1046 + difference 4 5) sourceC1046) = raw17148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1046 sourceB1046 sourceC1046 difference raw17148; decide +kernel
    rw [ha]
    exact (canonical17148 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1046 sourceB1046 sourceC1046
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1046, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1047 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1047 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC1047 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceForm1047 : Integer.Sparse Master := [(Sum.inr 1897, 1), (Sum.inr 1901, 1), (Sum.inr 1909, 2), (Sum.inr 2244, 1), (Sum.inr 2541, 1), (Sum.inr 2553, 2), (Sum.inr 2694, 1), (Sum.inr 3647, 1), (Sum.inr 3651, 2), (Sum.inr 3779, 2), (Sum.inr 3781, 2), (Sum.inr 3794, 2), (Sum.inr 3800, 2), (Sum.inr 3805, 2), (Sum.inr 3852, 2), (Sum.inr 3902, 1), (Sum.inr 3911, 1), (Sum.inr 3992, 2), (Sum.inr 4009, 1), (Sum.inr 4051, 1)]

theorem sourceEq1047 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1047 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1047 + difference 0 1) (sourceB1047 + difference 1 0) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA1047 + difference 0 1) (sourceB1047 + difference 1 0) sourceC1047) = raw17149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17149; decide +kernel
    rw [ha]
    exact (canonical17149 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1047 + difference 0 2) (sourceB1047 + difference 2 0) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA1047 + difference 0 2) (sourceB1047 + difference 2 0) sourceC1047) = raw17150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17150; decide +kernel
    rw [ha]
    exact (canonical17150 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1047 + difference 0 3) (sourceB1047 + difference 3 0) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA1047 + difference 0 3) (sourceB1047 + difference 3 0) sourceC1047) = raw17151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17151; decide +kernel
    rw [ha]
    exact (canonical17151 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1047 + difference 0 4) (sourceB1047 + difference 4 0) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3911) := by
    have ha : (tripleCharges (sourceA1047 + difference 0 4) (sourceB1047 + difference 4 0) sourceC1047) = raw17152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17152; decide +kernel
    rw [ha]
    exact (canonical17152 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1047 + difference 0 5) (sourceB1047 + difference 5 0) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4051) := by
    have ha : (tripleCharges (sourceA1047 + difference 0 5) (sourceB1047 + difference 5 0) sourceC1047) = raw17153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17153; decide +kernel
    rw [ha]
    exact (canonical17153 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1047 + difference 1 0) (sourceB1047 + difference 0 1) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA1047 + difference 1 0) (sourceB1047 + difference 0 1) sourceC1047) = raw17154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17154; decide +kernel
    rw [ha]
    exact (canonical17154 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1047 + difference 1 2) (sourceB1047 + difference 2 1) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA1047 + difference 1 2) (sourceB1047 + difference 2 1) sourceC1047) = raw17155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17155; decide +kernel
    rw [ha]
    exact (canonical17155 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1047 + difference 1 3) (sourceB1047 + difference 3 1) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA1047 + difference 1 3) (sourceB1047 + difference 3 1) sourceC1047) = raw17156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17156; decide +kernel
    rw [ha]
    exact (canonical17156 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1047 + difference 1 4) (sourceB1047 + difference 4 1) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA1047 + difference 1 4) (sourceB1047 + difference 4 1) sourceC1047) = raw17157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17157; decide +kernel
    rw [ha]
    exact (canonical17157 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1047 + difference 1 5) (sourceB1047 + difference 5 1) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4009) := by
    have ha : (tripleCharges (sourceA1047 + difference 1 5) (sourceB1047 + difference 5 1) sourceC1047) = raw17158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17158; decide +kernel
    rw [ha]
    exact (canonical17158 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1047 + difference 2 0) (sourceB1047 + difference 0 2) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA1047 + difference 2 0) (sourceB1047 + difference 0 2) sourceC1047) = raw17159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17159; decide +kernel
    rw [ha]
    exact (canonical17159 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1047 + difference 2 1) (sourceB1047 + difference 1 2) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3779) := by
    have ha : (tripleCharges (sourceA1047 + difference 2 1) (sourceB1047 + difference 1 2) sourceC1047) = raw17160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17160; decide +kernel
    rw [ha]
    exact (canonical17160 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1047 + difference 2 3) (sourceB1047 + difference 3 2) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3781) := by
    have ha : (tripleCharges (sourceA1047 + difference 2 3) (sourceB1047 + difference 3 2) sourceC1047) = raw17161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17161; decide +kernel
    rw [ha]
    exact (canonical17161 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1047 + difference 2 4) (sourceB1047 + difference 4 2) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1047 + difference 2 4) (sourceB1047 + difference 4 2) sourceC1047) = raw17162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17162; decide +kernel
    rw [ha]
    exact (canonical17162 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1047 + difference 2 5) (sourceB1047 + difference 5 2) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3992) := by
    have ha : (tripleCharges (sourceA1047 + difference 2 5) (sourceB1047 + difference 5 2) sourceC1047) = raw17163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17163; decide +kernel
    rw [ha]
    exact (canonical17163 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1047 + difference 3 0) (sourceB1047 + difference 0 3) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA1047 + difference 3 0) (sourceB1047 + difference 0 3) sourceC1047) = raw17164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17164; decide +kernel
    rw [ha]
    exact (canonical17164 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1047 + difference 3 1) (sourceB1047 + difference 1 3) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3779) := by
    have ha : (tripleCharges (sourceA1047 + difference 3 1) (sourceB1047 + difference 1 3) sourceC1047) = raw17165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17165; decide +kernel
    rw [ha]
    exact (canonical17165 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1047 + difference 3 2) (sourceB1047 + difference 2 3) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3781) := by
    have ha : (tripleCharges (sourceA1047 + difference 3 2) (sourceB1047 + difference 2 3) sourceC1047) = raw17166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17166; decide +kernel
    rw [ha]
    exact (canonical17166 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1047 + difference 3 4) (sourceB1047 + difference 4 3) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1047 + difference 3 4) (sourceB1047 + difference 4 3) sourceC1047) = raw17167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17167; decide +kernel
    rw [ha]
    exact (canonical17167 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1047 + difference 3 5) (sourceB1047 + difference 5 3) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3992) := by
    have ha : (tripleCharges (sourceA1047 + difference 3 5) (sourceB1047 + difference 5 3) sourceC1047) = raw17168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17168; decide +kernel
    rw [ha]
    exact (canonical17168 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1047 + difference 4 0) (sourceB1047 + difference 0 4) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2541) := by
    have ha : (tripleCharges (sourceA1047 + difference 4 0) (sourceB1047 + difference 0 4) sourceC1047) = raw17169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17169; decide +kernel
    rw [ha]
    exact (canonical17169 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1047 + difference 4 1) (sourceB1047 + difference 1 4) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3647) := by
    have ha : (tripleCharges (sourceA1047 + difference 4 1) (sourceB1047 + difference 1 4) sourceC1047) = raw17170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17170; decide +kernel
    rw [ha]
    exact (canonical17170 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1047 + difference 4 2) (sourceB1047 + difference 2 4) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3651) := by
    have ha : (tripleCharges (sourceA1047 + difference 4 2) (sourceB1047 + difference 2 4) sourceC1047) = raw17171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17171; decide +kernel
    rw [ha]
    exact (canonical17171 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1047 + difference 4 3) (sourceB1047 + difference 3 4) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3651) := by
    have ha : (tripleCharges (sourceA1047 + difference 4 3) (sourceB1047 + difference 3 4) sourceC1047) = raw17172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17172; decide +kernel
    rw [ha]
    exact (canonical17172 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1047 + difference 4 5) (sourceB1047 + difference 5 4) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA1047 + difference 4 5) (sourceB1047 + difference 5 4) sourceC1047) = raw17173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17173; decide +kernel
    rw [ha]
    exact (canonical17173 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1047 + difference 5 0) (sourceB1047 + difference 0 5) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1897) := by
    have ha : (tripleCharges (sourceA1047 + difference 5 0) (sourceB1047 + difference 0 5) sourceC1047) = raw17174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17174; decide +kernel
    rw [ha]
    exact (canonical17174 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1047 + difference 5 1) (sourceB1047 + difference 1 5) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1901) := by
    have ha : (tripleCharges (sourceA1047 + difference 5 1) (sourceB1047 + difference 1 5) sourceC1047) = raw17175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17175; decide +kernel
    rw [ha]
    exact (canonical17175 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1047 + difference 5 2) (sourceB1047 + difference 2 5) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1909) := by
    have ha : (tripleCharges (sourceA1047 + difference 5 2) (sourceB1047 + difference 2 5) sourceC1047) = raw17176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17176; decide +kernel
    rw [ha]
    exact (canonical17176 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1047 + difference 5 3) (sourceB1047 + difference 3 5) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1909) := by
    have ha : (tripleCharges (sourceA1047 + difference 5 3) (sourceB1047 + difference 3 5) sourceC1047) = raw17177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17177; decide +kernel
    rw [ha]
    exact (canonical17177 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1047 + difference 5 4) (sourceB1047 + difference 4 5) sourceC1047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA1047 + difference 5 4) (sourceB1047 + difference 4 5) sourceC1047) = raw17178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1047 sourceB1047 sourceC1047 difference raw17178; decide +kernel
    rw [ha]
    exact (canonical17178 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1047 sourceB1047 sourceC1047
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1047, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1048 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1048 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC1048 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceForm1048 : Integer.Sparse Master := [(Sum.inr 5065, 1), (Sum.inr 5067, 2), (Sum.inr 5073, 2), (Sum.inr 5074, 2), (Sum.inr 5250, 1), (Sum.inr 5284, 1), (Sum.inr 5348, 1), (Sum.inr 5352, 2), (Sum.inr 5353, 2), (Sum.inr 5401, 2), (Sum.inr 5406, 1), (Sum.inr 5408, 2), (Sum.inr 5410, 2), (Sum.inr 5430, 2), (Sum.inr 5433, 1), (Sum.inr 5439, 1), (Sum.inr 5471, 1), (Sum.inr 5480, 2), (Sum.inr 5482, 1), (Sum.inr 5485, 1)]

theorem sourceEq1048 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1048 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1048 + difference 0 1) (sourceB1048 + difference 1 0) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1048 + difference 0 1) (sourceB1048 + difference 1 0) sourceC1048) = raw17179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17179; decide +kernel
    rw [ha]
    exact (canonical17179 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1048 + difference 0 2) (sourceB1048 + difference 2 0) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA1048 + difference 0 2) (sourceB1048 + difference 2 0) sourceC1048) = raw17180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17180; decide +kernel
    rw [ha]
    exact (canonical17180 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1048 + difference 0 3) (sourceB1048 + difference 3 0) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA1048 + difference 0 3) (sourceB1048 + difference 3 0) sourceC1048) = raw17181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17181; decide +kernel
    rw [ha]
    exact (canonical17181 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1048 + difference 0 4) (sourceB1048 + difference 4 0) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1048 + difference 0 4) (sourceB1048 + difference 4 0) sourceC1048) = raw17182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17182; decide +kernel
    rw [ha]
    exact (canonical17182 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1048 + difference 0 5) (sourceB1048 + difference 5 0) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1048 + difference 0 5) (sourceB1048 + difference 5 0) sourceC1048) = raw17183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17183; decide +kernel
    rw [ha]
    exact (canonical17183 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1048 + difference 1 0) (sourceB1048 + difference 0 1) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA1048 + difference 1 0) (sourceB1048 + difference 0 1) sourceC1048) = raw17184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17184; decide +kernel
    rw [ha]
    exact (canonical17184 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1048 + difference 1 2) (sourceB1048 + difference 2 1) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1048 + difference 1 2) (sourceB1048 + difference 2 1) sourceC1048) = raw9129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9129; decide +kernel
    rw [ha]
    exact (canonical9129 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1048 + difference 1 3) (sourceB1048 + difference 3 1) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1048 + difference 1 3) (sourceB1048 + difference 3 1) sourceC1048) = raw9130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9130; decide +kernel
    rw [ha]
    exact (canonical9130 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1048 + difference 1 4) (sourceB1048 + difference 4 1) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1048 + difference 1 4) (sourceB1048 + difference 4 1) sourceC1048) = raw9131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9131; decide +kernel
    rw [ha]
    exact (canonical9131 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1048 + difference 1 5) (sourceB1048 + difference 5 1) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1048 + difference 1 5) (sourceB1048 + difference 5 1) sourceC1048) = raw9132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9132; decide +kernel
    rw [ha]
    exact (canonical9132 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1048 + difference 2 0) (sourceB1048 + difference 0 2) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA1048 + difference 2 0) (sourceB1048 + difference 0 2) sourceC1048) = raw9139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9139; decide +kernel
    rw [ha]
    exact (canonical9139 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1048 + difference 2 1) (sourceB1048 + difference 1 2) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA1048 + difference 2 1) (sourceB1048 + difference 1 2) sourceC1048) = raw17185 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17185; decide +kernel
    rw [ha]
    exact (canonical17185 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1048 + difference 2 3) (sourceB1048 + difference 3 2) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1048 + difference 2 3) (sourceB1048 + difference 3 2) sourceC1048) = raw17186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17186; decide +kernel
    rw [ha]
    exact (canonical17186 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1048 + difference 2 4) (sourceB1048 + difference 4 2) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1048 + difference 2 4) (sourceB1048 + difference 4 2) sourceC1048) = raw17187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17187; decide +kernel
    rw [ha]
    exact (canonical17187 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1048 + difference 2 5) (sourceB1048 + difference 5 2) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1048 + difference 2 5) (sourceB1048 + difference 5 2) sourceC1048) = raw17188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17188; decide +kernel
    rw [ha]
    exact (canonical17188 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1048 + difference 3 0) (sourceB1048 + difference 0 3) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA1048 + difference 3 0) (sourceB1048 + difference 0 3) sourceC1048) = raw9144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9144; decide +kernel
    rw [ha]
    exact (canonical9144 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1048 + difference 3 1) (sourceB1048 + difference 1 3) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA1048 + difference 3 1) (sourceB1048 + difference 1 3) sourceC1048) = raw17189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17189; decide +kernel
    rw [ha]
    exact (canonical17189 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1048 + difference 3 2) (sourceB1048 + difference 2 3) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1048 + difference 3 2) (sourceB1048 + difference 2 3) sourceC1048) = raw17190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17190; decide +kernel
    rw [ha]
    exact (canonical17190 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1048 + difference 3 4) (sourceB1048 + difference 4 3) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1048 + difference 3 4) (sourceB1048 + difference 4 3) sourceC1048) = raw17191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17191; decide +kernel
    rw [ha]
    exact (canonical17191 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1048 + difference 3 5) (sourceB1048 + difference 5 3) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1048 + difference 3 5) (sourceB1048 + difference 5 3) sourceC1048) = raw17192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17192; decide +kernel
    rw [ha]
    exact (canonical17192 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1048 + difference 4 0) (sourceB1048 + difference 0 4) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA1048 + difference 4 0) (sourceB1048 + difference 0 4) sourceC1048) = raw9149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9149; decide +kernel
    rw [ha]
    exact (canonical9149 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1048 + difference 4 1) (sourceB1048 + difference 1 4) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5348) := by
    have ha : (tripleCharges (sourceA1048 + difference 4 1) (sourceB1048 + difference 1 4) sourceC1048) = raw17193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17193; decide +kernel
    rw [ha]
    exact (canonical17193 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1048 + difference 4 2) (sourceB1048 + difference 2 4) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1048 + difference 4 2) (sourceB1048 + difference 2 4) sourceC1048) = raw17194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17194; decide +kernel
    rw [ha]
    exact (canonical17194 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1048 + difference 4 3) (sourceB1048 + difference 3 4) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1048 + difference 4 3) (sourceB1048 + difference 3 4) sourceC1048) = raw17195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17195; decide +kernel
    rw [ha]
    exact (canonical17195 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1048 + difference 4 5) (sourceB1048 + difference 5 4) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1048 + difference 4 5) (sourceB1048 + difference 5 4) sourceC1048) = raw17196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17196; decide +kernel
    rw [ha]
    exact (canonical17196 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1048 + difference 5 0) (sourceB1048 + difference 0 5) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5065) := by
    have ha : (tripleCharges (sourceA1048 + difference 5 0) (sourceB1048 + difference 0 5) sourceC1048) = raw9154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9154; decide +kernel
    rw [ha]
    exact (canonical9154 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1048 + difference 5 1) (sourceB1048 + difference 1 5) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA1048 + difference 5 1) (sourceB1048 + difference 1 5) sourceC1048) = raw17197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17197; decide +kernel
    rw [ha]
    exact (canonical17197 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1048 + difference 5 2) (sourceB1048 + difference 2 5) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1048 + difference 5 2) (sourceB1048 + difference 2 5) sourceC1048) = raw17198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17198; decide +kernel
    rw [ha]
    exact (canonical17198 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1048 + difference 5 3) (sourceB1048 + difference 3 5) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1048 + difference 5 3) (sourceB1048 + difference 3 5) sourceC1048) = raw17199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17199; decide +kernel
    rw [ha]
    exact (canonical17199 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1048 + difference 5 4) (sourceB1048 + difference 4 5) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA1048 + difference 5 4) (sourceB1048 + difference 4 5) sourceC1048) = raw17200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17200; decide +kernel
    rw [ha]
    exact (canonical17200 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1048 sourceB1048 sourceC1048
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1048, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1049 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1049 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC1049 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceForm1049 : Integer.Sparse Master := [(Sum.inr 3463, 2), (Sum.inr 3466, 1), (Sum.inr 3467, 2), (Sum.inr 3476, 2), (Sum.inr 3531, 1), (Sum.inr 3625, 1), (Sum.inr 3761, 2), (Sum.inr 3764, 2), (Sum.inr 3768, 1), (Sum.inr 3804, 2), (Sum.inr 3806, 2), (Sum.inr 3812, 1), (Sum.inr 3816, 2), (Sum.inr 3848, 2), (Sum.inr 3851, 1), (Sum.inr 3858, 1), (Sum.inr 3956, 1), (Sum.inr 3978, 2), (Sum.inr 3980, 1), (Sum.inr 3984, 1)]

theorem sourceEq1049 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1049 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1049 + difference 0 1) (sourceB1049 + difference 1 0) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA1049 + difference 0 1) (sourceB1049 + difference 1 0) sourceC1049) = raw17201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17201; decide +kernel
    rw [ha]
    exact (canonical17201 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1049 + difference 0 2) (sourceB1049 + difference 2 0) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA1049 + difference 0 2) (sourceB1049 + difference 2 0) sourceC1049) = raw17202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17202; decide +kernel
    rw [ha]
    exact (canonical17202 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1049 + difference 0 3) (sourceB1049 + difference 3 0) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA1049 + difference 0 3) (sourceB1049 + difference 3 0) sourceC1049) = raw17203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17203; decide +kernel
    rw [ha]
    exact (canonical17203 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1049 + difference 0 4) (sourceB1049 + difference 4 0) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA1049 + difference 0 4) (sourceB1049 + difference 4 0) sourceC1049) = raw17204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17204; decide +kernel
    rw [ha]
    exact (canonical17204 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1049 + difference 0 5) (sourceB1049 + difference 5 0) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA1049 + difference 0 5) (sourceB1049 + difference 5 0) sourceC1049) = raw17205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17205; decide +kernel
    rw [ha]
    exact (canonical17205 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1049 + difference 1 0) (sourceB1049 + difference 0 1) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA1049 + difference 1 0) (sourceB1049 + difference 0 1) sourceC1049) = raw17206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17206; decide +kernel
    rw [ha]
    exact (canonical17206 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1049 + difference 1 2) (sourceB1049 + difference 2 1) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA1049 + difference 1 2) (sourceB1049 + difference 2 1) sourceC1049) = raw9189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw9189; decide +kernel
    rw [ha]
    exact (canonical9189 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1049 + difference 1 3) (sourceB1049 + difference 3 1) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA1049 + difference 1 3) (sourceB1049 + difference 3 1) sourceC1049) = raw9190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw9190; decide +kernel
    rw [ha]
    exact (canonical9190 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1049 + difference 1 4) (sourceB1049 + difference 4 1) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA1049 + difference 1 4) (sourceB1049 + difference 4 1) sourceC1049) = raw9191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw9191; decide +kernel
    rw [ha]
    exact (canonical9191 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1049 + difference 1 5) (sourceB1049 + difference 5 1) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA1049 + difference 1 5) (sourceB1049 + difference 5 1) sourceC1049) = raw9192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw9192; decide +kernel
    rw [ha]
    exact (canonical9192 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1049 + difference 2 0) (sourceB1049 + difference 0 2) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA1049 + difference 2 0) (sourceB1049 + difference 0 2) sourceC1049) = raw9199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw9199; decide +kernel
    rw [ha]
    exact (canonical9199 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1049 + difference 2 1) (sourceB1049 + difference 1 2) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA1049 + difference 2 1) (sourceB1049 + difference 1 2) sourceC1049) = raw17207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17207; decide +kernel
    rw [ha]
    exact (canonical17207 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1049 + difference 2 3) (sourceB1049 + difference 3 2) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA1049 + difference 2 3) (sourceB1049 + difference 3 2) sourceC1049) = raw17208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17208; decide +kernel
    rw [ha]
    exact (canonical17208 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1049 + difference 2 4) (sourceB1049 + difference 4 2) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA1049 + difference 2 4) (sourceB1049 + difference 4 2) sourceC1049) = raw17209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17209; decide +kernel
    rw [ha]
    exact (canonical17209 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1049 + difference 2 5) (sourceB1049 + difference 5 2) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1049 + difference 2 5) (sourceB1049 + difference 5 2) sourceC1049) = raw17210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17210; decide +kernel
    rw [ha]
    exact (canonical17210 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1049 + difference 3 0) (sourceB1049 + difference 0 3) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA1049 + difference 3 0) (sourceB1049 + difference 0 3) sourceC1049) = raw9204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw9204; decide +kernel
    rw [ha]
    exact (canonical9204 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1049 + difference 3 1) (sourceB1049 + difference 1 3) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA1049 + difference 3 1) (sourceB1049 + difference 1 3) sourceC1049) = raw17211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17211; decide +kernel
    rw [ha]
    exact (canonical17211 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1049 + difference 3 2) (sourceB1049 + difference 2 3) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA1049 + difference 3 2) (sourceB1049 + difference 2 3) sourceC1049) = raw17212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17212; decide +kernel
    rw [ha]
    exact (canonical17212 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1049 + difference 3 4) (sourceB1049 + difference 4 3) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA1049 + difference 3 4) (sourceB1049 + difference 4 3) sourceC1049) = raw17213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17213; decide +kernel
    rw [ha]
    exact (canonical17213 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1049 + difference 3 5) (sourceB1049 + difference 5 3) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1049 + difference 3 5) (sourceB1049 + difference 5 3) sourceC1049) = raw17214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17214; decide +kernel
    rw [ha]
    exact (canonical17214 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1049 + difference 4 0) (sourceB1049 + difference 0 4) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA1049 + difference 4 0) (sourceB1049 + difference 0 4) sourceC1049) = raw9209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw9209; decide +kernel
    rw [ha]
    exact (canonical9209 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1049 + difference 4 1) (sourceB1049 + difference 1 4) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3768) := by
    have ha : (tripleCharges (sourceA1049 + difference 4 1) (sourceB1049 + difference 1 4) sourceC1049) = raw17215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17215; decide +kernel
    rw [ha]
    exact (canonical17215 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1049 + difference 4 2) (sourceB1049 + difference 2 4) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA1049 + difference 4 2) (sourceB1049 + difference 2 4) sourceC1049) = raw17216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17216; decide +kernel
    rw [ha]
    exact (canonical17216 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1049 + difference 4 3) (sourceB1049 + difference 3 4) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA1049 + difference 4 3) (sourceB1049 + difference 3 4) sourceC1049) = raw17217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17217; decide +kernel
    rw [ha]
    exact (canonical17217 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1049 + difference 4 5) (sourceB1049 + difference 5 4) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA1049 + difference 4 5) (sourceB1049 + difference 5 4) sourceC1049) = raw17218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17218; decide +kernel
    rw [ha]
    exact (canonical17218 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1049 + difference 5 0) (sourceB1049 + difference 0 5) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3466) := by
    have ha : (tripleCharges (sourceA1049 + difference 5 0) (sourceB1049 + difference 0 5) sourceC1049) = raw9214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw9214; decide +kernel
    rw [ha]
    exact (canonical9214 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1049 + difference 5 1) (sourceB1049 + difference 1 5) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA1049 + difference 5 1) (sourceB1049 + difference 1 5) sourceC1049) = raw17219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17219; decide +kernel
    rw [ha]
    exact (canonical17219 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1049 + difference 5 2) (sourceB1049 + difference 2 5) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA1049 + difference 5 2) (sourceB1049 + difference 2 5) sourceC1049) = raw17220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17220; decide +kernel
    rw [ha]
    exact (canonical17220 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1049 + difference 5 3) (sourceB1049 + difference 3 5) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA1049 + difference 5 3) (sourceB1049 + difference 3 5) sourceC1049) = raw17221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17221; decide +kernel
    rw [ha]
    exact (canonical17221 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1049 + difference 5 4) (sourceB1049 + difference 4 5) sourceC1049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA1049 + difference 5 4) (sourceB1049 + difference 4 5) sourceC1049) = raw17222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1049 sourceB1049 sourceC1049 difference raw17222; decide +kernel
    rw [ha]
    exact (canonical17222 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1049 sourceB1049 sourceC1049
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1049, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1050 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1050 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC1050 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1050 : Integer.Sparse Master := [(Sum.inr 5072, 1), (Sum.inr 5074, 2), (Sum.inr 5098, 1), (Sum.inr 5256, 1), (Sum.inr 5351, 1), (Sum.inr 5353, 2), (Sum.inr 5365, 1), (Sum.inr 5400, 1), (Sum.inr 5402, 2), (Sum.inr 5405, 1), (Sum.inr 5406, 2), (Sum.inr 5407, 2), (Sum.inr 5409, 2), (Sum.inr 5410, 2), (Sum.inr 5411, 2), (Sum.inr 5429, 1), (Sum.inr 5434, 2), (Sum.inr 5471, 2), (Sum.inr 5483, 2)]

theorem sourceEq1050 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1050 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1050 + difference 0 1) (sourceB1050 + difference 1 0) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1050 + difference 0 1) (sourceB1050 + difference 1 0) sourceC1050) = raw16842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw16842; decide +kernel
    rw [ha]
    exact (canonical16842 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1050 + difference 0 2) (sourceB1050 + difference 2 0) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1050 + difference 0 2) (sourceB1050 + difference 2 0) sourceC1050) = raw17122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17122; decide +kernel
    rw [ha]
    exact (canonical17122 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1050 + difference 0 3) (sourceB1050 + difference 3 0) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1050 + difference 0 3) (sourceB1050 + difference 3 0) sourceC1050) = raw17223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17223; decide +kernel
    rw [ha]
    exact (canonical17223 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1050 + difference 0 4) (sourceB1050 + difference 4 0) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1050 + difference 0 4) (sourceB1050 + difference 4 0) sourceC1050) = raw17224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17224; decide +kernel
    rw [ha]
    exact (canonical17224 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1050 + difference 0 5) (sourceB1050 + difference 5 0) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA1050 + difference 0 5) (sourceB1050 + difference 5 0) sourceC1050) = raw17225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17225; decide +kernel
    rw [ha]
    exact (canonical17225 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1050 + difference 1 0) (sourceB1050 + difference 0 1) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1050 + difference 1 0) (sourceB1050 + difference 0 1) sourceC1050) = raw15127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15127; decide +kernel
    rw [ha]
    exact (canonical15127 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1050 + difference 1 2) (sourceB1050 + difference 2 1) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1050 + difference 1 2) (sourceB1050 + difference 2 1) sourceC1050) = raw15117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15117; decide +kernel
    rw [ha]
    exact (canonical15117 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1050 + difference 1 3) (sourceB1050 + difference 3 1) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1050 + difference 1 3) (sourceB1050 + difference 3 1) sourceC1050) = raw15859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15859; decide +kernel
    rw [ha]
    exact (canonical15859 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1050 + difference 1 4) (sourceB1050 + difference 4 1) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA1050 + difference 1 4) (sourceB1050 + difference 4 1) sourceC1050) = raw15667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15667; decide +kernel
    rw [ha]
    exact (canonical15667 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1050 + difference 1 5) (sourceB1050 + difference 5 1) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA1050 + difference 1 5) (sourceB1050 + difference 5 1) sourceC1050) = raw15860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15860; decide +kernel
    rw [ha]
    exact (canonical15860 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1050 + difference 2 0) (sourceB1050 + difference 0 2) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5407) := by
    have ha : (tripleCharges (sourceA1050 + difference 2 0) (sourceB1050 + difference 0 2) sourceC1050) = raw15865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15865; decide +kernel
    rw [ha]
    exact (canonical15865 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1050 + difference 2 1) (sourceB1050 + difference 1 2) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5402) := by
    have ha : (tripleCharges (sourceA1050 + difference 2 1) (sourceB1050 + difference 1 2) sourceC1050) = raw16848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw16848; decide +kernel
    rw [ha]
    exact (canonical16848 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1050 + difference 2 3) (sourceB1050 + difference 3 2) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1050 + difference 2 3) (sourceB1050 + difference 3 2) sourceC1050) = raw17226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17226; decide +kernel
    rw [ha]
    exact (canonical17226 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1050 + difference 2 4) (sourceB1050 + difference 4 2) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA1050 + difference 2 4) (sourceB1050 + difference 4 2) sourceC1050) = raw17227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17227; decide +kernel
    rw [ha]
    exact (canonical17227 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1050 + difference 2 5) (sourceB1050 + difference 5 2) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA1050 + difference 2 5) (sourceB1050 + difference 5 2) sourceC1050) = raw17228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17228; decide +kernel
    rw [ha]
    exact (canonical17228 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1050 + difference 3 0) (sourceB1050 + difference 0 3) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5407) := by
    have ha : (tripleCharges (sourceA1050 + difference 3 0) (sourceB1050 + difference 0 3) sourceC1050) = raw15869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15869; decide +kernel
    rw [ha]
    exact (canonical15869 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1050 + difference 3 1) (sourceB1050 + difference 1 3) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5402) := by
    have ha : (tripleCharges (sourceA1050 + difference 3 1) (sourceB1050 + difference 1 3) sourceC1050) = raw16853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw16853; decide +kernel
    rw [ha]
    exact (canonical16853 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1050 + difference 3 2) (sourceB1050 + difference 2 3) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1050 + difference 3 2) (sourceB1050 + difference 2 3) sourceC1050) = raw17038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17038; decide +kernel
    rw [ha]
    exact (canonical17038 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1050 + difference 3 4) (sourceB1050 + difference 4 3) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA1050 + difference 3 4) (sourceB1050 + difference 4 3) sourceC1050) = raw17229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17229; decide +kernel
    rw [ha]
    exact (canonical17229 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1050 + difference 3 5) (sourceB1050 + difference 5 3) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA1050 + difference 3 5) (sourceB1050 + difference 5 3) sourceC1050) = raw17230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17230; decide +kernel
    rw [ha]
    exact (canonical17230 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1050 + difference 4 0) (sourceB1050 + difference 0 4) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1050 + difference 4 0) (sourceB1050 + difference 0 4) sourceC1050) = raw15205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15205; decide +kernel
    rw [ha]
    exact (canonical15205 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1050 + difference 4 1) (sourceB1050 + difference 1 4) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1050 + difference 4 1) (sourceB1050 + difference 1 4) sourceC1050) = raw16858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw16858; decide +kernel
    rw [ha]
    exact (canonical16858 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1050 + difference 4 2) (sourceB1050 + difference 2 4) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1050 + difference 4 2) (sourceB1050 + difference 2 4) sourceC1050) = raw15200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15200; decide +kernel
    rw [ha]
    exact (canonical15200 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1050 + difference 4 3) (sourceB1050 + difference 3 4) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1050 + difference 4 3) (sourceB1050 + difference 3 4) sourceC1050) = raw17231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17231; decide +kernel
    rw [ha]
    exact (canonical17231 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1050 + difference 4 5) (sourceB1050 + difference 5 4) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA1050 + difference 4 5) (sourceB1050 + difference 5 4) sourceC1050) = raw17232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17232; decide +kernel
    rw [ha]
    exact (canonical17232 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1050 + difference 5 0) (sourceB1050 + difference 0 5) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1050 + difference 5 0) (sourceB1050 + difference 0 5) sourceC1050) = raw15124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15124; decide +kernel
    rw [ha]
    exact (canonical15124 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1050 + difference 5 1) (sourceB1050 + difference 1 5) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1050 + difference 5 1) (sourceB1050 + difference 1 5) sourceC1050) = raw17123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17123; decide +kernel
    rw [ha]
    exact (canonical17123 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1050 + difference 5 2) (sourceB1050 + difference 2 5) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1050 + difference 5 2) (sourceB1050 + difference 2 5) sourceC1050) = raw15113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15113; decide +kernel
    rw [ha]
    exact (canonical15113 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1050 + difference 5 3) (sourceB1050 + difference 3 5) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1050 + difference 5 3) (sourceB1050 + difference 3 5) sourceC1050) = raw16843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw16843; decide +kernel
    rw [ha]
    exact (canonical16843 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1050 + difference 5 4) (sourceB1050 + difference 4 5) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1050 + difference 5 4) (sourceB1050 + difference 4 5) sourceC1050) = raw15664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15664; decide +kernel
    rw [ha]
    exact (canonical15664 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1050 sourceB1050 sourceC1050
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1050, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1051 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1051 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC1051 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1051 : Integer.Sparse Master := [(Sum.inr 3459, 1), (Sum.inr 3460, 1), (Sum.inr 3463, 2), (Sum.inr 3525, 1), (Sum.inr 3757, 1), (Sum.inr 3758, 1), (Sum.inr 3761, 2), (Sum.inr 3799, 1), (Sum.inr 3801, 1), (Sum.inr 3802, 2), (Sum.inr 3803, 2), (Sum.inr 3807, 2), (Sum.inr 3808, 2), (Sum.inr 3813, 2), (Sum.inr 3846, 1), (Sum.inr 3847, 1), (Sum.inr 3852, 2), (Sum.inr 3953, 1), (Sum.inr 3976, 1), (Sum.inr 3977, 1), (Sum.inr 3981, 2)]

theorem sourceEq1051 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1051 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1051 + difference 0 1) (sourceB1051 + difference 1 0) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA1051 + difference 0 1) (sourceB1051 + difference 1 0) sourceC1051) = raw16895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw16895; decide +kernel
    rw [ha]
    exact (canonical16895 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1051 + difference 0 2) (sourceB1051 + difference 2 0) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA1051 + difference 0 2) (sourceB1051 + difference 2 0) sourceC1051) = raw17233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17233; decide +kernel
    rw [ha]
    exact (canonical17233 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1051 + difference 0 3) (sourceB1051 + difference 3 0) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA1051 + difference 0 3) (sourceB1051 + difference 3 0) sourceC1051) = raw17234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17234; decide +kernel
    rw [ha]
    exact (canonical17234 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1051 + difference 0 4) (sourceB1051 + difference 4 0) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA1051 + difference 0 4) (sourceB1051 + difference 4 0) sourceC1051) = raw17235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17235; decide +kernel
    rw [ha]
    exact (canonical17235 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1051 + difference 0 5) (sourceB1051 + difference 5 0) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3459) := by
    have ha : (tripleCharges (sourceA1051 + difference 0 5) (sourceB1051 + difference 5 0) sourceC1051) = raw17236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17236; decide +kernel
    rw [ha]
    exact (canonical17236 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1051 + difference 1 0) (sourceB1051 + difference 0 1) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA1051 + difference 1 0) (sourceB1051 + difference 0 1) sourceC1051) = raw15154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15154; decide +kernel
    rw [ha]
    exact (canonical15154 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1051 + difference 1 2) (sourceB1051 + difference 2 1) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA1051 + difference 1 2) (sourceB1051 + difference 2 1) sourceC1051) = raw15144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15144; decide +kernel
    rw [ha]
    exact (canonical15144 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1051 + difference 1 3) (sourceB1051 + difference 3 1) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA1051 + difference 1 3) (sourceB1051 + difference 3 1) sourceC1051) = raw15893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15893; decide +kernel
    rw [ha]
    exact (canonical15893 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1051 + difference 1 4) (sourceB1051 + difference 4 1) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA1051 + difference 1 4) (sourceB1051 + difference 4 1) sourceC1051) = raw15718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15718; decide +kernel
    rw [ha]
    exact (canonical15718 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1051 + difference 1 5) (sourceB1051 + difference 5 1) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA1051 + difference 1 5) (sourceB1051 + difference 5 1) sourceC1051) = raw15894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15894; decide +kernel
    rw [ha]
    exact (canonical15894 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1051 + difference 2 0) (sourceB1051 + difference 0 2) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA1051 + difference 2 0) (sourceB1051 + difference 0 2) sourceC1051) = raw15899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15899; decide +kernel
    rw [ha]
    exact (canonical15899 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1051 + difference 2 1) (sourceB1051 + difference 1 2) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA1051 + difference 2 1) (sourceB1051 + difference 1 2) sourceC1051) = raw16901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw16901; decide +kernel
    rw [ha]
    exact (canonical16901 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1051 + difference 2 3) (sourceB1051 + difference 3 2) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA1051 + difference 2 3) (sourceB1051 + difference 3 2) sourceC1051) = raw17237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17237; decide +kernel
    rw [ha]
    exact (canonical17237 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1051 + difference 2 4) (sourceB1051 + difference 4 2) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA1051 + difference 2 4) (sourceB1051 + difference 4 2) sourceC1051) = raw17238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17238; decide +kernel
    rw [ha]
    exact (canonical17238 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1051 + difference 2 5) (sourceB1051 + difference 5 2) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA1051 + difference 2 5) (sourceB1051 + difference 5 2) sourceC1051) = raw17239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17239; decide +kernel
    rw [ha]
    exact (canonical17239 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1051 + difference 3 0) (sourceB1051 + difference 0 3) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA1051 + difference 3 0) (sourceB1051 + difference 0 3) sourceC1051) = raw15903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15903; decide +kernel
    rw [ha]
    exact (canonical15903 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1051 + difference 3 1) (sourceB1051 + difference 1 3) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA1051 + difference 3 1) (sourceB1051 + difference 1 3) sourceC1051) = raw16906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw16906; decide +kernel
    rw [ha]
    exact (canonical16906 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1051 + difference 3 2) (sourceB1051 + difference 2 3) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA1051 + difference 3 2) (sourceB1051 + difference 2 3) sourceC1051) = raw17240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17240; decide +kernel
    rw [ha]
    exact (canonical17240 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1051 + difference 3 4) (sourceB1051 + difference 4 3) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA1051 + difference 3 4) (sourceB1051 + difference 4 3) sourceC1051) = raw17241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17241; decide +kernel
    rw [ha]
    exact (canonical17241 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1051 + difference 3 5) (sourceB1051 + difference 5 3) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA1051 + difference 3 5) (sourceB1051 + difference 5 3) sourceC1051) = raw17242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17242; decide +kernel
    rw [ha]
    exact (canonical17242 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1051 + difference 4 0) (sourceB1051 + difference 0 4) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA1051 + difference 4 0) (sourceB1051 + difference 0 4) sourceC1051) = raw15906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15906; decide +kernel
    rw [ha]
    exact (canonical15906 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1051 + difference 4 1) (sourceB1051 + difference 1 4) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA1051 + difference 4 1) (sourceB1051 + difference 1 4) sourceC1051) = raw16911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw16911; decide +kernel
    rw [ha]
    exact (canonical16911 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1051 + difference 4 2) (sourceB1051 + difference 2 4) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1051 + difference 4 2) (sourceB1051 + difference 2 4) sourceC1051) = raw17243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17243; decide +kernel
    rw [ha]
    exact (canonical17243 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1051 + difference 4 3) (sourceB1051 + difference 3 4) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1051 + difference 4 3) (sourceB1051 + difference 3 4) sourceC1051) = raw17244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17244; decide +kernel
    rw [ha]
    exact (canonical17244 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1051 + difference 4 5) (sourceB1051 + difference 5 4) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA1051 + difference 4 5) (sourceB1051 + difference 5 4) sourceC1051) = raw17245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17245; decide +kernel
    rw [ha]
    exact (canonical17245 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1051 + difference 5 0) (sourceB1051 + difference 0 5) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA1051 + difference 5 0) (sourceB1051 + difference 0 5) sourceC1051) = raw15151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15151; decide +kernel
    rw [ha]
    exact (canonical15151 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1051 + difference 5 1) (sourceB1051 + difference 1 5) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3976) := by
    have ha : (tripleCharges (sourceA1051 + difference 5 1) (sourceB1051 + difference 1 5) sourceC1051) = raw17246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17246; decide +kernel
    rw [ha]
    exact (canonical17246 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1051 + difference 5 2) (sourceB1051 + difference 2 5) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1051 + difference 5 2) (sourceB1051 + difference 2 5) sourceC1051) = raw15140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15140; decide +kernel
    rw [ha]
    exact (canonical15140 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1051 + difference 5 3) (sourceB1051 + difference 3 5) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1051 + difference 5 3) (sourceB1051 + difference 3 5) sourceC1051) = raw16896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw16896; decide +kernel
    rw [ha]
    exact (canonical16896 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1051 + difference 5 4) (sourceB1051 + difference 4 5) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA1051 + difference 5 4) (sourceB1051 + difference 4 5) sourceC1051) = raw15715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15715; decide +kernel
    rw [ha]
    exact (canonical15715 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1051 sourceB1051 sourceC1051
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1051, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1052 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1052 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC1052 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceForm1052 : Integer.Sparse Master := [(Sum.inr 5138, 1), (Sum.inr 5139, 1), (Sum.inr 5140, 1), (Sum.inr 5170, 1), (Sum.inr 5185, 1), (Sum.inr 5189, 1), (Sum.inr 5199, 1), (Sum.inr 5226, 1), (Sum.inr 5229, 1), (Sum.inr 5236, 1), (Sum.inr 5259, 1), (Sum.inr 5260, 1), (Sum.inr 5289, 1), (Sum.inr 5401, 1), (Sum.inr 5404, 1), (Sum.inr 5410, 1), (Sum.inr 5419, 1), (Sum.inr 5421, 1), (Sum.inr 5424, 1), (Sum.inr 5430, 1), (Sum.inr 5431, 1), (Sum.inr 5438, 1), (Sum.inr 5439, 1), (Sum.inr 5440, 1), (Sum.inr 5446, 1), (Sum.inr 5448, 1), (Sum.inr 5480, 1), (Sum.inr 5484, 2), (Sum.inr 5485, 1)]

theorem sourceEq1052 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1052 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1052 + difference 0 1) (sourceB1052 + difference 1 0) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1052 + difference 0 1) (sourceB1052 + difference 1 0) sourceC1052) = raw17247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17247; decide +kernel
    rw [ha]
    exact (canonical17247 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1052 + difference 0 2) (sourceB1052 + difference 2 0) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1052 + difference 0 2) (sourceB1052 + difference 2 0) sourceC1052) = raw17248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17248; decide +kernel
    rw [ha]
    exact (canonical17248 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1052 + difference 0 3) (sourceB1052 + difference 3 0) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1052 + difference 0 3) (sourceB1052 + difference 3 0) sourceC1052) = raw17249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17249; decide +kernel
    rw [ha]
    exact (canonical17249 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1052 + difference 0 4) (sourceB1052 + difference 4 0) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1052 + difference 0 4) (sourceB1052 + difference 4 0) sourceC1052) = raw17250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17250; decide +kernel
    rw [ha]
    exact (canonical17250 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1052 + difference 0 5) (sourceB1052 + difference 5 0) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1052 + difference 0 5) (sourceB1052 + difference 5 0) sourceC1052) = raw17251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17251; decide +kernel
    rw [ha]
    exact (canonical17251 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1052 + difference 1 0) (sourceB1052 + difference 0 1) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA1052 + difference 1 0) (sourceB1052 + difference 0 1) sourceC1052) = raw17252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17252; decide +kernel
    rw [ha]
    exact (canonical17252 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1052 + difference 1 2) (sourceB1052 + difference 2 1) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1052 + difference 1 2) (sourceB1052 + difference 2 1) sourceC1052) = raw17253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17253; decide +kernel
    rw [ha]
    exact (canonical17253 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1052 + difference 1 3) (sourceB1052 + difference 3 1) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1052 + difference 1 3) (sourceB1052 + difference 3 1) sourceC1052) = raw17254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17254; decide +kernel
    rw [ha]
    exact (canonical17254 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1052 + difference 1 4) (sourceB1052 + difference 4 1) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1052 + difference 1 4) (sourceB1052 + difference 4 1) sourceC1052) = raw17255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17255; decide +kernel
    rw [ha]
    exact (canonical17255 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1052 + difference 1 5) (sourceB1052 + difference 5 1) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1052 + difference 1 5) (sourceB1052 + difference 5 1) sourceC1052) = raw17256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17256; decide +kernel
    rw [ha]
    exact (canonical17256 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1052 + difference 2 0) (sourceB1052 + difference 0 2) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA1052 + difference 2 0) (sourceB1052 + difference 0 2) sourceC1052) = raw17257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17257; decide +kernel
    rw [ha]
    exact (canonical17257 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1052 + difference 2 1) (sourceB1052 + difference 1 2) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA1052 + difference 2 1) (sourceB1052 + difference 1 2) sourceC1052) = raw17258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17258; decide +kernel
    rw [ha]
    exact (canonical17258 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1052 + difference 2 3) (sourceB1052 + difference 3 2) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1052 + difference 2 3) (sourceB1052 + difference 3 2) sourceC1052) = raw17259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17259; decide +kernel
    rw [ha]
    exact (canonical17259 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1052 + difference 2 4) (sourceB1052 + difference 4 2) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1052 + difference 2 4) (sourceB1052 + difference 4 2) sourceC1052) = raw17260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17260; decide +kernel
    rw [ha]
    exact (canonical17260 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1052 + difference 2 5) (sourceB1052 + difference 5 2) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1052 + difference 2 5) (sourceB1052 + difference 5 2) sourceC1052) = raw17261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17261; decide +kernel
    rw [ha]
    exact (canonical17261 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1052 + difference 3 0) (sourceB1052 + difference 0 3) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA1052 + difference 3 0) (sourceB1052 + difference 0 3) sourceC1052) = raw17262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17262; decide +kernel
    rw [ha]
    exact (canonical17262 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1052 + difference 3 1) (sourceB1052 + difference 1 3) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5419) := by
    have ha : (tripleCharges (sourceA1052 + difference 3 1) (sourceB1052 + difference 1 3) sourceC1052) = raw17263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17263; decide +kernel
    rw [ha]
    exact (canonical17263 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1052 + difference 3 2) (sourceB1052 + difference 2 3) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1052 + difference 3 2) (sourceB1052 + difference 2 3) sourceC1052) = raw17264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17264; decide +kernel
    rw [ha]
    exact (canonical17264 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1052 + difference 3 4) (sourceB1052 + difference 4 3) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1052 + difference 3 4) (sourceB1052 + difference 4 3) sourceC1052) = raw17265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17265; decide +kernel
    rw [ha]
    exact (canonical17265 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1052 + difference 3 5) (sourceB1052 + difference 5 3) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1052 + difference 3 5) (sourceB1052 + difference 5 3) sourceC1052) = raw17266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17266; decide +kernel
    rw [ha]
    exact (canonical17266 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1052 + difference 4 0) (sourceB1052 + difference 0 4) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA1052 + difference 4 0) (sourceB1052 + difference 0 4) sourceC1052) = raw17267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17267; decide +kernel
    rw [ha]
    exact (canonical17267 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1052 + difference 4 1) (sourceB1052 + difference 1 4) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA1052 + difference 4 1) (sourceB1052 + difference 1 4) sourceC1052) = raw17268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17268; decide +kernel
    rw [ha]
    exact (canonical17268 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1052 + difference 4 2) (sourceB1052 + difference 2 4) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA1052 + difference 4 2) (sourceB1052 + difference 2 4) sourceC1052) = raw17269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17269; decide +kernel
    rw [ha]
    exact (canonical17269 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1052 + difference 4 3) (sourceB1052 + difference 3 4) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA1052 + difference 4 3) (sourceB1052 + difference 3 4) sourceC1052) = raw17270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17270; decide +kernel
    rw [ha]
    exact (canonical17270 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1052 + difference 4 5) (sourceB1052 + difference 5 4) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA1052 + difference 4 5) (sourceB1052 + difference 5 4) sourceC1052) = raw17271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17271; decide +kernel
    rw [ha]
    exact (canonical17271 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1052 + difference 5 0) (sourceB1052 + difference 0 5) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1052 + difference 5 0) (sourceB1052 + difference 0 5) sourceC1052) = raw17272 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17272; decide +kernel
    rw [ha]
    exact (canonical17272 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1052 + difference 5 1) (sourceB1052 + difference 1 5) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA1052 + difference 5 1) (sourceB1052 + difference 1 5) sourceC1052) = raw17273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17273; decide +kernel
    rw [ha]
    exact (canonical17273 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1052 + difference 5 2) (sourceB1052 + difference 2 5) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA1052 + difference 5 2) (sourceB1052 + difference 2 5) sourceC1052) = raw17274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17274; decide +kernel
    rw [ha]
    exact (canonical17274 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1052 + difference 5 3) (sourceB1052 + difference 3 5) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA1052 + difference 5 3) (sourceB1052 + difference 3 5) sourceC1052) = raw17275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17275; decide +kernel
    rw [ha]
    exact (canonical17275 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1052 + difference 5 4) (sourceB1052 + difference 4 5) sourceC1052) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA1052 + difference 5 4) (sourceB1052 + difference 4 5) sourceC1052) = raw17276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1052 sourceB1052 sourceC1052 difference raw17276; decide +kernel
    rw [ha]
    exact (canonical17276 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1052 sourceB1052 sourceC1052
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1052, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1053 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1053 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC1053 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceForm1053 : Integer.Sparse Master := [(Sum.inr 2669, 1), (Sum.inr 2670, 1), (Sum.inr 2673, 1), (Sum.inr 2682, 1), (Sum.inr 2763, 1), (Sum.inr 3517, 1), (Sum.inr 3523, 1), (Sum.inr 3529, 1), (Sum.inr 3540, 1), (Sum.inr 3542, 1), (Sum.inr 3544, 1), (Sum.inr 3578, 1), (Sum.inr 3606, 1), (Sum.inr 3804, 1), (Sum.inr 3815, 1), (Sum.inr 3816, 1), (Sum.inr 3842, 1), (Sum.inr 3843, 1), (Sum.inr 3848, 1), (Sum.inr 3849, 1), (Sum.inr 3857, 1), (Sum.inr 3858, 1), (Sum.inr 3859, 1), (Sum.inr 3873, 1), (Sum.inr 3884, 1), (Sum.inr 3885, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 1), (Sum.inr 3997, 1), (Sum.inr 3998, 1)]

theorem sourceEq1053 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1053 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1053 + difference 0 1) (sourceB1053 + difference 1 0) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA1053 + difference 0 1) (sourceB1053 + difference 1 0) sourceC1053) = raw17277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17277; decide +kernel
    rw [ha]
    exact (canonical17277 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1053 + difference 0 2) (sourceB1053 + difference 2 0) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA1053 + difference 0 2) (sourceB1053 + difference 2 0) sourceC1053) = raw17278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17278; decide +kernel
    rw [ha]
    exact (canonical17278 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1053 + difference 0 3) (sourceB1053 + difference 3 0) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA1053 + difference 0 3) (sourceB1053 + difference 3 0) sourceC1053) = raw17279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17279; decide +kernel
    rw [ha]
    exact (canonical17279 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1053 + difference 0 4) (sourceB1053 + difference 4 0) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3859) := by
    have ha : (tripleCharges (sourceA1053 + difference 0 4) (sourceB1053 + difference 4 0) sourceC1053) = raw17280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17280; decide +kernel
    rw [ha]
    exact (canonical17280 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1053 + difference 0 5) (sourceB1053 + difference 5 0) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA1053 + difference 0 5) (sourceB1053 + difference 5 0) sourceC1053) = raw17281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17281; decide +kernel
    rw [ha]
    exact (canonical17281 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1053 + difference 1 0) (sourceB1053 + difference 0 1) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA1053 + difference 1 0) (sourceB1053 + difference 0 1) sourceC1053) = raw17282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17282; decide +kernel
    rw [ha]
    exact (canonical17282 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1053 + difference 1 2) (sourceB1053 + difference 2 1) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA1053 + difference 1 2) (sourceB1053 + difference 2 1) sourceC1053) = raw17283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17283; decide +kernel
    rw [ha]
    exact (canonical17283 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1053 + difference 1 3) (sourceB1053 + difference 3 1) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA1053 + difference 1 3) (sourceB1053 + difference 3 1) sourceC1053) = raw17284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17284; decide +kernel
    rw [ha]
    exact (canonical17284 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1053 + difference 1 4) (sourceB1053 + difference 4 1) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA1053 + difference 1 4) (sourceB1053 + difference 4 1) sourceC1053) = raw17285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17285; decide +kernel
    rw [ha]
    exact (canonical17285 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1053 + difference 1 5) (sourceB1053 + difference 5 1) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3997) := by
    have ha : (tripleCharges (sourceA1053 + difference 1 5) (sourceB1053 + difference 5 1) sourceC1053) = raw17286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17286; decide +kernel
    rw [ha]
    exact (canonical17286 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1053 + difference 2 0) (sourceB1053 + difference 0 2) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA1053 + difference 2 0) (sourceB1053 + difference 0 2) sourceC1053) = raw17287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17287; decide +kernel
    rw [ha]
    exact (canonical17287 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1053 + difference 2 1) (sourceB1053 + difference 1 2) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3815) := by
    have ha : (tripleCharges (sourceA1053 + difference 2 1) (sourceB1053 + difference 1 2) sourceC1053) = raw17288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17288; decide +kernel
    rw [ha]
    exact (canonical17288 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1053 + difference 2 3) (sourceB1053 + difference 3 2) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA1053 + difference 2 3) (sourceB1053 + difference 3 2) sourceC1053) = raw17289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17289; decide +kernel
    rw [ha]
    exact (canonical17289 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1053 + difference 2 4) (sourceB1053 + difference 4 2) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA1053 + difference 2 4) (sourceB1053 + difference 4 2) sourceC1053) = raw17290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17290; decide +kernel
    rw [ha]
    exact (canonical17290 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1053 + difference 2 5) (sourceB1053 + difference 5 2) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA1053 + difference 2 5) (sourceB1053 + difference 5 2) sourceC1053) = raw17291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17291; decide +kernel
    rw [ha]
    exact (canonical17291 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1053 + difference 3 0) (sourceB1053 + difference 0 3) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA1053 + difference 3 0) (sourceB1053 + difference 0 3) sourceC1053) = raw17292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17292; decide +kernel
    rw [ha]
    exact (canonical17292 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1053 + difference 3 1) (sourceB1053 + difference 1 3) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3842) := by
    have ha : (tripleCharges (sourceA1053 + difference 3 1) (sourceB1053 + difference 1 3) sourceC1053) = raw17293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17293; decide +kernel
    rw [ha]
    exact (canonical17293 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1053 + difference 3 2) (sourceB1053 + difference 2 3) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA1053 + difference 3 2) (sourceB1053 + difference 2 3) sourceC1053) = raw17294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17294; decide +kernel
    rw [ha]
    exact (canonical17294 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1053 + difference 3 4) (sourceB1053 + difference 4 3) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA1053 + difference 3 4) (sourceB1053 + difference 4 3) sourceC1053) = raw17295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17295; decide +kernel
    rw [ha]
    exact (canonical17295 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1053 + difference 3 5) (sourceB1053 + difference 5 3) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1053 + difference 3 5) (sourceB1053 + difference 5 3) sourceC1053) = raw17296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17296; decide +kernel
    rw [ha]
    exact (canonical17296 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1053 + difference 4 0) (sourceB1053 + difference 0 4) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA1053 + difference 4 0) (sourceB1053 + difference 0 4) sourceC1053) = raw17297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17297; decide +kernel
    rw [ha]
    exact (canonical17297 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1053 + difference 4 1) (sourceB1053 + difference 1 4) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2682) := by
    have ha : (tripleCharges (sourceA1053 + difference 4 1) (sourceB1053 + difference 1 4) sourceC1053) = raw17298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17298; decide +kernel
    rw [ha]
    exact (canonical17298 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1053 + difference 4 2) (sourceB1053 + difference 2 4) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA1053 + difference 4 2) (sourceB1053 + difference 2 4) sourceC1053) = raw17299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17299; decide +kernel
    rw [ha]
    exact (canonical17299 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1053 + difference 4 3) (sourceB1053 + difference 3 4) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA1053 + difference 4 3) (sourceB1053 + difference 3 4) sourceC1053) = raw17300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17300; decide +kernel
    rw [ha]
    exact (canonical17300 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1053 + difference 4 5) (sourceB1053 + difference 5 4) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA1053 + difference 4 5) (sourceB1053 + difference 5 4) sourceC1053) = raw17301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17301; decide +kernel
    rw [ha]
    exact (canonical17301 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1053 + difference 5 0) (sourceB1053 + difference 0 5) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1053 + difference 5 0) (sourceB1053 + difference 0 5) sourceC1053) = raw17302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17302; decide +kernel
    rw [ha]
    exact (canonical17302 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1053 + difference 5 1) (sourceB1053 + difference 1 5) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA1053 + difference 5 1) (sourceB1053 + difference 1 5) sourceC1053) = raw17303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17303; decide +kernel
    rw [ha]
    exact (canonical17303 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1053 + difference 5 2) (sourceB1053 + difference 2 5) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA1053 + difference 5 2) (sourceB1053 + difference 2 5) sourceC1053) = raw17304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17304; decide +kernel
    rw [ha]
    exact (canonical17304 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1053 + difference 5 3) (sourceB1053 + difference 3 5) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA1053 + difference 5 3) (sourceB1053 + difference 3 5) sourceC1053) = raw17305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17305; decide +kernel
    rw [ha]
    exact (canonical17305 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1053 + difference 5 4) (sourceB1053 + difference 4 5) sourceC1053) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA1053 + difference 5 4) (sourceB1053 + difference 4 5) sourceC1053) = raw17306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1053 sourceB1053 sourceC1053 difference raw17306; decide +kernel
    rw [ha]
    exact (canonical17306 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1053 sourceB1053 sourceC1053
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1053, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1054 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1054 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC1054 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceForm1054 : Integer.Sparse Master := [(Sum.inr 2621, 1), (Sum.inr 3115, 1), (Sum.inr 3790, 1), (Sum.inr 3825, 1), (Sum.inr 3876, 2), (Sum.inr 4091, -1)]

theorem sourceEq1054 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1054 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1054 + difference 0 1) (sourceB1054 + difference 1 0) sourceC1054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1054 + difference 0 1) (sourceB1054 + difference 1 0) sourceC1054) = raw17307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1054 sourceB1054 sourceC1054 difference raw17307; decide +kernel
    rw [ha]
    exact (canonical17307 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1054 + difference 1 1) (sourceB1054 + difference 1 1) sourceC1054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1054 + difference 1 1) (sourceB1054 + difference 1 1) sourceC1054) = raw17308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1054 sourceB1054 sourceC1054 difference raw17308; decide +kernel
    rw [ha]
    exact (canonical17308 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1054 + difference 2 1) (sourceB1054 + difference 1 2) sourceC1054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3790) := by
    have ha : (tripleCharges (sourceA1054 + difference 2 1) (sourceB1054 + difference 1 2) sourceC1054) = raw17309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1054 sourceB1054 sourceC1054 difference raw17309; decide +kernel
    rw [ha]
    exact (canonical17309 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1054 + difference 3 1) (sourceB1054 + difference 1 3) sourceC1054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3825) := by
    have ha : (tripleCharges (sourceA1054 + difference 3 1) (sourceB1054 + difference 1 3) sourceC1054) = raw17310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1054 sourceB1054 sourceC1054 difference raw17310; decide +kernel
    rw [ha]
    exact (canonical17310 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1054 + difference 4 1) (sourceB1054 + difference 1 4) sourceC1054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3115) := by
    have ha : (tripleCharges (sourceA1054 + difference 4 1) (sourceB1054 + difference 1 4) sourceC1054) = raw17311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1054 sourceB1054 sourceC1054 difference raw17311; decide +kernel
    rw [ha]
    exact (canonical17311 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1054 + difference 5 1) (sourceB1054 + difference 1 5) sourceC1054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2621) := by
    have ha : (tripleCharges (sourceA1054 + difference 5 1) (sourceB1054 + difference 1 5) sourceC1054) = raw17312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1054 sourceB1054 sourceC1054 difference raw17312; decide +kernel
    rw [ha]
    exact (canonical17312 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1054 + sourceB1054) sourceC1054) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1054 + sourceB1054) sourceC1054) = raw17313 := by
      apply Matrix.ext; unfold doubleCharges sourceA1054 sourceB1054 sourceC1054 raw17313; decide +kernel
    rw [ha]
    exact (canonical17313 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1054 sourceB1054 sourceC1054
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1054, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1055 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1055 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1055 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceForm1055 : Integer.Sparse Master := [(Sum.inr 4826, 1), (Sum.inr 4827, 1), (Sum.inr 4828, 1), (Sum.inr 4839, 1), (Sum.inr 4866, 1), (Sum.inr 5070, 1), (Sum.inr 5080, 1), (Sum.inr 5095, 1), (Sum.inr 5291, 1), (Sum.inr 5349, 1), (Sum.inr 5355, 1), (Sum.inr 5363, 1), (Sum.inr 5364, 1), (Sum.inr 5370, 1), (Sum.inr 5380, 1), (Sum.inr 5388, 1), (Sum.inr 5397, 1), (Sum.inr 5401, 1), (Sum.inr 5431, 1), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 1), (Sum.inr 5438, 1), (Sum.inr 5443, 1), (Sum.inr 5450, 1), (Sum.inr 5451, 1), (Sum.inr 5481, 1), (Sum.inr 5484, 1), (Sum.inr 5490, 1), (Sum.inr 5492, 1)]

theorem sourceEq1055 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1055 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1055 + difference 0 1) (sourceB1055 + difference 1 0) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1055 + difference 0 1) (sourceB1055 + difference 1 0) sourceC1055) = raw17314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17314; decide +kernel
    rw [ha]
    exact (canonical17314 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1055 + difference 0 2) (sourceB1055 + difference 2 0) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1055 + difference 0 2) (sourceB1055 + difference 2 0) sourceC1055) = raw17315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17315; decide +kernel
    rw [ha]
    exact (canonical17315 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1055 + difference 0 3) (sourceB1055 + difference 3 0) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1055 + difference 0 3) (sourceB1055 + difference 3 0) sourceC1055) = raw17316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17316; decide +kernel
    rw [ha]
    exact (canonical17316 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1055 + difference 0 4) (sourceB1055 + difference 4 0) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1055 + difference 0 4) (sourceB1055 + difference 4 0) sourceC1055) = raw17317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17317; decide +kernel
    rw [ha]
    exact (canonical17317 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1055 + difference 0 5) (sourceB1055 + difference 5 0) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1055 + difference 0 5) (sourceB1055 + difference 5 0) sourceC1055) = raw17318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17318; decide +kernel
    rw [ha]
    exact (canonical17318 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1055 + difference 1 0) (sourceB1055 + difference 0 1) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA1055 + difference 1 0) (sourceB1055 + difference 0 1) sourceC1055) = raw17319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17319; decide +kernel
    rw [ha]
    exact (canonical17319 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1055 + difference 1 2) (sourceB1055 + difference 2 1) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1055 + difference 1 2) (sourceB1055 + difference 2 1) sourceC1055) = raw17320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17320; decide +kernel
    rw [ha]
    exact (canonical17320 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1055 + difference 1 3) (sourceB1055 + difference 3 1) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1055 + difference 1 3) (sourceB1055 + difference 3 1) sourceC1055) = raw17321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17321; decide +kernel
    rw [ha]
    exact (canonical17321 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1055 + difference 1 4) (sourceB1055 + difference 4 1) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1055 + difference 1 4) (sourceB1055 + difference 4 1) sourceC1055) = raw17322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17322; decide +kernel
    rw [ha]
    exact (canonical17322 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1055 + difference 1 5) (sourceB1055 + difference 5 1) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1055 + difference 1 5) (sourceB1055 + difference 5 1) sourceC1055) = raw17323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17323; decide +kernel
    rw [ha]
    exact (canonical17323 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1055 + difference 2 0) (sourceB1055 + difference 0 2) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA1055 + difference 2 0) (sourceB1055 + difference 0 2) sourceC1055) = raw17324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17324; decide +kernel
    rw [ha]
    exact (canonical17324 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1055 + difference 2 1) (sourceB1055 + difference 1 2) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5364) := by
    have ha : (tripleCharges (sourceA1055 + difference 2 1) (sourceB1055 + difference 1 2) sourceC1055) = raw17325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17325; decide +kernel
    rw [ha]
    exact (canonical17325 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1055 + difference 2 3) (sourceB1055 + difference 3 2) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5363) := by
    have ha : (tripleCharges (sourceA1055 + difference 2 3) (sourceB1055 + difference 3 2) sourceC1055) = raw17326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17326; decide +kernel
    rw [ha]
    exact (canonical17326 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1055 + difference 2 4) (sourceB1055 + difference 4 2) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA1055 + difference 2 4) (sourceB1055 + difference 4 2) sourceC1055) = raw17327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17327; decide +kernel
    rw [ha]
    exact (canonical17327 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1055 + difference 2 5) (sourceB1055 + difference 5 2) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1055 + difference 2 5) (sourceB1055 + difference 5 2) sourceC1055) = raw17328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17328; decide +kernel
    rw [ha]
    exact (canonical17328 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1055 + difference 3 0) (sourceB1055 + difference 0 3) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA1055 + difference 3 0) (sourceB1055 + difference 0 3) sourceC1055) = raw17329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17329; decide +kernel
    rw [ha]
    exact (canonical17329 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1055 + difference 3 1) (sourceB1055 + difference 1 3) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA1055 + difference 3 1) (sourceB1055 + difference 1 3) sourceC1055) = raw17330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17330; decide +kernel
    rw [ha]
    exact (canonical17330 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1055 + difference 3 2) (sourceB1055 + difference 2 3) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1055 + difference 3 2) (sourceB1055 + difference 2 3) sourceC1055) = raw17331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17331; decide +kernel
    rw [ha]
    exact (canonical17331 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1055 + difference 3 4) (sourceB1055 + difference 4 3) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1055 + difference 3 4) (sourceB1055 + difference 4 3) sourceC1055) = raw17332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17332; decide +kernel
    rw [ha]
    exact (canonical17332 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1055 + difference 3 5) (sourceB1055 + difference 5 3) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA1055 + difference 3 5) (sourceB1055 + difference 5 3) sourceC1055) = raw17333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17333; decide +kernel
    rw [ha]
    exact (canonical17333 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1055 + difference 4 0) (sourceB1055 + difference 0 4) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA1055 + difference 4 0) (sourceB1055 + difference 0 4) sourceC1055) = raw17334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17334; decide +kernel
    rw [ha]
    exact (canonical17334 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1055 + difference 4 1) (sourceB1055 + difference 1 4) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA1055 + difference 4 1) (sourceB1055 + difference 1 4) sourceC1055) = raw17335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17335; decide +kernel
    rw [ha]
    exact (canonical17335 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1055 + difference 4 2) (sourceB1055 + difference 2 4) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA1055 + difference 4 2) (sourceB1055 + difference 2 4) sourceC1055) = raw17336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17336; decide +kernel
    rw [ha]
    exact (canonical17336 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1055 + difference 4 3) (sourceB1055 + difference 3 4) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA1055 + difference 4 3) (sourceB1055 + difference 3 4) sourceC1055) = raw17337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17337; decide +kernel
    rw [ha]
    exact (canonical17337 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1055 + difference 4 5) (sourceB1055 + difference 5 4) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1055 + difference 4 5) (sourceB1055 + difference 5 4) sourceC1055) = raw17338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17338; decide +kernel
    rw [ha]
    exact (canonical17338 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1055 + difference 5 0) (sourceB1055 + difference 0 5) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA1055 + difference 5 0) (sourceB1055 + difference 0 5) sourceC1055) = raw17339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17339; decide +kernel
    rw [ha]
    exact (canonical17339 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1055 + difference 5 1) (sourceB1055 + difference 1 5) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA1055 + difference 5 1) (sourceB1055 + difference 1 5) sourceC1055) = raw17340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17340; decide +kernel
    rw [ha]
    exact (canonical17340 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1055 + difference 5 2) (sourceB1055 + difference 2 5) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA1055 + difference 5 2) (sourceB1055 + difference 2 5) sourceC1055) = raw17341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17341; decide +kernel
    rw [ha]
    exact (canonical17341 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1055 + difference 5 3) (sourceB1055 + difference 3 5) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA1055 + difference 5 3) (sourceB1055 + difference 3 5) sourceC1055) = raw17342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17342; decide +kernel
    rw [ha]
    exact (canonical17342 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1055 + difference 5 4) (sourceB1055 + difference 4 5) sourceC1055) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA1055 + difference 5 4) (sourceB1055 + difference 4 5) sourceC1055) = raw17343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1055 sourceB1055 sourceC1055 difference raw17343; decide +kernel
    rw [ha]
    exact (canonical17343 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1055 sourceB1055 sourceC1055
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1055, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
