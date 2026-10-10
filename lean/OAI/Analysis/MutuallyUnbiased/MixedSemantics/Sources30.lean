import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical114
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical115
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical117
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical118
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical122
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical123
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical124
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical125
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical126

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA960 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB960 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC960 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm960 : Integer.Sparse Master := [(Sum.inr 2614, 1), (Sum.inr 3043, 1), (Sum.inr 3786, 1), (Sum.inr 3850, 2), (Sum.inr 3874, 1), (Sum.inr 4092, -1)]

theorem sourceEq960 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm960 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA960 + difference 5 0) (sourceB960 + difference 0 5) sourceC960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2614) := by
    have ha : (tripleCharges (sourceA960 + difference 5 0) (sourceB960 + difference 0 5) sourceC960) = raw15755 := by
      apply Matrix.ext; unfold tripleCharges sourceA960 sourceB960 sourceC960 difference raw15755; decide +kernel
    rw [ha]
    exact (canonical15755 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA960 + difference 5 1) (sourceB960 + difference 1 5) sourceC960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3786) := by
    have ha : (tripleCharges (sourceA960 + difference 5 1) (sourceB960 + difference 1 5) sourceC960) = raw15751 := by
      apply Matrix.ext; unfold tripleCharges sourceA960 sourceB960 sourceC960 difference raw15751; decide +kernel
    rw [ha]
    exact (canonical15751 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA960 + difference 5 2) (sourceB960 + difference 2 5) sourceC960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA960 + difference 5 2) (sourceB960 + difference 2 5) sourceC960) = raw15756 := by
      apply Matrix.ext; unfold tripleCharges sourceA960 sourceB960 sourceC960 difference raw15756; decide +kernel
    rw [ha]
    exact (canonical15756 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA960 + difference 5 3) (sourceB960 + difference 3 5) sourceC960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA960 + difference 5 3) (sourceB960 + difference 3 5) sourceC960) = raw15757 := by
      apply Matrix.ext; unfold tripleCharges sourceA960 sourceB960 sourceC960 difference raw15757; decide +kernel
    rw [ha]
    exact (canonical15757 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA960 + difference 5 4) (sourceB960 + difference 4 5) sourceC960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3043) := by
    have ha : (tripleCharges (sourceA960 + difference 5 4) (sourceB960 + difference 4 5) sourceC960) = raw15754 := by
      apply Matrix.ext; unfold tripleCharges sourceA960 sourceB960 sourceC960 difference raw15754; decide +kernel
    rw [ha]
    exact (canonical15754 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA960 + difference 5 5) (sourceB960 + difference 5 5) sourceC960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA960 + difference 5 5) (sourceB960 + difference 5 5) sourceC960) = raw15737 := by
      apply Matrix.ext; unfold tripleCharges sourceA960 sourceB960 sourceC960 difference raw15737; decide +kernel
    rw [ha]
    exact (canonical15737 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA960 + sourceB960) sourceC960) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA960 + sourceB960) sourceC960) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA960 sourceB960 sourceC960 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA960 sourceB960 sourceC960
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm960, Integer.Sparse.eval]
  linarith only [hs]

def sourceA961 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB961 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC961 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceForm961 : Integer.Sparse Master := [(Sum.inr 4729, 1), (Sum.inr 4731, 1), (Sum.inr 4740, 2), (Sum.inr 4889, 1), (Sum.inr 5142, 1), (Sum.inr 5149, 2), (Sum.inr 5284, 1), (Sum.inr 5320, 1), (Sum.inr 5326, 2), (Sum.inr 5378, 2), (Sum.inr 5397, 2), (Sum.inr 5400, 1), (Sum.inr 5401, 2), (Sum.inr 5406, 1), (Sum.inr 5411, 2), (Sum.inr 5433, 2), (Sum.inr 5435, 2), (Sum.inr 5450, 1), (Sum.inr 5452, 1), (Sum.inr 5453, 1), (Sum.inr 5489, 1)]

theorem sourceEq961 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm961 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA961 + difference 0 1) (sourceB961 + difference 1 0) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA961 + difference 0 1) (sourceB961 + difference 1 0) sourceC961) = raw15758 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15758; decide +kernel
    rw [ha]
    exact (canonical15758 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA961 + difference 0 2) (sourceB961 + difference 2 0) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA961 + difference 0 2) (sourceB961 + difference 2 0) sourceC961) = raw15759 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15759; decide +kernel
    rw [ha]
    exact (canonical15759 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA961 + difference 0 3) (sourceB961 + difference 3 0) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA961 + difference 0 3) (sourceB961 + difference 3 0) sourceC961) = raw15760 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15760; decide +kernel
    rw [ha]
    exact (canonical15760 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA961 + difference 0 4) (sourceB961 + difference 4 0) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA961 + difference 0 4) (sourceB961 + difference 4 0) sourceC961) = raw15761 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15761; decide +kernel
    rw [ha]
    exact (canonical15761 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA961 + difference 0 5) (sourceB961 + difference 5 0) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA961 + difference 0 5) (sourceB961 + difference 5 0) sourceC961) = raw2939 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw2939; decide +kernel
    rw [ha]
    exact (canonical2939 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA961 + difference 1 0) (sourceB961 + difference 0 1) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA961 + difference 1 0) (sourceB961 + difference 0 1) sourceC961) = raw2964 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw2964; decide +kernel
    rw [ha]
    exact (canonical2964 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA961 + difference 1 2) (sourceB961 + difference 2 1) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA961 + difference 1 2) (sourceB961 + difference 2 1) sourceC961) = raw2966 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw2966; decide +kernel
    rw [ha]
    exact (canonical2966 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA961 + difference 1 3) (sourceB961 + difference 3 1) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA961 + difference 1 3) (sourceB961 + difference 3 1) sourceC961) = raw2967 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw2967; decide +kernel
    rw [ha]
    exact (canonical2967 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA961 + difference 1 4) (sourceB961 + difference 4 1) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA961 + difference 1 4) (sourceB961 + difference 4 1) sourceC961) = raw2968 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw2968; decide +kernel
    rw [ha]
    exact (canonical2968 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA961 + difference 1 5) (sourceB961 + difference 5 1) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA961 + difference 1 5) (sourceB961 + difference 5 1) sourceC961) = raw9084 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw9084; decide +kernel
    rw [ha]
    exact (canonical9084 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA961 + difference 2 0) (sourceB961 + difference 0 2) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA961 + difference 2 0) (sourceB961 + difference 0 2) sourceC961) = raw9090 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw9090; decide +kernel
    rw [ha]
    exact (canonical9090 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA961 + difference 2 1) (sourceB961 + difference 1 2) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA961 + difference 2 1) (sourceB961 + difference 1 2) sourceC961) = raw15762 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15762; decide +kernel
    rw [ha]
    exact (canonical15762 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA961 + difference 2 3) (sourceB961 + difference 3 2) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA961 + difference 2 3) (sourceB961 + difference 3 2) sourceC961) = raw15763 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15763; decide +kernel
    rw [ha]
    exact (canonical15763 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA961 + difference 2 4) (sourceB961 + difference 4 2) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA961 + difference 2 4) (sourceB961 + difference 4 2) sourceC961) = raw15764 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15764; decide +kernel
    rw [ha]
    exact (canonical15764 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA961 + difference 2 5) (sourceB961 + difference 5 2) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA961 + difference 2 5) (sourceB961 + difference 5 2) sourceC961) = raw2950 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw2950; decide +kernel
    rw [ha]
    exact (canonical2950 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA961 + difference 3 0) (sourceB961 + difference 0 3) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA961 + difference 3 0) (sourceB961 + difference 0 3) sourceC961) = raw9094 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw9094; decide +kernel
    rw [ha]
    exact (canonical9094 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA961 + difference 3 1) (sourceB961 + difference 1 3) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA961 + difference 3 1) (sourceB961 + difference 1 3) sourceC961) = raw15765 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15765; decide +kernel
    rw [ha]
    exact (canonical15765 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA961 + difference 3 2) (sourceB961 + difference 2 3) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA961 + difference 3 2) (sourceB961 + difference 2 3) sourceC961) = raw15766 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15766; decide +kernel
    rw [ha]
    exact (canonical15766 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA961 + difference 3 4) (sourceB961 + difference 4 3) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA961 + difference 3 4) (sourceB961 + difference 4 3) sourceC961) = raw15767 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15767; decide +kernel
    rw [ha]
    exact (canonical15767 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA961 + difference 3 5) (sourceB961 + difference 5 3) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA961 + difference 3 5) (sourceB961 + difference 5 3) sourceC961) = raw2955 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw2955; decide +kernel
    rw [ha]
    exact (canonical2955 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA961 + difference 4 0) (sourceB961 + difference 0 4) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5142) := by
    have ha : (tripleCharges (sourceA961 + difference 4 0) (sourceB961 + difference 0 4) sourceC961) = raw9098 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw9098; decide +kernel
    rw [ha]
    exact (canonical9098 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA961 + difference 4 1) (sourceB961 + difference 1 4) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5320) := by
    have ha : (tripleCharges (sourceA961 + difference 4 1) (sourceB961 + difference 1 4) sourceC961) = raw15768 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15768; decide +kernel
    rw [ha]
    exact (canonical15768 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA961 + difference 4 2) (sourceB961 + difference 2 4) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5326) := by
    have ha : (tripleCharges (sourceA961 + difference 4 2) (sourceB961 + difference 2 4) sourceC961) = raw15769 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15769; decide +kernel
    rw [ha]
    exact (canonical15769 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA961 + difference 4 3) (sourceB961 + difference 3 4) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5326) := by
    have ha : (tripleCharges (sourceA961 + difference 4 3) (sourceB961 + difference 3 4) sourceC961) = raw15770 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15770; decide +kernel
    rw [ha]
    exact (canonical15770 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA961 + difference 4 5) (sourceB961 + difference 5 4) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA961 + difference 4 5) (sourceB961 + difference 5 4) sourceC961) = raw2960 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw2960; decide +kernel
    rw [ha]
    exact (canonical2960 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA961 + difference 5 0) (sourceB961 + difference 0 5) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4729) := by
    have ha : (tripleCharges (sourceA961 + difference 5 0) (sourceB961 + difference 0 5) sourceC961) = raw9102 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw9102; decide +kernel
    rw [ha]
    exact (canonical9102 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA961 + difference 5 1) (sourceB961 + difference 1 5) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4731) := by
    have ha : (tripleCharges (sourceA961 + difference 5 1) (sourceB961 + difference 1 5) sourceC961) = raw15771 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15771; decide +kernel
    rw [ha]
    exact (canonical15771 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA961 + difference 5 2) (sourceB961 + difference 2 5) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA961 + difference 5 2) (sourceB961 + difference 2 5) sourceC961) = raw15772 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15772; decide +kernel
    rw [ha]
    exact (canonical15772 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA961 + difference 5 3) (sourceB961 + difference 3 5) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA961 + difference 5 3) (sourceB961 + difference 3 5) sourceC961) = raw15773 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15773; decide +kernel
    rw [ha]
    exact (canonical15773 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA961 + difference 5 4) (sourceB961 + difference 4 5) sourceC961) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA961 + difference 5 4) (sourceB961 + difference 4 5) sourceC961) = raw15774 := by
      apply Matrix.ext; unfold tripleCharges sourceA961 sourceB961 sourceC961 difference raw15774; decide +kernel
    rw [ha]
    exact (canonical15774 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA961 sourceB961 sourceC961
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm961, Integer.Sparse.eval]
  linarith only [hs]

def sourceA962 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB962 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC962 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceForm962 : Integer.Sparse Master := [(Sum.inr 1898, 1), (Sum.inr 1900, 1), (Sum.inr 1913, 2), (Sum.inr 2245, 1), (Sum.inr 2913, 1), (Sum.inr 2924, 2), (Sum.inr 3077, 1), (Sum.inr 3646, 1), (Sum.inr 3653, 2), (Sum.inr 3719, 2), (Sum.inr 3782, 2), (Sum.inr 3799, 1), (Sum.inr 3801, 1), (Sum.inr 3804, 2), (Sum.inr 3809, 2), (Sum.inr 3853, 2), (Sum.inr 3910, 1), (Sum.inr 3912, 1), (Sum.inr 4009, 1), (Sum.inr 4033, 2), (Sum.inr 4039, 1)]

theorem sourceEq962 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm962 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA962 + difference 0 1) (sourceB962 + difference 1 0) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA962 + difference 0 1) (sourceB962 + difference 1 0) sourceC962) = raw15775 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15775; decide +kernel
    rw [ha]
    exact (canonical15775 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA962 + difference 0 2) (sourceB962 + difference 2 0) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA962 + difference 0 2) (sourceB962 + difference 2 0) sourceC962) = raw15776 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15776; decide +kernel
    rw [ha]
    exact (canonical15776 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA962 + difference 0 3) (sourceB962 + difference 3 0) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA962 + difference 0 3) (sourceB962 + difference 3 0) sourceC962) = raw15777 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15777; decide +kernel
    rw [ha]
    exact (canonical15777 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA962 + difference 0 4) (sourceB962 + difference 4 0) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA962 + difference 0 4) (sourceB962 + difference 4 0) sourceC962) = raw15778 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15778; decide +kernel
    rw [ha]
    exact (canonical15778 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA962 + difference 0 5) (sourceB962 + difference 5 0) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4009) := by
    have ha : (tripleCharges (sourceA962 + difference 0 5) (sourceB962 + difference 5 0) sourceC962) = raw2969 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw2969; decide +kernel
    rw [ha]
    exact (canonical2969 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA962 + difference 1 0) (sourceB962 + difference 0 1) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA962 + difference 1 0) (sourceB962 + difference 0 1) sourceC962) = raw2994 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw2994; decide +kernel
    rw [ha]
    exact (canonical2994 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA962 + difference 1 2) (sourceB962 + difference 2 1) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA962 + difference 1 2) (sourceB962 + difference 2 1) sourceC962) = raw2996 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw2996; decide +kernel
    rw [ha]
    exact (canonical2996 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA962 + difference 1 3) (sourceB962 + difference 3 1) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA962 + difference 1 3) (sourceB962 + difference 3 1) sourceC962) = raw2997 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw2997; decide +kernel
    rw [ha]
    exact (canonical2997 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA962 + difference 1 4) (sourceB962 + difference 4 1) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3912) := by
    have ha : (tripleCharges (sourceA962 + difference 1 4) (sourceB962 + difference 4 1) sourceC962) = raw2998 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw2998; decide +kernel
    rw [ha]
    exact (canonical2998 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA962 + difference 1 5) (sourceB962 + difference 5 1) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4039) := by
    have ha : (tripleCharges (sourceA962 + difference 1 5) (sourceB962 + difference 5 1) sourceC962) = raw9106 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw9106; decide +kernel
    rw [ha]
    exact (canonical9106 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA962 + difference 2 0) (sourceB962 + difference 0 2) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA962 + difference 2 0) (sourceB962 + difference 0 2) sourceC962) = raw9112 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw9112; decide +kernel
    rw [ha]
    exact (canonical9112 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA962 + difference 2 1) (sourceB962 + difference 1 2) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA962 + difference 2 1) (sourceB962 + difference 1 2) sourceC962) = raw15779 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15779; decide +kernel
    rw [ha]
    exact (canonical15779 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA962 + difference 2 3) (sourceB962 + difference 3 2) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA962 + difference 2 3) (sourceB962 + difference 3 2) sourceC962) = raw15780 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15780; decide +kernel
    rw [ha]
    exact (canonical15780 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA962 + difference 2 4) (sourceB962 + difference 4 2) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA962 + difference 2 4) (sourceB962 + difference 4 2) sourceC962) = raw15781 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15781; decide +kernel
    rw [ha]
    exact (canonical15781 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA962 + difference 2 5) (sourceB962 + difference 5 2) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA962 + difference 2 5) (sourceB962 + difference 5 2) sourceC962) = raw2980 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw2980; decide +kernel
    rw [ha]
    exact (canonical2980 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA962 + difference 3 0) (sourceB962 + difference 0 3) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA962 + difference 3 0) (sourceB962 + difference 0 3) sourceC962) = raw9116 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw9116; decide +kernel
    rw [ha]
    exact (canonical9116 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA962 + difference 3 1) (sourceB962 + difference 1 3) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA962 + difference 3 1) (sourceB962 + difference 1 3) sourceC962) = raw15782 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15782; decide +kernel
    rw [ha]
    exact (canonical15782 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA962 + difference 3 2) (sourceB962 + difference 2 3) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA962 + difference 3 2) (sourceB962 + difference 2 3) sourceC962) = raw15783 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15783; decide +kernel
    rw [ha]
    exact (canonical15783 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA962 + difference 3 4) (sourceB962 + difference 4 3) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA962 + difference 3 4) (sourceB962 + difference 4 3) sourceC962) = raw15784 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15784; decide +kernel
    rw [ha]
    exact (canonical15784 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA962 + difference 3 5) (sourceB962 + difference 5 3) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA962 + difference 3 5) (sourceB962 + difference 5 3) sourceC962) = raw2985 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw2985; decide +kernel
    rw [ha]
    exact (canonical2985 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA962 + difference 4 0) (sourceB962 + difference 0 4) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2913) := by
    have ha : (tripleCharges (sourceA962 + difference 4 0) (sourceB962 + difference 0 4) sourceC962) = raw9120 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw9120; decide +kernel
    rw [ha]
    exact (canonical9120 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA962 + difference 4 1) (sourceB962 + difference 1 4) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3646) := by
    have ha : (tripleCharges (sourceA962 + difference 4 1) (sourceB962 + difference 1 4) sourceC962) = raw15785 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15785; decide +kernel
    rw [ha]
    exact (canonical15785 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA962 + difference 4 2) (sourceB962 + difference 2 4) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3653) := by
    have ha : (tripleCharges (sourceA962 + difference 4 2) (sourceB962 + difference 2 4) sourceC962) = raw15786 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15786; decide +kernel
    rw [ha]
    exact (canonical15786 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA962 + difference 4 3) (sourceB962 + difference 3 4) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3653) := by
    have ha : (tripleCharges (sourceA962 + difference 4 3) (sourceB962 + difference 3 4) sourceC962) = raw15787 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15787; decide +kernel
    rw [ha]
    exact (canonical15787 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA962 + difference 4 5) (sourceB962 + difference 5 4) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA962 + difference 4 5) (sourceB962 + difference 5 4) sourceC962) = raw2990 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw2990; decide +kernel
    rw [ha]
    exact (canonical2990 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA962 + difference 5 0) (sourceB962 + difference 0 5) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA962 + difference 5 0) (sourceB962 + difference 0 5) sourceC962) = raw9124 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw9124; decide +kernel
    rw [ha]
    exact (canonical9124 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA962 + difference 5 1) (sourceB962 + difference 1 5) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1900) := by
    have ha : (tripleCharges (sourceA962 + difference 5 1) (sourceB962 + difference 1 5) sourceC962) = raw15788 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15788; decide +kernel
    rw [ha]
    exact (canonical15788 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA962 + difference 5 2) (sourceB962 + difference 2 5) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1913) := by
    have ha : (tripleCharges (sourceA962 + difference 5 2) (sourceB962 + difference 2 5) sourceC962) = raw15789 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15789; decide +kernel
    rw [ha]
    exact (canonical15789 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA962 + difference 5 3) (sourceB962 + difference 3 5) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1913) := by
    have ha : (tripleCharges (sourceA962 + difference 5 3) (sourceB962 + difference 3 5) sourceC962) = raw15790 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15790; decide +kernel
    rw [ha]
    exact (canonical15790 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA962 + difference 5 4) (sourceB962 + difference 4 5) sourceC962) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA962 + difference 5 4) (sourceB962 + difference 4 5) sourceC962) = raw15791 := by
      apply Matrix.ext; unfold tripleCharges sourceA962 sourceB962 sourceC962 difference raw15791; decide +kernel
    rw [ha]
    exact (canonical15791 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA962 sourceB962 sourceC962
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm962, Integer.Sparse.eval]
  linarith only [hs]

def sourceA963 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB963 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC963 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceForm963 : Integer.Sparse Master := [(Sum.inr 4792, 1), (Sum.inr 4795, 1), (Sum.inr 4803, 2), (Sum.inr 4885, 1), (Sum.inr 5067, 1), (Sum.inr 5076, 2), (Sum.inr 5251, 1), (Sum.inr 5348, 1), (Sum.inr 5353, 2), (Sum.inr 5354, 2), (Sum.inr 5403, 2), (Sum.inr 5405, 1), (Sum.inr 5406, 2), (Sum.inr 5408, 2), (Sum.inr 5425, 2), (Sum.inr 5429, 1), (Sum.inr 5430, 2), (Sum.inr 5433, 1), (Sum.inr 5437, 1), (Sum.inr 5447, 1), (Sum.inr 5482, 1)]

theorem sourceEq963 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm963 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA963 + difference 0 1) (sourceB963 + difference 1 0) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA963 + difference 0 1) (sourceB963 + difference 1 0) sourceC963) = raw15792 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15792; decide +kernel
    rw [ha]
    exact (canonical15792 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA963 + difference 0 2) (sourceB963 + difference 2 0) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA963 + difference 0 2) (sourceB963 + difference 2 0) sourceC963) = raw15793 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15793; decide +kernel
    rw [ha]
    exact (canonical15793 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA963 + difference 0 3) (sourceB963 + difference 3 0) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA963 + difference 0 3) (sourceB963 + difference 3 0) sourceC963) = raw15794 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15794; decide +kernel
    rw [ha]
    exact (canonical15794 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA963 + difference 0 4) (sourceB963 + difference 4 0) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA963 + difference 0 4) (sourceB963 + difference 4 0) sourceC963) = raw15795 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15795; decide +kernel
    rw [ha]
    exact (canonical15795 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA963 + difference 0 5) (sourceB963 + difference 5 0) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA963 + difference 0 5) (sourceB963 + difference 5 0) sourceC963) = raw15796 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15796; decide +kernel
    rw [ha]
    exact (canonical15796 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA963 + difference 1 0) (sourceB963 + difference 0 1) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA963 + difference 1 0) (sourceB963 + difference 0 1) sourceC963) = raw15797 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15797; decide +kernel
    rw [ha]
    exact (canonical15797 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA963 + difference 1 2) (sourceB963 + difference 2 1) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA963 + difference 1 2) (sourceB963 + difference 2 1) sourceC963) = raw5541 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw5541; decide +kernel
    rw [ha]
    exact (canonical5541 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA963 + difference 1 3) (sourceB963 + difference 3 1) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA963 + difference 1 3) (sourceB963 + difference 3 1) sourceC963) = raw5542 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw5542; decide +kernel
    rw [ha]
    exact (canonical5542 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA963 + difference 1 4) (sourceB963 + difference 4 1) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA963 + difference 1 4) (sourceB963 + difference 4 1) sourceC963) = raw5543 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw5543; decide +kernel
    rw [ha]
    exact (canonical5543 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA963 + difference 1 5) (sourceB963 + difference 5 1) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA963 + difference 1 5) (sourceB963 + difference 5 1) sourceC963) = raw5544 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw5544; decide +kernel
    rw [ha]
    exact (canonical5544 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA963 + difference 2 0) (sourceB963 + difference 0 2) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA963 + difference 2 0) (sourceB963 + difference 0 2) sourceC963) = raw5551 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw5551; decide +kernel
    rw [ha]
    exact (canonical5551 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA963 + difference 2 1) (sourceB963 + difference 1 2) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA963 + difference 2 1) (sourceB963 + difference 1 2) sourceC963) = raw15798 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15798; decide +kernel
    rw [ha]
    exact (canonical15798 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA963 + difference 2 3) (sourceB963 + difference 3 2) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA963 + difference 2 3) (sourceB963 + difference 3 2) sourceC963) = raw15799 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15799; decide +kernel
    rw [ha]
    exact (canonical15799 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA963 + difference 2 4) (sourceB963 + difference 4 2) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA963 + difference 2 4) (sourceB963 + difference 4 2) sourceC963) = raw15800 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15800; decide +kernel
    rw [ha]
    exact (canonical15800 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA963 + difference 2 5) (sourceB963 + difference 5 2) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA963 + difference 2 5) (sourceB963 + difference 5 2) sourceC963) = raw15801 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15801; decide +kernel
    rw [ha]
    exact (canonical15801 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA963 + difference 3 0) (sourceB963 + difference 0 3) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA963 + difference 3 0) (sourceB963 + difference 0 3) sourceC963) = raw5556 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw5556; decide +kernel
    rw [ha]
    exact (canonical5556 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA963 + difference 3 1) (sourceB963 + difference 1 3) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA963 + difference 3 1) (sourceB963 + difference 1 3) sourceC963) = raw15802 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15802; decide +kernel
    rw [ha]
    exact (canonical15802 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA963 + difference 3 2) (sourceB963 + difference 2 3) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA963 + difference 3 2) (sourceB963 + difference 2 3) sourceC963) = raw15803 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15803; decide +kernel
    rw [ha]
    exact (canonical15803 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA963 + difference 3 4) (sourceB963 + difference 4 3) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA963 + difference 3 4) (sourceB963 + difference 4 3) sourceC963) = raw15804 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15804; decide +kernel
    rw [ha]
    exact (canonical15804 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA963 + difference 3 5) (sourceB963 + difference 5 3) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA963 + difference 3 5) (sourceB963 + difference 5 3) sourceC963) = raw15805 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15805; decide +kernel
    rw [ha]
    exact (canonical15805 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA963 + difference 4 0) (sourceB963 + difference 0 4) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA963 + difference 4 0) (sourceB963 + difference 0 4) sourceC963) = raw5561 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw5561; decide +kernel
    rw [ha]
    exact (canonical5561 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA963 + difference 4 1) (sourceB963 + difference 1 4) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5348) := by
    have ha : (tripleCharges (sourceA963 + difference 4 1) (sourceB963 + difference 1 4) sourceC963) = raw15806 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15806; decide +kernel
    rw [ha]
    exact (canonical15806 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA963 + difference 4 2) (sourceB963 + difference 2 4) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA963 + difference 4 2) (sourceB963 + difference 2 4) sourceC963) = raw15807 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15807; decide +kernel
    rw [ha]
    exact (canonical15807 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA963 + difference 4 3) (sourceB963 + difference 3 4) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA963 + difference 4 3) (sourceB963 + difference 3 4) sourceC963) = raw15808 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15808; decide +kernel
    rw [ha]
    exact (canonical15808 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA963 + difference 4 5) (sourceB963 + difference 5 4) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA963 + difference 4 5) (sourceB963 + difference 5 4) sourceC963) = raw15809 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15809; decide +kernel
    rw [ha]
    exact (canonical15809 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA963 + difference 5 0) (sourceB963 + difference 0 5) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA963 + difference 5 0) (sourceB963 + difference 0 5) sourceC963) = raw5566 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw5566; decide +kernel
    rw [ha]
    exact (canonical5566 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA963 + difference 5 1) (sourceB963 + difference 1 5) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA963 + difference 5 1) (sourceB963 + difference 1 5) sourceC963) = raw15810 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15810; decide +kernel
    rw [ha]
    exact (canonical15810 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA963 + difference 5 2) (sourceB963 + difference 2 5) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA963 + difference 5 2) (sourceB963 + difference 2 5) sourceC963) = raw15811 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15811; decide +kernel
    rw [ha]
    exact (canonical15811 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA963 + difference 5 3) (sourceB963 + difference 3 5) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA963 + difference 5 3) (sourceB963 + difference 3 5) sourceC963) = raw15812 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15812; decide +kernel
    rw [ha]
    exact (canonical15812 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA963 + difference 5 4) (sourceB963 + difference 4 5) sourceC963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA963 + difference 5 4) (sourceB963 + difference 4 5) sourceC963) = raw15813 := by
      apply Matrix.ext; unfold tripleCharges sourceA963 sourceB963 sourceC963 difference raw15813; decide +kernel
    rw [ha]
    exact (canonical15813 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA963 sourceB963 sourceC963
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm963, Integer.Sparse.eval]
  linarith only [hs]

def sourceA964 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB964 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC964 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceForm964 : Integer.Sparse Master := [(Sum.inr 2009, 1), (Sum.inr 2012, 1), (Sum.inr 2021, 2), (Sum.inr 2233, 1), (Sum.inr 2981, 1), (Sum.inr 2986, 2), (Sum.inr 3064, 1), (Sum.inr 3685, 1), (Sum.inr 3691, 2), (Sum.inr 3818, 2), (Sum.inr 3822, 2), (Sum.inr 3839, 2), (Sum.inr 3846, 1), (Sum.inr 3847, 2), (Sum.inr 3848, 2), (Sum.inr 3899, 1), (Sum.inr 3909, 1), (Sum.inr 3977, 1), (Sum.inr 3992, 1), (Sum.inr 4033, 1), (Sum.inr 4038, 2)]

theorem sourceEq964 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm964 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA964 + difference 0 1) (sourceB964 + difference 1 0) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA964 + difference 0 1) (sourceB964 + difference 1 0) sourceC964) = raw15814 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15814; decide +kernel
    rw [ha]
    exact (canonical15814 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA964 + difference 0 2) (sourceB964 + difference 2 0) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4038) := by
    have ha : (tripleCharges (sourceA964 + difference 0 2) (sourceB964 + difference 2 0) sourceC964) = raw15815 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15815; decide +kernel
    rw [ha]
    exact (canonical15815 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA964 + difference 0 3) (sourceB964 + difference 3 0) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4038) := by
    have ha : (tripleCharges (sourceA964 + difference 0 3) (sourceB964 + difference 3 0) sourceC964) = raw15816 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15816; decide +kernel
    rw [ha]
    exact (canonical15816 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA964 + difference 0 4) (sourceB964 + difference 4 0) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA964 + difference 0 4) (sourceB964 + difference 4 0) sourceC964) = raw15817 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15817; decide +kernel
    rw [ha]
    exact (canonical15817 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA964 + difference 0 5) (sourceB964 + difference 5 0) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3992) := by
    have ha : (tripleCharges (sourceA964 + difference 0 5) (sourceB964 + difference 5 0) sourceC964) = raw15818 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15818; decide +kernel
    rw [ha]
    exact (canonical15818 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA964 + difference 1 0) (sourceB964 + difference 0 1) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA964 + difference 1 0) (sourceB964 + difference 0 1) sourceC964) = raw15819 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15819; decide +kernel
    rw [ha]
    exact (canonical15819 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA964 + difference 1 2) (sourceB964 + difference 2 1) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA964 + difference 1 2) (sourceB964 + difference 2 1) sourceC964) = raw5571 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw5571; decide +kernel
    rw [ha]
    exact (canonical5571 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA964 + difference 1 3) (sourceB964 + difference 3 1) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA964 + difference 1 3) (sourceB964 + difference 3 1) sourceC964) = raw5572 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw5572; decide +kernel
    rw [ha]
    exact (canonical5572 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA964 + difference 1 4) (sourceB964 + difference 4 1) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA964 + difference 1 4) (sourceB964 + difference 4 1) sourceC964) = raw5573 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw5573; decide +kernel
    rw [ha]
    exact (canonical5573 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA964 + difference 1 5) (sourceB964 + difference 5 1) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA964 + difference 1 5) (sourceB964 + difference 5 1) sourceC964) = raw5574 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw5574; decide +kernel
    rw [ha]
    exact (canonical5574 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA964 + difference 2 0) (sourceB964 + difference 0 2) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA964 + difference 2 0) (sourceB964 + difference 0 2) sourceC964) = raw5581 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw5581; decide +kernel
    rw [ha]
    exact (canonical5581 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA964 + difference 2 1) (sourceB964 + difference 1 2) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA964 + difference 2 1) (sourceB964 + difference 1 2) sourceC964) = raw15820 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15820; decide +kernel
    rw [ha]
    exact (canonical15820 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA964 + difference 2 3) (sourceB964 + difference 3 2) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3822) := by
    have ha : (tripleCharges (sourceA964 + difference 2 3) (sourceB964 + difference 3 2) sourceC964) = raw15821 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15821; decide +kernel
    rw [ha]
    exact (canonical15821 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA964 + difference 2 4) (sourceB964 + difference 4 2) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA964 + difference 2 4) (sourceB964 + difference 4 2) sourceC964) = raw15822 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15822; decide +kernel
    rw [ha]
    exact (canonical15822 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA964 + difference 2 5) (sourceB964 + difference 5 2) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA964 + difference 2 5) (sourceB964 + difference 5 2) sourceC964) = raw15823 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15823; decide +kernel
    rw [ha]
    exact (canonical15823 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA964 + difference 3 0) (sourceB964 + difference 0 3) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA964 + difference 3 0) (sourceB964 + difference 0 3) sourceC964) = raw5586 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw5586; decide +kernel
    rw [ha]
    exact (canonical5586 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA964 + difference 3 1) (sourceB964 + difference 1 3) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA964 + difference 3 1) (sourceB964 + difference 1 3) sourceC964) = raw15824 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15824; decide +kernel
    rw [ha]
    exact (canonical15824 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA964 + difference 3 2) (sourceB964 + difference 2 3) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3822) := by
    have ha : (tripleCharges (sourceA964 + difference 3 2) (sourceB964 + difference 2 3) sourceC964) = raw15825 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15825; decide +kernel
    rw [ha]
    exact (canonical15825 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA964 + difference 3 4) (sourceB964 + difference 4 3) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA964 + difference 3 4) (sourceB964 + difference 4 3) sourceC964) = raw15826 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15826; decide +kernel
    rw [ha]
    exact (canonical15826 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA964 + difference 3 5) (sourceB964 + difference 5 3) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA964 + difference 3 5) (sourceB964 + difference 5 3) sourceC964) = raw15827 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15827; decide +kernel
    rw [ha]
    exact (canonical15827 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA964 + difference 4 0) (sourceB964 + difference 0 4) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA964 + difference 4 0) (sourceB964 + difference 0 4) sourceC964) = raw5591 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw5591; decide +kernel
    rw [ha]
    exact (canonical5591 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA964 + difference 4 1) (sourceB964 + difference 1 4) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3685) := by
    have ha : (tripleCharges (sourceA964 + difference 4 1) (sourceB964 + difference 1 4) sourceC964) = raw15828 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15828; decide +kernel
    rw [ha]
    exact (canonical15828 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA964 + difference 4 2) (sourceB964 + difference 2 4) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3818) := by
    have ha : (tripleCharges (sourceA964 + difference 4 2) (sourceB964 + difference 2 4) sourceC964) = raw15829 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15829; decide +kernel
    rw [ha]
    exact (canonical15829 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA964 + difference 4 3) (sourceB964 + difference 3 4) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3818) := by
    have ha : (tripleCharges (sourceA964 + difference 4 3) (sourceB964 + difference 3 4) sourceC964) = raw15830 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15830; decide +kernel
    rw [ha]
    exact (canonical15830 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA964 + difference 4 5) (sourceB964 + difference 5 4) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA964 + difference 4 5) (sourceB964 + difference 5 4) sourceC964) = raw15831 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15831; decide +kernel
    rw [ha]
    exact (canonical15831 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA964 + difference 5 0) (sourceB964 + difference 0 5) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA964 + difference 5 0) (sourceB964 + difference 0 5) sourceC964) = raw5596 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw5596; decide +kernel
    rw [ha]
    exact (canonical5596 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA964 + difference 5 1) (sourceB964 + difference 1 5) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2981) := by
    have ha : (tripleCharges (sourceA964 + difference 5 1) (sourceB964 + difference 1 5) sourceC964) = raw15832 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15832; decide +kernel
    rw [ha]
    exact (canonical15832 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA964 + difference 5 2) (sourceB964 + difference 2 5) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2986) := by
    have ha : (tripleCharges (sourceA964 + difference 5 2) (sourceB964 + difference 2 5) sourceC964) = raw15833 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15833; decide +kernel
    rw [ha]
    exact (canonical15833 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA964 + difference 5 3) (sourceB964 + difference 3 5) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2986) := by
    have ha : (tripleCharges (sourceA964 + difference 5 3) (sourceB964 + difference 3 5) sourceC964) = raw15834 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15834; decide +kernel
    rw [ha]
    exact (canonical15834 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA964 + difference 5 4) (sourceB964 + difference 4 5) sourceC964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA964 + difference 5 4) (sourceB964 + difference 4 5) sourceC964) = raw15835 := by
      apply Matrix.ext; unfold tripleCharges sourceA964 sourceB964 sourceC964 difference raw15835; decide +kernel
    rw [ha]
    exact (canonical15835 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA964 sourceB964 sourceC964
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm964, Integer.Sparse.eval]
  linarith only [hs]

def sourceA965 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB965 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC965 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceForm965 : Integer.Sparse Master := [(Sum.inr 2195, 2), (Sum.inr 2201, 1), (Sum.inr 2213, 1), (Sum.inr 2252, 1), (Sum.inr 3476, 1), (Sum.inr 3477, 2), (Sum.inr 3539, 1), (Sum.inr 3761, 2), (Sum.inr 3768, 1), (Sum.inr 3769, 2), (Sum.inr 3805, 1), (Sum.inr 3806, 2), (Sum.inr 3810, 2), (Sum.inr 3812, 2), (Sum.inr 3840, 2), (Sum.inr 3851, 1), (Sum.inr 3855, 1), (Sum.inr 3871, 2), (Sum.inr 3874, 1), (Sum.inr 3882, 1), (Sum.inr 3980, 1)]

theorem sourceEq965 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm965 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA965 + difference 0 1) (sourceB965 + difference 1 0) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA965 + difference 0 1) (sourceB965 + difference 1 0) sourceC965) = raw15836 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15836; decide +kernel
    rw [ha]
    exact (canonical15836 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA965 + difference 0 2) (sourceB965 + difference 2 0) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA965 + difference 0 2) (sourceB965 + difference 2 0) sourceC965) = raw15837 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15837; decide +kernel
    rw [ha]
    exact (canonical15837 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA965 + difference 0 3) (sourceB965 + difference 3 0) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA965 + difference 0 3) (sourceB965 + difference 3 0) sourceC965) = raw15838 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15838; decide +kernel
    rw [ha]
    exact (canonical15838 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA965 + difference 0 4) (sourceB965 + difference 4 0) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA965 + difference 0 4) (sourceB965 + difference 4 0) sourceC965) = raw15839 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15839; decide +kernel
    rw [ha]
    exact (canonical15839 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA965 + difference 0 5) (sourceB965 + difference 5 0) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA965 + difference 0 5) (sourceB965 + difference 5 0) sourceC965) = raw15840 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15840; decide +kernel
    rw [ha]
    exact (canonical15840 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA965 + difference 1 0) (sourceB965 + difference 0 1) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA965 + difference 1 0) (sourceB965 + difference 0 1) sourceC965) = raw15841 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15841; decide +kernel
    rw [ha]
    exact (canonical15841 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA965 + difference 1 2) (sourceB965 + difference 2 1) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA965 + difference 1 2) (sourceB965 + difference 2 1) sourceC965) = raw5601 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw5601; decide +kernel
    rw [ha]
    exact (canonical5601 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA965 + difference 1 3) (sourceB965 + difference 3 1) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA965 + difference 1 3) (sourceB965 + difference 3 1) sourceC965) = raw5602 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw5602; decide +kernel
    rw [ha]
    exact (canonical5602 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA965 + difference 1 4) (sourceB965 + difference 4 1) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3855) := by
    have ha : (tripleCharges (sourceA965 + difference 1 4) (sourceB965 + difference 4 1) sourceC965) = raw5603 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw5603; decide +kernel
    rw [ha]
    exact (canonical5603 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA965 + difference 1 5) (sourceB965 + difference 5 1) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3882) := by
    have ha : (tripleCharges (sourceA965 + difference 1 5) (sourceB965 + difference 5 1) sourceC965) = raw5604 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw5604; decide +kernel
    rw [ha]
    exact (canonical5604 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA965 + difference 2 0) (sourceB965 + difference 0 2) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA965 + difference 2 0) (sourceB965 + difference 0 2) sourceC965) = raw5611 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw5611; decide +kernel
    rw [ha]
    exact (canonical5611 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA965 + difference 2 1) (sourceB965 + difference 1 2) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA965 + difference 2 1) (sourceB965 + difference 1 2) sourceC965) = raw15842 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15842; decide +kernel
    rw [ha]
    exact (canonical15842 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA965 + difference 2 3) (sourceB965 + difference 3 2) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3810) := by
    have ha : (tripleCharges (sourceA965 + difference 2 3) (sourceB965 + difference 3 2) sourceC965) = raw15843 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15843; decide +kernel
    rw [ha]
    exact (canonical15843 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA965 + difference 2 4) (sourceB965 + difference 4 2) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA965 + difference 2 4) (sourceB965 + difference 4 2) sourceC965) = raw15844 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15844; decide +kernel
    rw [ha]
    exact (canonical15844 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA965 + difference 2 5) (sourceB965 + difference 5 2) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA965 + difference 2 5) (sourceB965 + difference 5 2) sourceC965) = raw15845 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15845; decide +kernel
    rw [ha]
    exact (canonical15845 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA965 + difference 3 0) (sourceB965 + difference 0 3) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA965 + difference 3 0) (sourceB965 + difference 0 3) sourceC965) = raw5616 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw5616; decide +kernel
    rw [ha]
    exact (canonical5616 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA965 + difference 3 1) (sourceB965 + difference 1 3) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA965 + difference 3 1) (sourceB965 + difference 1 3) sourceC965) = raw15846 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15846; decide +kernel
    rw [ha]
    exact (canonical15846 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA965 + difference 3 2) (sourceB965 + difference 2 3) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3810) := by
    have ha : (tripleCharges (sourceA965 + difference 3 2) (sourceB965 + difference 2 3) sourceC965) = raw15847 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15847; decide +kernel
    rw [ha]
    exact (canonical15847 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA965 + difference 3 4) (sourceB965 + difference 4 3) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA965 + difference 3 4) (sourceB965 + difference 4 3) sourceC965) = raw15848 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15848; decide +kernel
    rw [ha]
    exact (canonical15848 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA965 + difference 3 5) (sourceB965 + difference 5 3) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA965 + difference 3 5) (sourceB965 + difference 5 3) sourceC965) = raw15849 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15849; decide +kernel
    rw [ha]
    exact (canonical15849 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA965 + difference 4 0) (sourceB965 + difference 0 4) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA965 + difference 4 0) (sourceB965 + difference 0 4) sourceC965) = raw5621 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw5621; decide +kernel
    rw [ha]
    exact (canonical5621 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA965 + difference 4 1) (sourceB965 + difference 1 4) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3768) := by
    have ha : (tripleCharges (sourceA965 + difference 4 1) (sourceB965 + difference 1 4) sourceC965) = raw15850 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15850; decide +kernel
    rw [ha]
    exact (canonical15850 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA965 + difference 4 2) (sourceB965 + difference 2 4) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA965 + difference 4 2) (sourceB965 + difference 2 4) sourceC965) = raw15851 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15851; decide +kernel
    rw [ha]
    exact (canonical15851 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA965 + difference 4 3) (sourceB965 + difference 3 4) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA965 + difference 4 3) (sourceB965 + difference 3 4) sourceC965) = raw15852 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15852; decide +kernel
    rw [ha]
    exact (canonical15852 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA965 + difference 4 5) (sourceB965 + difference 5 4) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA965 + difference 4 5) (sourceB965 + difference 5 4) sourceC965) = raw15853 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15853; decide +kernel
    rw [ha]
    exact (canonical15853 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA965 + difference 5 0) (sourceB965 + difference 0 5) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA965 + difference 5 0) (sourceB965 + difference 0 5) sourceC965) = raw5626 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw5626; decide +kernel
    rw [ha]
    exact (canonical5626 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA965 + difference 5 1) (sourceB965 + difference 1 5) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA965 + difference 5 1) (sourceB965 + difference 1 5) sourceC965) = raw15854 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15854; decide +kernel
    rw [ha]
    exact (canonical15854 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA965 + difference 5 2) (sourceB965 + difference 2 5) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3477) := by
    have ha : (tripleCharges (sourceA965 + difference 5 2) (sourceB965 + difference 2 5) sourceC965) = raw15855 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15855; decide +kernel
    rw [ha]
    exact (canonical15855 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA965 + difference 5 3) (sourceB965 + difference 3 5) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3477) := by
    have ha : (tripleCharges (sourceA965 + difference 5 3) (sourceB965 + difference 3 5) sourceC965) = raw15856 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15856; decide +kernel
    rw [ha]
    exact (canonical15856 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA965 + difference 5 4) (sourceB965 + difference 4 5) sourceC965) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA965 + difference 5 4) (sourceB965 + difference 4 5) sourceC965) = raw15857 := by
      apply Matrix.ext; unfold tripleCharges sourceA965 sourceB965 sourceC965 difference raw15857; decide +kernel
    rw [ha]
    exact (canonical15857 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA965 sourceB965 sourceC965
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm965, Integer.Sparse.eval]
  linarith only [hs]

def sourceA966 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB966 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC966 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm966 : Integer.Sparse Master := [(Sum.inr 5085, 1), (Sum.inr 5086, 2), (Sum.inr 5098, 1), (Sum.inr 5254, 2), (Sum.inr 5256, 1), (Sum.inr 5265, 2), (Sum.inr 5286, 1), (Sum.inr 5359, 1), (Sum.inr 5360, 2), (Sum.inr 5365, 1), (Sum.inr 5405, 2), (Sum.inr 5406, 1), (Sum.inr 5407, 2), (Sum.inr 5410, 2), (Sum.inr 5411, 2), (Sum.inr 5412, 2), (Sum.inr 5429, 1), (Sum.inr 5434, 2), (Sum.inr 5435, 2)]

theorem sourceEq966 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm966 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA966 + difference 0 1) (sourceB966 + difference 1 0) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA966 + difference 0 1) (sourceB966 + difference 1 0) sourceC966) = raw15858 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15858; decide +kernel
    rw [ha]
    exact (canonical15858 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA966 + difference 0 2) (sourceB966 + difference 2 0) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA966 + difference 0 2) (sourceB966 + difference 2 0) sourceC966) = raw15117 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15117; decide +kernel
    rw [ha]
    exact (canonical15117 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA966 + difference 0 3) (sourceB966 + difference 3 0) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA966 + difference 0 3) (sourceB966 + difference 3 0) sourceC966) = raw15859 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15859; decide +kernel
    rw [ha]
    exact (canonical15859 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA966 + difference 0 4) (sourceB966 + difference 4 0) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA966 + difference 0 4) (sourceB966 + difference 4 0) sourceC966) = raw15667 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15667; decide +kernel
    rw [ha]
    exact (canonical15667 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA966 + difference 0 5) (sourceB966 + difference 5 0) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA966 + difference 0 5) (sourceB966 + difference 5 0) sourceC966) = raw15860 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15860; decide +kernel
    rw [ha]
    exact (canonical15860 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA966 + difference 1 0) (sourceB966 + difference 0 1) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA966 + difference 1 0) (sourceB966 + difference 0 1) sourceC966) = raw15861 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15861; decide +kernel
    rw [ha]
    exact (canonical15861 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA966 + difference 1 2) (sourceB966 + difference 2 1) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA966 + difference 1 2) (sourceB966 + difference 2 1) sourceC966) = raw15122 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15122; decide +kernel
    rw [ha]
    exact (canonical15122 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA966 + difference 1 3) (sourceB966 + difference 3 1) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA966 + difference 1 3) (sourceB966 + difference 3 1) sourceC966) = raw15862 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15862; decide +kernel
    rw [ha]
    exact (canonical15862 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA966 + difference 1 4) (sourceB966 + difference 4 1) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA966 + difference 1 4) (sourceB966 + difference 4 1) sourceC966) = raw15671 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15671; decide +kernel
    rw [ha]
    exact (canonical15671 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA966 + difference 1 5) (sourceB966 + difference 5 1) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA966 + difference 1 5) (sourceB966 + difference 5 1) sourceC966) = raw15863 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15863; decide +kernel
    rw [ha]
    exact (canonical15863 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA966 + difference 2 0) (sourceB966 + difference 0 2) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA966 + difference 2 0) (sourceB966 + difference 0 2) sourceC966) = raw15864 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15864; decide +kernel
    rw [ha]
    exact (canonical15864 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA966 + difference 2 1) (sourceB966 + difference 1 2) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5407) := by
    have ha : (tripleCharges (sourceA966 + difference 2 1) (sourceB966 + difference 1 2) sourceC966) = raw15865 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15865; decide +kernel
    rw [ha]
    exact (canonical15865 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA966 + difference 2 3) (sourceB966 + difference 3 2) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA966 + difference 2 3) (sourceB966 + difference 3 2) sourceC966) = raw15866 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15866; decide +kernel
    rw [ha]
    exact (canonical15866 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA966 + difference 2 4) (sourceB966 + difference 4 2) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA966 + difference 2 4) (sourceB966 + difference 4 2) sourceC966) = raw15676 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15676; decide +kernel
    rw [ha]
    exact (canonical15676 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA966 + difference 2 5) (sourceB966 + difference 5 2) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA966 + difference 2 5) (sourceB966 + difference 5 2) sourceC966) = raw15867 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15867; decide +kernel
    rw [ha]
    exact (canonical15867 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA966 + difference 3 0) (sourceB966 + difference 0 3) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA966 + difference 3 0) (sourceB966 + difference 0 3) sourceC966) = raw15868 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15868; decide +kernel
    rw [ha]
    exact (canonical15868 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA966 + difference 3 1) (sourceB966 + difference 1 3) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5407) := by
    have ha : (tripleCharges (sourceA966 + difference 3 1) (sourceB966 + difference 1 3) sourceC966) = raw15869 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15869; decide +kernel
    rw [ha]
    exact (canonical15869 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA966 + difference 3 2) (sourceB966 + difference 2 3) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA966 + difference 3 2) (sourceB966 + difference 2 3) sourceC966) = raw15132 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15132; decide +kernel
    rw [ha]
    exact (canonical15132 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA966 + difference 3 4) (sourceB966 + difference 4 3) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA966 + difference 3 4) (sourceB966 + difference 4 3) sourceC966) = raw15680 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15680; decide +kernel
    rw [ha]
    exact (canonical15680 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA966 + difference 3 5) (sourceB966 + difference 5 3) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA966 + difference 3 5) (sourceB966 + difference 5 3) sourceC966) = raw15870 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15870; decide +kernel
    rw [ha]
    exact (canonical15870 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA966 + difference 4 0) (sourceB966 + difference 0 4) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA966 + difference 4 0) (sourceB966 + difference 0 4) sourceC966) = raw15204 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15204; decide +kernel
    rw [ha]
    exact (canonical15204 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA966 + difference 4 1) (sourceB966 + difference 1 4) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA966 + difference 4 1) (sourceB966 + difference 1 4) sourceC966) = raw15205 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15205; decide +kernel
    rw [ha]
    exact (canonical15205 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA966 + difference 4 2) (sourceB966 + difference 2 4) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA966 + difference 4 2) (sourceB966 + difference 2 4) sourceC966) = raw14714 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw14714; decide +kernel
    rw [ha]
    exact (canonical14714 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA966 + difference 4 3) (sourceB966 + difference 3 4) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA966 + difference 4 3) (sourceB966 + difference 3 4) sourceC966) = raw14984 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw14984; decide +kernel
    rw [ha]
    exact (canonical14984 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA966 + difference 4 5) (sourceB966 + difference 5 4) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA966 + difference 4 5) (sourceB966 + difference 5 4) sourceC966) = raw15206 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15206; decide +kernel
    rw [ha]
    exact (canonical15206 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA966 + difference 5 0) (sourceB966 + difference 0 5) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA966 + difference 5 0) (sourceB966 + difference 0 5) sourceC966) = raw15123 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15123; decide +kernel
    rw [ha]
    exact (canonical15123 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA966 + difference 5 1) (sourceB966 + difference 1 5) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA966 + difference 5 1) (sourceB966 + difference 1 5) sourceC966) = raw15124 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15124; decide +kernel
    rw [ha]
    exact (canonical15124 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA966 + difference 5 2) (sourceB966 + difference 2 5) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA966 + difference 5 2) (sourceB966 + difference 2 5) sourceC966) = raw15210 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15210; decide +kernel
    rw [ha]
    exact (canonical15210 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA966 + difference 5 3) (sourceB966 + difference 3 5) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA966 + difference 5 3) (sourceB966 + difference 3 5) sourceC966) = raw15125 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15125; decide +kernel
    rw [ha]
    exact (canonical15125 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA966 + difference 5 4) (sourceB966 + difference 4 5) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA966 + difference 5 4) (sourceB966 + difference 4 5) sourceC966) = raw15126 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15126; decide +kernel
    rw [ha]
    exact (canonical15126 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA966 sourceB966 sourceC966
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm966, Integer.Sparse.eval]
  linarith only [hs]

def sourceA967 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB967 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC967 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm967 : Integer.Sparse Master := [(Sum.inr 2974, 2), (Sum.inr 2976, 1), (Sum.inr 2996, 1), (Sum.inr 3037, 1), (Sum.inr 3525, 1), (Sum.inr 3526, 1), (Sum.inr 3528, 2), (Sum.inr 3567, 1), (Sum.inr 3780, 2), (Sum.inr 3800, 1), (Sum.inr 3801, 1), (Sum.inr 3803, 2), (Sum.inr 3846, 1), (Sum.inr 3852, 2), (Sum.inr 3853, 2), (Sum.inr 3856, 2), (Sum.inr 3878, 1), (Sum.inr 3883, 2), (Sum.inr 3938, 1), (Sum.inr 3977, 1), (Sum.inr 3996, 2)]

theorem sourceEq967 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm967 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA967 + difference 0 1) (sourceB967 + difference 1 0) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA967 + difference 0 1) (sourceB967 + difference 1 0) sourceC967) = raw15871 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15871; decide +kernel
    rw [ha]
    exact (canonical15871 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA967 + difference 0 2) (sourceB967 + difference 2 0) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3996) := by
    have ha : (tripleCharges (sourceA967 + difference 0 2) (sourceB967 + difference 2 0) sourceC967) = raw15872 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15872; decide +kernel
    rw [ha]
    exact (canonical15872 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA967 + difference 0 3) (sourceB967 + difference 3 0) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3996) := by
    have ha : (tripleCharges (sourceA967 + difference 0 3) (sourceB967 + difference 3 0) sourceC967) = raw15873 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15873; decide +kernel
    rw [ha]
    exact (canonical15873 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA967 + difference 0 4) (sourceB967 + difference 4 0) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3938) := by
    have ha : (tripleCharges (sourceA967 + difference 0 4) (sourceB967 + difference 4 0) sourceC967) = raw15689 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15689; decide +kernel
    rw [ha]
    exact (canonical15689 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA967 + difference 0 5) (sourceB967 + difference 5 0) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2996) := by
    have ha : (tripleCharges (sourceA967 + difference 0 5) (sourceB967 + difference 5 0) sourceC967) = raw15874 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15874; decide +kernel
    rw [ha]
    exact (canonical15874 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA967 + difference 1 0) (sourceB967 + difference 0 1) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA967 + difference 1 0) (sourceB967 + difference 0 1) sourceC967) = raw15875 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15875; decide +kernel
    rw [ha]
    exact (canonical15875 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA967 + difference 1 2) (sourceB967 + difference 2 1) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA967 + difference 1 2) (sourceB967 + difference 2 1) sourceC967) = raw15876 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15876; decide +kernel
    rw [ha]
    exact (canonical15876 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA967 + difference 1 3) (sourceB967 + difference 3 1) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA967 + difference 1 3) (sourceB967 + difference 3 1) sourceC967) = raw15877 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15877; decide +kernel
    rw [ha]
    exact (canonical15877 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA967 + difference 1 4) (sourceB967 + difference 4 1) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3878) := by
    have ha : (tripleCharges (sourceA967 + difference 1 4) (sourceB967 + difference 4 1) sourceC967) = raw15694 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15694; decide +kernel
    rw [ha]
    exact (canonical15694 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA967 + difference 1 5) (sourceB967 + difference 5 1) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA967 + difference 1 5) (sourceB967 + difference 5 1) sourceC967) = raw15878 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15878; decide +kernel
    rw [ha]
    exact (canonical15878 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA967 + difference 2 0) (sourceB967 + difference 0 2) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA967 + difference 2 0) (sourceB967 + difference 0 2) sourceC967) = raw15879 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15879; decide +kernel
    rw [ha]
    exact (canonical15879 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA967 + difference 2 1) (sourceB967 + difference 1 2) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA967 + difference 2 1) (sourceB967 + difference 1 2) sourceC967) = raw15880 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15880; decide +kernel
    rw [ha]
    exact (canonical15880 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA967 + difference 2 3) (sourceB967 + difference 3 2) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3856) := by
    have ha : (tripleCharges (sourceA967 + difference 2 3) (sourceB967 + difference 3 2) sourceC967) = raw15881 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15881; decide +kernel
    rw [ha]
    exact (canonical15881 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA967 + difference 2 4) (sourceB967 + difference 4 2) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3780) := by
    have ha : (tripleCharges (sourceA967 + difference 2 4) (sourceB967 + difference 4 2) sourceC967) = raw15699 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15699; decide +kernel
    rw [ha]
    exact (canonical15699 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA967 + difference 2 5) (sourceB967 + difference 5 2) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA967 + difference 2 5) (sourceB967 + difference 5 2) sourceC967) = raw15882 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15882; decide +kernel
    rw [ha]
    exact (canonical15882 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA967 + difference 3 0) (sourceB967 + difference 0 3) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA967 + difference 3 0) (sourceB967 + difference 0 3) sourceC967) = raw15883 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15883; decide +kernel
    rw [ha]
    exact (canonical15883 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA967 + difference 3 1) (sourceB967 + difference 1 3) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA967 + difference 3 1) (sourceB967 + difference 1 3) sourceC967) = raw15884 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15884; decide +kernel
    rw [ha]
    exact (canonical15884 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA967 + difference 3 2) (sourceB967 + difference 2 3) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3856) := by
    have ha : (tripleCharges (sourceA967 + difference 3 2) (sourceB967 + difference 2 3) sourceC967) = raw15885 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15885; decide +kernel
    rw [ha]
    exact (canonical15885 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA967 + difference 3 4) (sourceB967 + difference 4 3) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3780) := by
    have ha : (tripleCharges (sourceA967 + difference 3 4) (sourceB967 + difference 4 3) sourceC967) = raw15704 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15704; decide +kernel
    rw [ha]
    exact (canonical15704 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA967 + difference 3 5) (sourceB967 + difference 5 3) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA967 + difference 3 5) (sourceB967 + difference 5 3) sourceC967) = raw15886 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15886; decide +kernel
    rw [ha]
    exact (canonical15886 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA967 + difference 4 0) (sourceB967 + difference 0 4) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA967 + difference 4 0) (sourceB967 + difference 0 4) sourceC967) = raw15887 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15887; decide +kernel
    rw [ha]
    exact (canonical15887 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA967 + difference 4 1) (sourceB967 + difference 1 4) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA967 + difference 4 1) (sourceB967 + difference 1 4) sourceC967) = raw15888 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15888; decide +kernel
    rw [ha]
    exact (canonical15888 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA967 + difference 4 2) (sourceB967 + difference 2 4) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA967 + difference 4 2) (sourceB967 + difference 2 4) sourceC967) = raw14744 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw14744; decide +kernel
    rw [ha]
    exact (canonical14744 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA967 + difference 4 3) (sourceB967 + difference 3 4) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA967 + difference 4 3) (sourceB967 + difference 3 4) sourceC967) = raw15889 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15889; decide +kernel
    rw [ha]
    exact (canonical15889 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA967 + difference 4 5) (sourceB967 + difference 5 4) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA967 + difference 4 5) (sourceB967 + difference 5 4) sourceC967) = raw15890 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15890; decide +kernel
    rw [ha]
    exact (canonical15890 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA967 + difference 5 0) (sourceB967 + difference 0 5) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA967 + difference 5 0) (sourceB967 + difference 0 5) sourceC967) = raw15705 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15705; decide +kernel
    rw [ha]
    exact (canonical15705 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA967 + difference 5 1) (sourceB967 + difference 1 5) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA967 + difference 5 1) (sourceB967 + difference 1 5) sourceC967) = raw15706 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15706; decide +kernel
    rw [ha]
    exact (canonical15706 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA967 + difference 5 2) (sourceB967 + difference 2 5) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA967 + difference 5 2) (sourceB967 + difference 2 5) sourceC967) = raw15707 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15707; decide +kernel
    rw [ha]
    exact (canonical15707 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA967 + difference 5 3) (sourceB967 + difference 3 5) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA967 + difference 5 3) (sourceB967 + difference 3 5) sourceC967) = raw15708 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15708; decide +kernel
    rw [ha]
    exact (canonical15708 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA967 + difference 5 4) (sourceB967 + difference 4 5) sourceC967) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA967 + difference 5 4) (sourceB967 + difference 4 5) sourceC967) = raw15891 := by
      apply Matrix.ext; unfold tripleCharges sourceA967 sourceB967 sourceC967 difference raw15891; decide +kernel
    rw [ha]
    exact (canonical15891 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA967 sourceB967 sourceC967
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm967, Integer.Sparse.eval]
  linarith only [hs]

def sourceA968 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB968 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC968 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm968 : Integer.Sparse Master := [(Sum.inr 3016, 2), (Sum.inr 3023, 1), (Sum.inr 3037, 1), (Sum.inr 3085, 1), (Sum.inr 3460, 1), (Sum.inr 3461, 1), (Sum.inr 3464, 2), (Sum.inr 3526, 1), (Sum.inr 3758, 1), (Sum.inr 3759, 1), (Sum.inr 3762, 2), (Sum.inr 3800, 1), (Sum.inr 3803, 2), (Sum.inr 3808, 2), (Sum.inr 3809, 2), (Sum.inr 3814, 2), (Sum.inr 3847, 1), (Sum.inr 3853, 2), (Sum.inr 3954, 1), (Sum.inr 3977, 1), (Sum.inr 3982, 2)]

theorem sourceEq968 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm968 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA968 + difference 0 1) (sourceB968 + difference 1 0) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA968 + difference 0 1) (sourceB968 + difference 1 0) sourceC968) = raw15892 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15892; decide +kernel
    rw [ha]
    exact (canonical15892 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA968 + difference 0 2) (sourceB968 + difference 2 0) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA968 + difference 0 2) (sourceB968 + difference 2 0) sourceC968) = raw15144 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15144; decide +kernel
    rw [ha]
    exact (canonical15144 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA968 + difference 0 3) (sourceB968 + difference 3 0) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA968 + difference 0 3) (sourceB968 + difference 3 0) sourceC968) = raw15893 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15893; decide +kernel
    rw [ha]
    exact (canonical15893 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA968 + difference 0 4) (sourceB968 + difference 4 0) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA968 + difference 0 4) (sourceB968 + difference 4 0) sourceC968) = raw15718 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15718; decide +kernel
    rw [ha]
    exact (canonical15718 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA968 + difference 0 5) (sourceB968 + difference 5 0) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA968 + difference 0 5) (sourceB968 + difference 5 0) sourceC968) = raw15894 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15894; decide +kernel
    rw [ha]
    exact (canonical15894 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA968 + difference 1 0) (sourceB968 + difference 0 1) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA968 + difference 1 0) (sourceB968 + difference 0 1) sourceC968) = raw15895 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15895; decide +kernel
    rw [ha]
    exact (canonical15895 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA968 + difference 1 2) (sourceB968 + difference 2 1) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA968 + difference 1 2) (sourceB968 + difference 2 1) sourceC968) = raw15149 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15149; decide +kernel
    rw [ha]
    exact (canonical15149 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA968 + difference 1 3) (sourceB968 + difference 3 1) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA968 + difference 1 3) (sourceB968 + difference 3 1) sourceC968) = raw15896 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15896; decide +kernel
    rw [ha]
    exact (canonical15896 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA968 + difference 1 4) (sourceB968 + difference 4 1) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3759) := by
    have ha : (tripleCharges (sourceA968 + difference 1 4) (sourceB968 + difference 4 1) sourceC968) = raw15722 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15722; decide +kernel
    rw [ha]
    exact (canonical15722 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA968 + difference 1 5) (sourceB968 + difference 5 1) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA968 + difference 1 5) (sourceB968 + difference 5 1) sourceC968) = raw15897 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15897; decide +kernel
    rw [ha]
    exact (canonical15897 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA968 + difference 2 0) (sourceB968 + difference 0 2) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA968 + difference 2 0) (sourceB968 + difference 0 2) sourceC968) = raw15898 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15898; decide +kernel
    rw [ha]
    exact (canonical15898 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA968 + difference 2 1) (sourceB968 + difference 1 2) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA968 + difference 2 1) (sourceB968 + difference 1 2) sourceC968) = raw15899 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15899; decide +kernel
    rw [ha]
    exact (canonical15899 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA968 + difference 2 3) (sourceB968 + difference 3 2) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA968 + difference 2 3) (sourceB968 + difference 3 2) sourceC968) = raw15900 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15900; decide +kernel
    rw [ha]
    exact (canonical15900 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA968 + difference 2 4) (sourceB968 + difference 4 2) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA968 + difference 2 4) (sourceB968 + difference 4 2) sourceC968) = raw15727 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15727; decide +kernel
    rw [ha]
    exact (canonical15727 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA968 + difference 2 5) (sourceB968 + difference 5 2) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA968 + difference 2 5) (sourceB968 + difference 5 2) sourceC968) = raw15901 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15901; decide +kernel
    rw [ha]
    exact (canonical15901 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA968 + difference 3 0) (sourceB968 + difference 0 3) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA968 + difference 3 0) (sourceB968 + difference 0 3) sourceC968) = raw15902 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15902; decide +kernel
    rw [ha]
    exact (canonical15902 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA968 + difference 3 1) (sourceB968 + difference 1 3) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA968 + difference 3 1) (sourceB968 + difference 1 3) sourceC968) = raw15903 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15903; decide +kernel
    rw [ha]
    exact (canonical15903 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA968 + difference 3 2) (sourceB968 + difference 2 3) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA968 + difference 3 2) (sourceB968 + difference 2 3) sourceC968) = raw15159 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15159; decide +kernel
    rw [ha]
    exact (canonical15159 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA968 + difference 3 4) (sourceB968 + difference 4 3) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA968 + difference 3 4) (sourceB968 + difference 4 3) sourceC968) = raw15731 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15731; decide +kernel
    rw [ha]
    exact (canonical15731 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA968 + difference 3 5) (sourceB968 + difference 5 3) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA968 + difference 3 5) (sourceB968 + difference 5 3) sourceC968) = raw15904 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15904; decide +kernel
    rw [ha]
    exact (canonical15904 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA968 + difference 4 0) (sourceB968 + difference 0 4) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA968 + difference 4 0) (sourceB968 + difference 0 4) sourceC968) = raw15905 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15905; decide +kernel
    rw [ha]
    exact (canonical15905 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA968 + difference 4 1) (sourceB968 + difference 1 4) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA968 + difference 4 1) (sourceB968 + difference 1 4) sourceC968) = raw15906 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15906; decide +kernel
    rw [ha]
    exact (canonical15906 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA968 + difference 4 2) (sourceB968 + difference 2 4) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA968 + difference 4 2) (sourceB968 + difference 2 4) sourceC968) = raw14774 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw14774; decide +kernel
    rw [ha]
    exact (canonical14774 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA968 + difference 4 3) (sourceB968 + difference 3 4) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA968 + difference 4 3) (sourceB968 + difference 3 4) sourceC968) = raw15006 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15006; decide +kernel
    rw [ha]
    exact (canonical15006 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA968 + difference 4 5) (sourceB968 + difference 5 4) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA968 + difference 4 5) (sourceB968 + difference 5 4) sourceC968) = raw15907 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15907; decide +kernel
    rw [ha]
    exact (canonical15907 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA968 + difference 5 0) (sourceB968 + difference 0 5) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA968 + difference 5 0) (sourceB968 + difference 0 5) sourceC968) = raw15150 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15150; decide +kernel
    rw [ha]
    exact (canonical15150 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA968 + difference 5 1) (sourceB968 + difference 1 5) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA968 + difference 5 1) (sourceB968 + difference 1 5) sourceC968) = raw15151 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15151; decide +kernel
    rw [ha]
    exact (canonical15151 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA968 + difference 5 2) (sourceB968 + difference 2 5) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA968 + difference 5 2) (sourceB968 + difference 2 5) sourceC968) = raw15732 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15732; decide +kernel
    rw [ha]
    exact (canonical15732 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA968 + difference 5 3) (sourceB968 + difference 3 5) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA968 + difference 5 3) (sourceB968 + difference 3 5) sourceC968) = raw15152 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15152; decide +kernel
    rw [ha]
    exact (canonical15152 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA968 + difference 5 4) (sourceB968 + difference 4 5) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA968 + difference 5 4) (sourceB968 + difference 4 5) sourceC968) = raw15153 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15153; decide +kernel
    rw [ha]
    exact (canonical15153 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA968 sourceB968 sourceC968
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm968, Integer.Sparse.eval]
  linarith only [hs]

def sourceA969 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB969 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC969 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm969 : Integer.Sparse Master := [(Sum.inr 2508, 1), (Sum.inr 3703, 1), (Sum.inr 3805, 1), (Sum.inr 3812, 1), (Sum.inr 3816, 2), (Sum.inr 4092, -1)]

theorem sourceEq969 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm969 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA969 + difference 0 0) (sourceB969 + difference 0 0) sourceC969) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA969 + difference 0 0) (sourceB969 + difference 0 0) sourceC969) = raw15908 := by
      apply Matrix.ext; unfold tripleCharges sourceA969 sourceB969 sourceC969 difference raw15908; decide +kernel
    rw [ha]
    exact (canonical15908 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA969 + difference 0 1) (sourceB969 + difference 1 0) sourceC969) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA969 + difference 0 1) (sourceB969 + difference 1 0) sourceC969) = raw15909 := by
      apply Matrix.ext; unfold tripleCharges sourceA969 sourceB969 sourceC969 difference raw15909; decide +kernel
    rw [ha]
    exact (canonical15909 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA969 + difference 0 2) (sourceB969 + difference 2 0) sourceC969) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA969 + difference 0 2) (sourceB969 + difference 2 0) sourceC969) = raw15910 := by
      apply Matrix.ext; unfold tripleCharges sourceA969 sourceB969 sourceC969 difference raw15910; decide +kernel
    rw [ha]
    exact (canonical15910 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA969 + difference 0 3) (sourceB969 + difference 3 0) sourceC969) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA969 + difference 0 3) (sourceB969 + difference 3 0) sourceC969) = raw15911 := by
      apply Matrix.ext; unfold tripleCharges sourceA969 sourceB969 sourceC969 difference raw15911; decide +kernel
    rw [ha]
    exact (canonical15911 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA969 + difference 0 4) (sourceB969 + difference 4 0) sourceC969) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3703) := by
    have ha : (tripleCharges (sourceA969 + difference 0 4) (sourceB969 + difference 4 0) sourceC969) = raw15742 := by
      apply Matrix.ext; unfold tripleCharges sourceA969 sourceB969 sourceC969 difference raw15742; decide +kernel
    rw [ha]
    exact (canonical15742 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA969 + difference 0 5) (sourceB969 + difference 5 0) sourceC969) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA969 + difference 0 5) (sourceB969 + difference 5 0) sourceC969) = raw15912 := by
      apply Matrix.ext; unfold tripleCharges sourceA969 sourceB969 sourceC969 difference raw15912; decide +kernel
    rw [ha]
    exact (canonical15912 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA969 + sourceB969) sourceC969) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA969 + sourceB969) sourceC969) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA969 sourceB969 sourceC969 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA969 sourceB969 sourceC969
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm969, Integer.Sparse.eval]
  linarith only [hs]

def sourceA970 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB970 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC970 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceForm970 : Integer.Sparse Master := [(Sum.inr 5048, 1), (Sum.inr 5049, 1), (Sum.inr 5061, 1), (Sum.inr 5074, 1), (Sum.inr 5122, 1), (Sum.inr 5124, 1), (Sum.inr 5160, 1), (Sum.inr 5182, 1), (Sum.inr 5185, 1), (Sum.inr 5190, 1), (Sum.inr 5226, 1), (Sum.inr 5250, 1), (Sum.inr 5260, 1), (Sum.inr 5347, 1), (Sum.inr 5353, 1), (Sum.inr 5401, 1), (Sum.inr 5405, 1), (Sum.inr 5425, 1), (Sum.inr 5430, 1), (Sum.inr 5431, 1), (Sum.inr 5433, 1), (Sum.inr 5438, 1), (Sum.inr 5439, 1), (Sum.inr 5444, 1), (Sum.inr 5445, 1), (Sum.inr 5446, 1), (Sum.inr 5461, 1), (Sum.inr 5478, 1), (Sum.inr 5480, 1), (Sum.inr 5484, 1)]

theorem sourceEq970 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm970 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA970 + difference 0 1) (sourceB970 + difference 1 0) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA970 + difference 0 1) (sourceB970 + difference 1 0) sourceC970) = raw15913 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15913; decide +kernel
    rw [ha]
    exact (canonical15913 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA970 + difference 0 2) (sourceB970 + difference 2 0) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA970 + difference 0 2) (sourceB970 + difference 2 0) sourceC970) = raw15914 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15914; decide +kernel
    rw [ha]
    exact (canonical15914 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA970 + difference 0 3) (sourceB970 + difference 3 0) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5461) := by
    have ha : (tripleCharges (sourceA970 + difference 0 3) (sourceB970 + difference 3 0) sourceC970) = raw15915 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15915; decide +kernel
    rw [ha]
    exact (canonical15915 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA970 + difference 0 4) (sourceB970 + difference 4 0) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA970 + difference 0 4) (sourceB970 + difference 4 0) sourceC970) = raw15916 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15916; decide +kernel
    rw [ha]
    exact (canonical15916 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA970 + difference 0 5) (sourceB970 + difference 5 0) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA970 + difference 0 5) (sourceB970 + difference 5 0) sourceC970) = raw15917 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15917; decide +kernel
    rw [ha]
    exact (canonical15917 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA970 + difference 1 0) (sourceB970 + difference 0 1) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA970 + difference 1 0) (sourceB970 + difference 0 1) sourceC970) = raw15918 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15918; decide +kernel
    rw [ha]
    exact (canonical15918 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA970 + difference 1 2) (sourceB970 + difference 2 1) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA970 + difference 1 2) (sourceB970 + difference 2 1) sourceC970) = raw15919 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15919; decide +kernel
    rw [ha]
    exact (canonical15919 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA970 + difference 1 3) (sourceB970 + difference 3 1) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA970 + difference 1 3) (sourceB970 + difference 3 1) sourceC970) = raw15920 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15920; decide +kernel
    rw [ha]
    exact (canonical15920 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA970 + difference 1 4) (sourceB970 + difference 4 1) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA970 + difference 1 4) (sourceB970 + difference 4 1) sourceC970) = raw15921 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15921; decide +kernel
    rw [ha]
    exact (canonical15921 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA970 + difference 1 5) (sourceB970 + difference 5 1) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA970 + difference 1 5) (sourceB970 + difference 5 1) sourceC970) = raw15922 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15922; decide +kernel
    rw [ha]
    exact (canonical15922 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA970 + difference 2 0) (sourceB970 + difference 0 2) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5190) := by
    have ha : (tripleCharges (sourceA970 + difference 2 0) (sourceB970 + difference 0 2) sourceC970) = raw15923 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15923; decide +kernel
    rw [ha]
    exact (canonical15923 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA970 + difference 2 1) (sourceB970 + difference 1 2) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5124) := by
    have ha : (tripleCharges (sourceA970 + difference 2 1) (sourceB970 + difference 1 2) sourceC970) = raw15924 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15924; decide +kernel
    rw [ha]
    exact (canonical15924 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA970 + difference 2 3) (sourceB970 + difference 3 2) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5444) := by
    have ha : (tripleCharges (sourceA970 + difference 2 3) (sourceB970 + difference 3 2) sourceC970) = raw15925 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15925; decide +kernel
    rw [ha]
    exact (canonical15925 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA970 + difference 2 4) (sourceB970 + difference 4 2) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA970 + difference 2 4) (sourceB970 + difference 4 2) sourceC970) = raw15926 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15926; decide +kernel
    rw [ha]
    exact (canonical15926 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA970 + difference 2 5) (sourceB970 + difference 5 2) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA970 + difference 2 5) (sourceB970 + difference 5 2) sourceC970) = raw15927 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15927; decide +kernel
    rw [ha]
    exact (canonical15927 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA970 + difference 3 0) (sourceB970 + difference 0 3) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA970 + difference 3 0) (sourceB970 + difference 0 3) sourceC970) = raw15928 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15928; decide +kernel
    rw [ha]
    exact (canonical15928 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA970 + difference 3 1) (sourceB970 + difference 1 3) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA970 + difference 3 1) (sourceB970 + difference 1 3) sourceC970) = raw15929 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15929; decide +kernel
    rw [ha]
    exact (canonical15929 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA970 + difference 3 2) (sourceB970 + difference 2 3) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA970 + difference 3 2) (sourceB970 + difference 2 3) sourceC970) = raw15930 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15930; decide +kernel
    rw [ha]
    exact (canonical15930 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA970 + difference 3 4) (sourceB970 + difference 4 3) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA970 + difference 3 4) (sourceB970 + difference 4 3) sourceC970) = raw15931 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15931; decide +kernel
    rw [ha]
    exact (canonical15931 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA970 + difference 3 5) (sourceB970 + difference 5 3) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA970 + difference 3 5) (sourceB970 + difference 5 3) sourceC970) = raw15932 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15932; decide +kernel
    rw [ha]
    exact (canonical15932 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA970 + difference 4 0) (sourceB970 + difference 0 4) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5182) := by
    have ha : (tripleCharges (sourceA970 + difference 4 0) (sourceB970 + difference 0 4) sourceC970) = raw15933 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15933; decide +kernel
    rw [ha]
    exact (canonical15933 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA970 + difference 4 1) (sourceB970 + difference 1 4) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5122) := by
    have ha : (tripleCharges (sourceA970 + difference 4 1) (sourceB970 + difference 1 4) sourceC970) = raw15934 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15934; decide +kernel
    rw [ha]
    exact (canonical15934 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA970 + difference 4 2) (sourceB970 + difference 2 4) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA970 + difference 4 2) (sourceB970 + difference 2 4) sourceC970) = raw15935 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15935; decide +kernel
    rw [ha]
    exact (canonical15935 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA970 + difference 4 3) (sourceB970 + difference 3 4) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5347) := by
    have ha : (tripleCharges (sourceA970 + difference 4 3) (sourceB970 + difference 3 4) sourceC970) = raw15936 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15936; decide +kernel
    rw [ha]
    exact (canonical15936 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA970 + difference 4 5) (sourceB970 + difference 5 4) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA970 + difference 4 5) (sourceB970 + difference 5 4) sourceC970) = raw15937 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15937; decide +kernel
    rw [ha]
    exact (canonical15937 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA970 + difference 5 0) (sourceB970 + difference 0 5) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5048) := by
    have ha : (tripleCharges (sourceA970 + difference 5 0) (sourceB970 + difference 0 5) sourceC970) = raw15938 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15938; decide +kernel
    rw [ha]
    exact (canonical15938 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA970 + difference 5 1) (sourceB970 + difference 1 5) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5049) := by
    have ha : (tripleCharges (sourceA970 + difference 5 1) (sourceB970 + difference 1 5) sourceC970) = raw15939 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15939; decide +kernel
    rw [ha]
    exact (canonical15939 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA970 + difference 5 2) (sourceB970 + difference 2 5) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA970 + difference 5 2) (sourceB970 + difference 2 5) sourceC970) = raw15940 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15940; decide +kernel
    rw [ha]
    exact (canonical15940 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA970 + difference 5 3) (sourceB970 + difference 3 5) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5061) := by
    have ha : (tripleCharges (sourceA970 + difference 5 3) (sourceB970 + difference 3 5) sourceC970) = raw15941 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15941; decide +kernel
    rw [ha]
    exact (canonical15941 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA970 + difference 5 4) (sourceB970 + difference 4 5) sourceC970) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA970 + difference 5 4) (sourceB970 + difference 4 5) sourceC970) = raw15942 := by
      apply Matrix.ext; unfold tripleCharges sourceA970 sourceB970 sourceC970 difference raw15942; decide +kernel
    rw [ha]
    exact (canonical15942 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA970 sourceB970 sourceC970
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm970, Integer.Sparse.eval]
  linarith only [hs]

def sourceA971 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB971 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC971 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceForm971 : Integer.Sparse Master := [(Sum.inr 2450, 1), (Sum.inr 2451, 1), (Sum.inr 2464, 1), (Sum.inr 2481, 1), (Sum.inr 2724, 1), (Sum.inr 2850, 1), (Sum.inr 2854, 1), (Sum.inr 2862, 1), (Sum.inr 3065, 1), (Sum.inr 3367, 1), (Sum.inr 3371, 1), (Sum.inr 3376, 1), (Sum.inr 3558, 1), (Sum.inr 3684, 1), (Sum.inr 3691, 1), (Sum.inr 3839, 1), (Sum.inr 3943, 1), (Sum.inr 3959, 1), (Sum.inr 3966, 1), (Sum.inr 3972, 1), (Sum.inr 3973, 1), (Sum.inr 3974, 1), (Sum.inr 3977, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 1), (Sum.inr 3993, 1), (Sum.inr 4012, 1), (Sum.inr 4024, 1), (Sum.inr 4026, 1), (Sum.inr 4033, 1)]

theorem sourceEq971 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm971 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA971 + difference 0 1) (sourceB971 + difference 1 0) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA971 + difference 0 1) (sourceB971 + difference 1 0) sourceC971) = raw15943 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15943; decide +kernel
    rw [ha]
    exact (canonical15943 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA971 + difference 0 2) (sourceB971 + difference 2 0) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA971 + difference 0 2) (sourceB971 + difference 2 0) sourceC971) = raw15944 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15944; decide +kernel
    rw [ha]
    exact (canonical15944 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA971 + difference 0 3) (sourceB971 + difference 3 0) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3973) := by
    have ha : (tripleCharges (sourceA971 + difference 0 3) (sourceB971 + difference 3 0) sourceC971) = raw15945 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15945; decide +kernel
    rw [ha]
    exact (canonical15945 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA971 + difference 0 4) (sourceB971 + difference 4 0) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA971 + difference 0 4) (sourceB971 + difference 4 0) sourceC971) = raw15946 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15946; decide +kernel
    rw [ha]
    exact (canonical15946 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA971 + difference 0 5) (sourceB971 + difference 5 0) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA971 + difference 0 5) (sourceB971 + difference 5 0) sourceC971) = raw15947 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15947; decide +kernel
    rw [ha]
    exact (canonical15947 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA971 + difference 1 0) (sourceB971 + difference 0 1) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA971 + difference 1 0) (sourceB971 + difference 0 1) sourceC971) = raw15948 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15948; decide +kernel
    rw [ha]
    exact (canonical15948 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA971 + difference 1 2) (sourceB971 + difference 2 1) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA971 + difference 1 2) (sourceB971 + difference 2 1) sourceC971) = raw15949 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15949; decide +kernel
    rw [ha]
    exact (canonical15949 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA971 + difference 1 3) (sourceB971 + difference 3 1) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA971 + difference 1 3) (sourceB971 + difference 3 1) sourceC971) = raw15950 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15950; decide +kernel
    rw [ha]
    exact (canonical15950 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA971 + difference 1 4) (sourceB971 + difference 4 1) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA971 + difference 1 4) (sourceB971 + difference 4 1) sourceC971) = raw15951 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15951; decide +kernel
    rw [ha]
    exact (canonical15951 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA971 + difference 1 5) (sourceB971 + difference 5 1) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA971 + difference 1 5) (sourceB971 + difference 5 1) sourceC971) = raw15952 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15952; decide +kernel
    rw [ha]
    exact (canonical15952 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA971 + difference 2 0) (sourceB971 + difference 0 2) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2854) := by
    have ha : (tripleCharges (sourceA971 + difference 2 0) (sourceB971 + difference 0 2) sourceC971) = raw15953 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15953; decide +kernel
    rw [ha]
    exact (canonical15953 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA971 + difference 2 1) (sourceB971 + difference 1 2) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3371) := by
    have ha : (tripleCharges (sourceA971 + difference 2 1) (sourceB971 + difference 1 2) sourceC971) = raw15954 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15954; decide +kernel
    rw [ha]
    exact (canonical15954 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA971 + difference 2 3) (sourceB971 + difference 3 2) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3943) := by
    have ha : (tripleCharges (sourceA971 + difference 2 3) (sourceB971 + difference 3 2) sourceC971) = raw15955 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15955; decide +kernel
    rw [ha]
    exact (canonical15955 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA971 + difference 2 4) (sourceB971 + difference 4 2) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA971 + difference 2 4) (sourceB971 + difference 4 2) sourceC971) = raw15956 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15956; decide +kernel
    rw [ha]
    exact (canonical15956 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA971 + difference 2 5) (sourceB971 + difference 5 2) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA971 + difference 2 5) (sourceB971 + difference 5 2) sourceC971) = raw15957 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15957; decide +kernel
    rw [ha]
    exact (canonical15957 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA971 + difference 3 0) (sourceB971 + difference 0 3) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA971 + difference 3 0) (sourceB971 + difference 0 3) sourceC971) = raw15958 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15958; decide +kernel
    rw [ha]
    exact (canonical15958 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA971 + difference 3 1) (sourceB971 + difference 1 3) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA971 + difference 3 1) (sourceB971 + difference 1 3) sourceC971) = raw15959 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15959; decide +kernel
    rw [ha]
    exact (canonical15959 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA971 + difference 3 2) (sourceB971 + difference 2 3) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3966) := by
    have ha : (tripleCharges (sourceA971 + difference 3 2) (sourceB971 + difference 2 3) sourceC971) = raw15960 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15960; decide +kernel
    rw [ha]
    exact (canonical15960 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA971 + difference 3 4) (sourceB971 + difference 4 3) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA971 + difference 3 4) (sourceB971 + difference 4 3) sourceC971) = raw15961 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15961; decide +kernel
    rw [ha]
    exact (canonical15961 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA971 + difference 3 5) (sourceB971 + difference 5 3) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA971 + difference 3 5) (sourceB971 + difference 5 3) sourceC971) = raw15962 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15962; decide +kernel
    rw [ha]
    exact (canonical15962 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA971 + difference 4 0) (sourceB971 + difference 0 4) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2850) := by
    have ha : (tripleCharges (sourceA971 + difference 4 0) (sourceB971 + difference 0 4) sourceC971) = raw15963 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15963; decide +kernel
    rw [ha]
    exact (canonical15963 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA971 + difference 4 1) (sourceB971 + difference 1 4) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3367) := by
    have ha : (tripleCharges (sourceA971 + difference 4 1) (sourceB971 + difference 1 4) sourceC971) = raw15964 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15964; decide +kernel
    rw [ha]
    exact (canonical15964 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA971 + difference 4 2) (sourceB971 + difference 2 4) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA971 + difference 4 2) (sourceB971 + difference 2 4) sourceC971) = raw15965 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15965; decide +kernel
    rw [ha]
    exact (canonical15965 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA971 + difference 4 3) (sourceB971 + difference 3 4) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3684) := by
    have ha : (tripleCharges (sourceA971 + difference 4 3) (sourceB971 + difference 3 4) sourceC971) = raw15966 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15966; decide +kernel
    rw [ha]
    exact (canonical15966 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA971 + difference 4 5) (sourceB971 + difference 5 4) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA971 + difference 4 5) (sourceB971 + difference 5 4) sourceC971) = raw15967 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15967; decide +kernel
    rw [ha]
    exact (canonical15967 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA971 + difference 5 0) (sourceB971 + difference 0 5) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2450) := by
    have ha : (tripleCharges (sourceA971 + difference 5 0) (sourceB971 + difference 0 5) sourceC971) = raw15968 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15968; decide +kernel
    rw [ha]
    exact (canonical15968 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA971 + difference 5 1) (sourceB971 + difference 1 5) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2451) := by
    have ha : (tripleCharges (sourceA971 + difference 5 1) (sourceB971 + difference 1 5) sourceC971) = raw15969 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15969; decide +kernel
    rw [ha]
    exact (canonical15969 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA971 + difference 5 2) (sourceB971 + difference 2 5) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA971 + difference 5 2) (sourceB971 + difference 2 5) sourceC971) = raw15970 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15970; decide +kernel
    rw [ha]
    exact (canonical15970 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA971 + difference 5 3) (sourceB971 + difference 3 5) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2464) := by
    have ha : (tripleCharges (sourceA971 + difference 5 3) (sourceB971 + difference 3 5) sourceC971) = raw15971 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15971; decide +kernel
    rw [ha]
    exact (canonical15971 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA971 + difference 5 4) (sourceB971 + difference 4 5) sourceC971) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA971 + difference 5 4) (sourceB971 + difference 4 5) sourceC971) = raw15972 := by
      apply Matrix.ext; unfold tripleCharges sourceA971 sourceB971 sourceC971 difference raw15972; decide +kernel
    rw [ha]
    exact (canonical15972 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA971 sourceB971 sourceC971
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm971, Integer.Sparse.eval]
  linarith only [hs]

def sourceA972 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB972 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC972 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceForm972 : Integer.Sparse Master := [(Sum.inr 2534, 1), (Sum.inr 2535, 1), (Sum.inr 2537, 1), (Sum.inr 2587, 1), (Sum.inr 2669, 1), (Sum.inr 3431, 1), (Sum.inr 3434, 1), (Sum.inr 3463, 1), (Sum.inr 3529, 1), (Sum.inr 3531, 1), (Sum.inr 3536, 1), (Sum.inr 3540, 1), (Sum.inr 3568, 1), (Sum.inr 3743, 1), (Sum.inr 3761, 1), (Sum.inr 3804, 1), (Sum.inr 3805, 1), (Sum.inr 3840, 1), (Sum.inr 3848, 1), (Sum.inr 3849, 1), (Sum.inr 3851, 1), (Sum.inr 3857, 1), (Sum.inr 3858, 1), (Sum.inr 3879, 1), (Sum.inr 3880, 1), (Sum.inr 3884, 1), (Sum.inr 3927, 1), (Sum.inr 3978, 1), (Sum.inr 3994, 1), (Sum.inr 3997, 1)]

theorem sourceEq972 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm972 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA972 + difference 0 1) (sourceB972 + difference 1 0) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2587) := by
    have ha : (tripleCharges (sourceA972 + difference 0 1) (sourceB972 + difference 1 0) sourceC972) = raw15973 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15973; decide +kernel
    rw [ha]
    exact (canonical15973 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA972 + difference 0 2) (sourceB972 + difference 2 0) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA972 + difference 0 2) (sourceB972 + difference 2 0) sourceC972) = raw15974 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15974; decide +kernel
    rw [ha]
    exact (canonical15974 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA972 + difference 0 3) (sourceB972 + difference 3 0) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3927) := by
    have ha : (tripleCharges (sourceA972 + difference 0 3) (sourceB972 + difference 3 0) sourceC972) = raw15975 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15975; decide +kernel
    rw [ha]
    exact (canonical15975 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA972 + difference 0 4) (sourceB972 + difference 4 0) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3997) := by
    have ha : (tripleCharges (sourceA972 + difference 0 4) (sourceB972 + difference 4 0) sourceC972) = raw15976 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15976; decide +kernel
    rw [ha]
    exact (canonical15976 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA972 + difference 0 5) (sourceB972 + difference 5 0) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3994) := by
    have ha : (tripleCharges (sourceA972 + difference 0 5) (sourceB972 + difference 5 0) sourceC972) = raw15977 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15977; decide +kernel
    rw [ha]
    exact (canonical15977 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA972 + difference 1 0) (sourceB972 + difference 0 1) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA972 + difference 1 0) (sourceB972 + difference 0 1) sourceC972) = raw15978 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15978; decide +kernel
    rw [ha]
    exact (canonical15978 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA972 + difference 1 2) (sourceB972 + difference 2 1) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA972 + difference 1 2) (sourceB972 + difference 2 1) sourceC972) = raw15979 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15979; decide +kernel
    rw [ha]
    exact (canonical15979 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA972 + difference 1 3) (sourceB972 + difference 3 1) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA972 + difference 1 3) (sourceB972 + difference 3 1) sourceC972) = raw15980 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15980; decide +kernel
    rw [ha]
    exact (canonical15980 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA972 + difference 1 4) (sourceB972 + difference 4 1) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA972 + difference 1 4) (sourceB972 + difference 4 1) sourceC972) = raw15981 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15981; decide +kernel
    rw [ha]
    exact (canonical15981 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA972 + difference 1 5) (sourceB972 + difference 5 1) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA972 + difference 1 5) (sourceB972 + difference 5 1) sourceC972) = raw15982 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15982; decide +kernel
    rw [ha]
    exact (canonical15982 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA972 + difference 2 0) (sourceB972 + difference 0 2) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3568) := by
    have ha : (tripleCharges (sourceA972 + difference 2 0) (sourceB972 + difference 0 2) sourceC972) = raw15983 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15983; decide +kernel
    rw [ha]
    exact (canonical15983 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA972 + difference 2 1) (sourceB972 + difference 1 2) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2537) := by
    have ha : (tripleCharges (sourceA972 + difference 2 1) (sourceB972 + difference 1 2) sourceC972) = raw15984 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15984; decide +kernel
    rw [ha]
    exact (canonical15984 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA972 + difference 2 3) (sourceB972 + difference 3 2) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3879) := by
    have ha : (tripleCharges (sourceA972 + difference 2 3) (sourceB972 + difference 3 2) sourceC972) = raw15985 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15985; decide +kernel
    rw [ha]
    exact (canonical15985 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA972 + difference 2 4) (sourceB972 + difference 4 2) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA972 + difference 2 4) (sourceB972 + difference 4 2) sourceC972) = raw15986 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15986; decide +kernel
    rw [ha]
    exact (canonical15986 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA972 + difference 2 5) (sourceB972 + difference 5 2) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA972 + difference 2 5) (sourceB972 + difference 5 2) sourceC972) = raw15987 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15987; decide +kernel
    rw [ha]
    exact (canonical15987 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA972 + difference 3 0) (sourceB972 + difference 0 3) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA972 + difference 3 0) (sourceB972 + difference 0 3) sourceC972) = raw15988 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15988; decide +kernel
    rw [ha]
    exact (canonical15988 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA972 + difference 3 1) (sourceB972 + difference 1 3) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA972 + difference 3 1) (sourceB972 + difference 1 3) sourceC972) = raw15989 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15989; decide +kernel
    rw [ha]
    exact (canonical15989 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA972 + difference 3 2) (sourceB972 + difference 2 3) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA972 + difference 3 2) (sourceB972 + difference 2 3) sourceC972) = raw15990 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15990; decide +kernel
    rw [ha]
    exact (canonical15990 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA972 + difference 3 4) (sourceB972 + difference 4 3) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA972 + difference 3 4) (sourceB972 + difference 4 3) sourceC972) = raw15991 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15991; decide +kernel
    rw [ha]
    exact (canonical15991 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA972 + difference 3 5) (sourceB972 + difference 5 3) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA972 + difference 3 5) (sourceB972 + difference 5 3) sourceC972) = raw15992 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15992; decide +kernel
    rw [ha]
    exact (canonical15992 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA972 + difference 4 0) (sourceB972 + difference 0 4) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3536) := by
    have ha : (tripleCharges (sourceA972 + difference 4 0) (sourceB972 + difference 0 4) sourceC972) = raw15993 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15993; decide +kernel
    rw [ha]
    exact (canonical15993 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA972 + difference 4 1) (sourceB972 + difference 1 4) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2535) := by
    have ha : (tripleCharges (sourceA972 + difference 4 1) (sourceB972 + difference 1 4) sourceC972) = raw15994 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15994; decide +kernel
    rw [ha]
    exact (canonical15994 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA972 + difference 4 2) (sourceB972 + difference 2 4) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA972 + difference 4 2) (sourceB972 + difference 2 4) sourceC972) = raw15995 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15995; decide +kernel
    rw [ha]
    exact (canonical15995 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA972 + difference 4 3) (sourceB972 + difference 3 4) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3743) := by
    have ha : (tripleCharges (sourceA972 + difference 4 3) (sourceB972 + difference 3 4) sourceC972) = raw15996 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15996; decide +kernel
    rw [ha]
    exact (canonical15996 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA972 + difference 4 5) (sourceB972 + difference 5 4) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA972 + difference 4 5) (sourceB972 + difference 5 4) sourceC972) = raw15997 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15997; decide +kernel
    rw [ha]
    exact (canonical15997 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA972 + difference 5 0) (sourceB972 + difference 0 5) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3434) := by
    have ha : (tripleCharges (sourceA972 + difference 5 0) (sourceB972 + difference 0 5) sourceC972) = raw15998 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15998; decide +kernel
    rw [ha]
    exact (canonical15998 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA972 + difference 5 1) (sourceB972 + difference 1 5) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2534) := by
    have ha : (tripleCharges (sourceA972 + difference 5 1) (sourceB972 + difference 1 5) sourceC972) = raw15999 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw15999; decide +kernel
    rw [ha]
    exact (canonical15999 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA972 + difference 5 2) (sourceB972 + difference 2 5) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA972 + difference 5 2) (sourceB972 + difference 2 5) sourceC972) = raw16000 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw16000; decide +kernel
    rw [ha]
    exact (canonical16000 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA972 + difference 5 3) (sourceB972 + difference 3 5) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3431) := by
    have ha : (tripleCharges (sourceA972 + difference 5 3) (sourceB972 + difference 3 5) sourceC972) = raw16001 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw16001; decide +kernel
    rw [ha]
    exact (canonical16001 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA972 + difference 5 4) (sourceB972 + difference 4 5) sourceC972) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA972 + difference 5 4) (sourceB972 + difference 4 5) sourceC972) = raw16002 := by
      apply Matrix.ext; unfold tripleCharges sourceA972 sourceB972 sourceC972 difference raw16002; decide +kernel
    rw [ha]
    exact (canonical16002 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA972 sourceB972 sourceC972
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm972, Integer.Sparse.eval]
  linarith only [hs]

def sourceA973 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB973 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC973 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceForm973 : Integer.Sparse Master := [(Sum.inr 2951, 1), (Sum.inr 3871, 1), (Sum.inr 3927, 1), (Sum.inr 3974, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

theorem sourceEq973 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm973 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA973 + difference 0 0) (sourceB973 + difference 0 0) sourceC973) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA973 + difference 0 0) (sourceB973 + difference 0 0) sourceC973) = raw16003 := by
      apply Matrix.ext; unfold tripleCharges sourceA973 sourceB973 sourceC973 difference raw16003; decide +kernel
    rw [ha]
    exact (canonical16003 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA973 + difference 0 1) (sourceB973 + difference 1 0) sourceC973) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA973 + difference 0 1) (sourceB973 + difference 1 0) sourceC973) = raw16004 := by
      apply Matrix.ext; unfold tripleCharges sourceA973 sourceB973 sourceC973 difference raw16004; decide +kernel
    rw [ha]
    exact (canonical16004 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA973 + difference 0 2) (sourceB973 + difference 2 0) sourceC973) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA973 + difference 0 2) (sourceB973 + difference 2 0) sourceC973) = raw16005 := by
      apply Matrix.ext; unfold tripleCharges sourceA973 sourceB973 sourceC973 difference raw16005; decide +kernel
    rw [ha]
    exact (canonical16005 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA973 + difference 0 3) (sourceB973 + difference 3 0) sourceC973) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3927) := by
    have ha : (tripleCharges (sourceA973 + difference 0 3) (sourceB973 + difference 3 0) sourceC973) = raw16006 := by
      apply Matrix.ext; unfold tripleCharges sourceA973 sourceB973 sourceC973 difference raw16006; decide +kernel
    rw [ha]
    exact (canonical16006 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA973 + difference 0 4) (sourceB973 + difference 4 0) sourceC973) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA973 + difference 0 4) (sourceB973 + difference 4 0) sourceC973) = raw16007 := by
      apply Matrix.ext; unfold tripleCharges sourceA973 sourceB973 sourceC973 difference raw16007; decide +kernel
    rw [ha]
    exact (canonical16007 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA973 + difference 0 5) (sourceB973 + difference 5 0) sourceC973) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA973 + difference 0 5) (sourceB973 + difference 5 0) sourceC973) = raw16008 := by
      apply Matrix.ext; unfold tripleCharges sourceA973 sourceB973 sourceC973 difference raw16008; decide +kernel
    rw [ha]
    exact (canonical16008 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA973 + sourceB973) sourceC973) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA973 + sourceB973) sourceC973) = raw16009 := by
      apply Matrix.ext; unfold doubleCharges sourceA973 sourceB973 sourceC973 raw16009; decide +kernel
    rw [ha]
    exact (canonical16009 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA973 sourceB973 sourceC973
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm973, Integer.Sparse.eval]
  linarith only [hs]

def sourceA974 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB974 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC974 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceForm974 : Integer.Sparse Master := [(Sum.inr 2944, 1), (Sum.inr 2945, 1), (Sum.inr 2947, 1), (Sum.inr 2951, 1), (Sum.inr 3091, 1), (Sum.inr 3871, 1), (Sum.inr 4091, -1)]

theorem sourceEq974 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm974 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA974 + difference 0 1) (sourceB974 + difference 1 0) sourceC974) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA974 + difference 0 1) (sourceB974 + difference 1 0) sourceC974) = raw16004 := by
      apply Matrix.ext; unfold tripleCharges sourceA974 sourceB974 sourceC974 difference raw16004; decide +kernel
    rw [ha]
    exact (canonical16004 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA974 + difference 1 1) (sourceB974 + difference 1 1) sourceC974) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA974 + difference 1 1) (sourceB974 + difference 1 1) sourceC974) = raw16003 := by
      apply Matrix.ext; unfold tripleCharges sourceA974 sourceB974 sourceC974 difference raw16003; decide +kernel
    rw [ha]
    exact (canonical16003 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA974 + difference 2 1) (sourceB974 + difference 1 2) sourceC974) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2944) := by
    have ha : (tripleCharges (sourceA974 + difference 2 1) (sourceB974 + difference 1 2) sourceC974) = raw16010 := by
      apply Matrix.ext; unfold tripleCharges sourceA974 sourceB974 sourceC974 difference raw16010; decide +kernel
    rw [ha]
    exact (canonical16010 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA974 + difference 3 1) (sourceB974 + difference 1 3) sourceC974) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA974 + difference 3 1) (sourceB974 + difference 1 3) sourceC974) = raw16011 := by
      apply Matrix.ext; unfold tripleCharges sourceA974 sourceB974 sourceC974 difference raw16011; decide +kernel
    rw [ha]
    exact (canonical16011 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA974 + difference 4 1) (sourceB974 + difference 1 4) sourceC974) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2945) := by
    have ha : (tripleCharges (sourceA974 + difference 4 1) (sourceB974 + difference 1 4) sourceC974) = raw16012 := by
      apply Matrix.ext; unfold tripleCharges sourceA974 sourceB974 sourceC974 difference raw16012; decide +kernel
    rw [ha]
    exact (canonical16012 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA974 + difference 5 1) (sourceB974 + difference 1 5) sourceC974) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2947) := by
    have ha : (tripleCharges (sourceA974 + difference 5 1) (sourceB974 + difference 1 5) sourceC974) = raw16013 := by
      apply Matrix.ext; unfold tripleCharges sourceA974 sourceB974 sourceC974 difference raw16013; decide +kernel
    rw [ha]
    exact (canonical16013 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA974 + sourceB974) sourceC974) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA974 + sourceB974) sourceC974) = raw16009 := by
      apply Matrix.ext; unfold doubleCharges sourceA974 sourceB974 sourceC974 raw16009; decide +kernel
    rw [ha]
    exact (canonical16009 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA974 sourceB974 sourceC974
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm974, Integer.Sparse.eval]
  linarith only [hs]

def sourceA975 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB975 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC975 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceForm975 : Integer.Sparse Master := [(Sum.inr 2622, 1), (Sum.inr 2944, 1), (Sum.inr 3864, 1), (Sum.inr 3871, 1), (Sum.inr 3880, 1), (Sum.inr 3881, 1), (Sum.inr 4091, -1)]

theorem sourceEq975 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm975 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA975 + difference 2 0) (sourceB975 + difference 0 2) sourceC975) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2622) := by
    have ha : (tripleCharges (sourceA975 + difference 2 0) (sourceB975 + difference 0 2) sourceC975) = raw16014 := by
      apply Matrix.ext; unfold tripleCharges sourceA975 sourceB975 sourceC975 difference raw16014; decide +kernel
    rw [ha]
    exact (canonical16014 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA975 + difference 2 1) (sourceB975 + difference 1 2) sourceC975) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2944) := by
    have ha : (tripleCharges (sourceA975 + difference 2 1) (sourceB975 + difference 1 2) sourceC975) = raw16010 := by
      apply Matrix.ext; unfold tripleCharges sourceA975 sourceB975 sourceC975 difference raw16010; decide +kernel
    rw [ha]
    exact (canonical16010 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA975 + difference 2 2) (sourceB975 + difference 2 2) sourceC975) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA975 + difference 2 2) (sourceB975 + difference 2 2) sourceC975) = raw16003 := by
      apply Matrix.ext; unfold tripleCharges sourceA975 sourceB975 sourceC975 difference raw16003; decide +kernel
    rw [ha]
    exact (canonical16003 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA975 + difference 2 3) (sourceB975 + difference 3 2) sourceC975) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3864) := by
    have ha : (tripleCharges (sourceA975 + difference 2 3) (sourceB975 + difference 3 2) sourceC975) = raw16015 := by
      apply Matrix.ext; unfold tripleCharges sourceA975 sourceB975 sourceC975 difference raw16015; decide +kernel
    rw [ha]
    exact (canonical16015 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA975 + difference 2 4) (sourceB975 + difference 4 2) sourceC975) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA975 + difference 2 4) (sourceB975 + difference 4 2) sourceC975) = raw16016 := by
      apply Matrix.ext; unfold tripleCharges sourceA975 sourceB975 sourceC975 difference raw16016; decide +kernel
    rw [ha]
    exact (canonical16016 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA975 + difference 2 5) (sourceB975 + difference 5 2) sourceC975) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA975 + difference 2 5) (sourceB975 + difference 5 2) sourceC975) = raw16017 := by
      apply Matrix.ext; unfold tripleCharges sourceA975 sourceB975 sourceC975 difference raw16017; decide +kernel
    rw [ha]
    exact (canonical16017 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA975 + sourceB975) sourceC975) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA975 + sourceB975) sourceC975) = raw16009 := by
      apply Matrix.ext; unfold doubleCharges sourceA975 sourceB975 sourceC975 raw16009; decide +kernel
    rw [ha]
    exact (canonical16009 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA975 sourceB975 sourceC975
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm975, Integer.Sparse.eval]
  linarith only [hs]

def sourceA976 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB976 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC976 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceForm976 : Integer.Sparse Master := [(Sum.inr 2984, 1), (Sum.inr 3783, 1), (Sum.inr 3787, 1), (Sum.inr 3800, 1), (Sum.inr 3871, 1), (Sum.inr 3978, 1), (Sum.inr 4091, -1)]

theorem sourceEq976 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm976 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA976 + difference 0 2) (sourceB976 + difference 2 0) sourceC976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA976 + difference 0 2) (sourceB976 + difference 2 0) sourceC976) = raw16005 := by
      apply Matrix.ext; unfold tripleCharges sourceA976 sourceB976 sourceC976 difference raw16005; decide +kernel
    rw [ha]
    exact (canonical16005 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA976 + difference 1 2) (sourceB976 + difference 2 1) sourceC976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA976 + difference 1 2) (sourceB976 + difference 2 1) sourceC976) = raw16018 := by
      apply Matrix.ext; unfold tripleCharges sourceA976 sourceB976 sourceC976 difference raw16018; decide +kernel
    rw [ha]
    exact (canonical16018 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA976 + difference 2 2) (sourceB976 + difference 2 2) sourceC976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA976 + difference 2 2) (sourceB976 + difference 2 2) sourceC976) = raw16003 := by
      apply Matrix.ext; unfold tripleCharges sourceA976 sourceB976 sourceC976 difference raw16003; decide +kernel
    rw [ha]
    exact (canonical16003 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA976 + difference 3 2) (sourceB976 + difference 2 3) sourceC976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3787) := by
    have ha : (tripleCharges (sourceA976 + difference 3 2) (sourceB976 + difference 2 3) sourceC976) = raw16019 := by
      apply Matrix.ext; unfold tripleCharges sourceA976 sourceB976 sourceC976 difference raw16019; decide +kernel
    rw [ha]
    exact (canonical16019 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA976 + difference 4 2) (sourceB976 + difference 2 4) sourceC976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3783) := by
    have ha : (tripleCharges (sourceA976 + difference 4 2) (sourceB976 + difference 2 4) sourceC976) = raw16020 := by
      apply Matrix.ext; unfold tripleCharges sourceA976 sourceB976 sourceC976 difference raw16020; decide +kernel
    rw [ha]
    exact (canonical16020 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA976 + difference 5 2) (sourceB976 + difference 2 5) sourceC976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA976 + difference 5 2) (sourceB976 + difference 2 5) sourceC976) = raw16021 := by
      apply Matrix.ext; unfold tripleCharges sourceA976 sourceB976 sourceC976 difference raw16021; decide +kernel
    rw [ha]
    exact (canonical16021 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA976 + sourceB976) sourceC976) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA976 + sourceB976) sourceC976) = raw16009 := by
      apply Matrix.ext; unfold doubleCharges sourceA976 sourceB976 sourceC976 raw16009; decide +kernel
    rw [ha]
    exact (canonical16009 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA976 sourceB976 sourceC976
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm976, Integer.Sparse.eval]
  linarith only [hs]

def sourceA977 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB977 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC977 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceForm977 : Integer.Sparse Master := [(Sum.inr 2615, 1), (Sum.inr 3091, 1), (Sum.inr 3787, 1), (Sum.inr 3871, 1), (Sum.inr 3875, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

theorem sourceEq977 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm977 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA977 + difference 3 0) (sourceB977 + difference 0 3) sourceC977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA977 + difference 3 0) (sourceB977 + difference 0 3) sourceC977) = raw16022 := by
      apply Matrix.ext; unfold tripleCharges sourceA977 sourceB977 sourceC977 difference raw16022; decide +kernel
    rw [ha]
    exact (canonical16022 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA977 + difference 3 1) (sourceB977 + difference 1 3) sourceC977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA977 + difference 3 1) (sourceB977 + difference 1 3) sourceC977) = raw16011 := by
      apply Matrix.ext; unfold tripleCharges sourceA977 sourceB977 sourceC977 difference raw16011; decide +kernel
    rw [ha]
    exact (canonical16011 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA977 + difference 3 2) (sourceB977 + difference 2 3) sourceC977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3787) := by
    have ha : (tripleCharges (sourceA977 + difference 3 2) (sourceB977 + difference 2 3) sourceC977) = raw16019 := by
      apply Matrix.ext; unfold tripleCharges sourceA977 sourceB977 sourceC977 difference raw16019; decide +kernel
    rw [ha]
    exact (canonical16019 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA977 + difference 3 3) (sourceB977 + difference 3 3) sourceC977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA977 + difference 3 3) (sourceB977 + difference 3 3) sourceC977) = raw16003 := by
      apply Matrix.ext; unfold tripleCharges sourceA977 sourceB977 sourceC977 difference raw16003; decide +kernel
    rw [ha]
    exact (canonical16003 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA977 + difference 3 4) (sourceB977 + difference 4 3) sourceC977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA977 + difference 3 4) (sourceB977 + difference 4 3) sourceC977) = raw16023 := by
      apply Matrix.ext; unfold tripleCharges sourceA977 sourceB977 sourceC977 difference raw16023; decide +kernel
    rw [ha]
    exact (canonical16023 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA977 + difference 3 5) (sourceB977 + difference 5 3) sourceC977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA977 + difference 3 5) (sourceB977 + difference 5 3) sourceC977) = raw16024 := by
      apply Matrix.ext; unfold tripleCharges sourceA977 sourceB977 sourceC977 difference raw16024; decide +kernel
    rw [ha]
    exact (canonical16024 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA977 + sourceB977) sourceC977) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA977 + sourceB977) sourceC977) = raw16009 := by
      apply Matrix.ext; unfold doubleCharges sourceA977 sourceB977 sourceC977 raw16009; decide +kernel
    rw [ha]
    exact (canonical16009 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA977 sourceB977 sourceC977
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm977, Integer.Sparse.eval]
  linarith only [hs]

def sourceA978 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB978 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC978 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceForm978 : Integer.Sparse Master := [(Sum.inr 4797, 1), (Sum.inr 4799, 1), (Sum.inr 4803, 1), (Sum.inr 4825, 1), (Sum.inr 4851, 1), (Sum.inr 5129, 1), (Sum.inr 5132, 1), (Sum.inr 5144, 1), (Sum.inr 5249, 1), (Sum.inr 5350, 1), (Sum.inr 5353, 1), (Sum.inr 5362, 1), (Sum.inr 5377, 1), (Sum.inr 5379, 1), (Sum.inr 5380, 1), (Sum.inr 5403, 1), (Sum.inr 5406, 1), (Sum.inr 5414, 1), (Sum.inr 5419, 1), (Sum.inr 5422, 1), (Sum.inr 5424, 1), (Sum.inr 5425, 1), (Sum.inr 5429, 1), (Sum.inr 5430, 2), (Sum.inr 5447, 1), (Sum.inr 5478, 1), (Sum.inr 5480, 1), (Sum.inr 5481, 1), (Sum.inr 5482, 1)]

theorem sourceEq978 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm978 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA978 + difference 0 1) (sourceB978 + difference 1 0) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA978 + difference 0 1) (sourceB978 + difference 1 0) sourceC978) = raw16025 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16025; decide +kernel
    rw [ha]
    exact (canonical16025 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA978 + difference 0 2) (sourceB978 + difference 2 0) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA978 + difference 0 2) (sourceB978 + difference 2 0) sourceC978) = raw16026 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16026; decide +kernel
    rw [ha]
    exact (canonical16026 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA978 + difference 0 3) (sourceB978 + difference 3 0) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA978 + difference 0 3) (sourceB978 + difference 3 0) sourceC978) = raw16027 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16027; decide +kernel
    rw [ha]
    exact (canonical16027 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA978 + difference 0 4) (sourceB978 + difference 4 0) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA978 + difference 0 4) (sourceB978 + difference 4 0) sourceC978) = raw16028 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16028; decide +kernel
    rw [ha]
    exact (canonical16028 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA978 + difference 0 5) (sourceB978 + difference 5 0) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA978 + difference 0 5) (sourceB978 + difference 5 0) sourceC978) = raw16029 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16029; decide +kernel
    rw [ha]
    exact (canonical16029 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA978 + difference 1 0) (sourceB978 + difference 0 1) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA978 + difference 1 0) (sourceB978 + difference 0 1) sourceC978) = raw16030 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16030; decide +kernel
    rw [ha]
    exact (canonical16030 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA978 + difference 1 2) (sourceB978 + difference 2 1) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA978 + difference 1 2) (sourceB978 + difference 2 1) sourceC978) = raw16031 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16031; decide +kernel
    rw [ha]
    exact (canonical16031 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA978 + difference 1 3) (sourceB978 + difference 3 1) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA978 + difference 1 3) (sourceB978 + difference 3 1) sourceC978) = raw16032 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16032; decide +kernel
    rw [ha]
    exact (canonical16032 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA978 + difference 1 4) (sourceB978 + difference 4 1) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA978 + difference 1 4) (sourceB978 + difference 4 1) sourceC978) = raw16033 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16033; decide +kernel
    rw [ha]
    exact (canonical16033 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA978 + difference 1 5) (sourceB978 + difference 5 1) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA978 + difference 1 5) (sourceB978 + difference 5 1) sourceC978) = raw16034 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16034; decide +kernel
    rw [ha]
    exact (canonical16034 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA978 + difference 2 0) (sourceB978 + difference 0 2) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA978 + difference 2 0) (sourceB978 + difference 0 2) sourceC978) = raw16035 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16035; decide +kernel
    rw [ha]
    exact (canonical16035 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA978 + difference 2 1) (sourceB978 + difference 1 2) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA978 + difference 2 1) (sourceB978 + difference 1 2) sourceC978) = raw16036 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16036; decide +kernel
    rw [ha]
    exact (canonical16036 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA978 + difference 2 3) (sourceB978 + difference 3 2) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA978 + difference 2 3) (sourceB978 + difference 3 2) sourceC978) = raw16037 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16037; decide +kernel
    rw [ha]
    exact (canonical16037 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA978 + difference 2 4) (sourceB978 + difference 4 2) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA978 + difference 2 4) (sourceB978 + difference 4 2) sourceC978) = raw16038 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16038; decide +kernel
    rw [ha]
    exact (canonical16038 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA978 + difference 2 5) (sourceB978 + difference 5 2) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA978 + difference 2 5) (sourceB978 + difference 5 2) sourceC978) = raw16039 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16039; decide +kernel
    rw [ha]
    exact (canonical16039 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA978 + difference 3 0) (sourceB978 + difference 0 3) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4799) := by
    have ha : (tripleCharges (sourceA978 + difference 3 0) (sourceB978 + difference 0 3) sourceC978) = raw16040 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16040; decide +kernel
    rw [ha]
    exact (canonical16040 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA978 + difference 3 1) (sourceB978 + difference 1 3) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA978 + difference 3 1) (sourceB978 + difference 1 3) sourceC978) = raw16041 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16041; decide +kernel
    rw [ha]
    exact (canonical16041 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA978 + difference 3 2) (sourceB978 + difference 2 3) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5350) := by
    have ha : (tripleCharges (sourceA978 + difference 3 2) (sourceB978 + difference 2 3) sourceC978) = raw16042 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16042; decide +kernel
    rw [ha]
    exact (canonical16042 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA978 + difference 3 4) (sourceB978 + difference 4 3) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA978 + difference 3 4) (sourceB978 + difference 4 3) sourceC978) = raw16043 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16043; decide +kernel
    rw [ha]
    exact (canonical16043 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA978 + difference 3 5) (sourceB978 + difference 5 3) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA978 + difference 3 5) (sourceB978 + difference 5 3) sourceC978) = raw16044 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16044; decide +kernel
    rw [ha]
    exact (canonical16044 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA978 + difference 4 0) (sourceB978 + difference 0 4) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4825) := by
    have ha : (tripleCharges (sourceA978 + difference 4 0) (sourceB978 + difference 0 4) sourceC978) = raw16045 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16045; decide +kernel
    rw [ha]
    exact (canonical16045 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA978 + difference 4 1) (sourceB978 + difference 1 4) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5377) := by
    have ha : (tripleCharges (sourceA978 + difference 4 1) (sourceB978 + difference 1 4) sourceC978) = raw16046 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16046; decide +kernel
    rw [ha]
    exact (canonical16046 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA978 + difference 4 2) (sourceB978 + difference 2 4) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5362) := by
    have ha : (tripleCharges (sourceA978 + difference 4 2) (sourceB978 + difference 2 4) sourceC978) = raw16047 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16047; decide +kernel
    rw [ha]
    exact (canonical16047 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA978 + difference 4 3) (sourceB978 + difference 3 4) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5419) := by
    have ha : (tripleCharges (sourceA978 + difference 4 3) (sourceB978 + difference 3 4) sourceC978) = raw16048 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16048; decide +kernel
    rw [ha]
    exact (canonical16048 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA978 + difference 4 5) (sourceB978 + difference 5 4) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA978 + difference 4 5) (sourceB978 + difference 5 4) sourceC978) = raw16049 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16049; decide +kernel
    rw [ha]
    exact (canonical16049 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA978 + difference 5 0) (sourceB978 + difference 0 5) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4797) := by
    have ha : (tripleCharges (sourceA978 + difference 5 0) (sourceB978 + difference 0 5) sourceC978) = raw16050 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16050; decide +kernel
    rw [ha]
    exact (canonical16050 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA978 + difference 5 1) (sourceB978 + difference 1 5) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA978 + difference 5 1) (sourceB978 + difference 1 5) sourceC978) = raw16051 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16051; decide +kernel
    rw [ha]
    exact (canonical16051 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA978 + difference 5 2) (sourceB978 + difference 2 5) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5132) := by
    have ha : (tripleCharges (sourceA978 + difference 5 2) (sourceB978 + difference 2 5) sourceC978) = raw16052 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16052; decide +kernel
    rw [ha]
    exact (canonical16052 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA978 + difference 5 3) (sourceB978 + difference 3 5) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA978 + difference 5 3) (sourceB978 + difference 3 5) sourceC978) = raw16053 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16053; decide +kernel
    rw [ha]
    exact (canonical16053 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA978 + difference 5 4) (sourceB978 + difference 4 5) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA978 + difference 5 4) (sourceB978 + difference 4 5) sourceC978) = raw16054 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16054; decide +kernel
    rw [ha]
    exact (canonical16054 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA978 sourceB978 sourceC978
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm978, Integer.Sparse.eval]
  linarith only [hs]

def sourceA979 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB979 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC979 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceForm979 : Integer.Sparse Master := [(Sum.inr 2070, 1), (Sum.inr 2073, 1), (Sum.inr 2076, 1), (Sum.inr 2088, 1), (Sum.inr 2195, 1), (Sum.inr 2545, 1), (Sum.inr 2551, 1), (Sum.inr 2566, 1), (Sum.inr 2708, 1), (Sum.inr 3716, 1), (Sum.inr 3720, 1), (Sum.inr 3726, 1), (Sum.inr 3748, 1), (Sum.inr 3750, 1), (Sum.inr 3761, 1), (Sum.inr 3810, 1), (Sum.inr 3812, 1), (Sum.inr 3825, 1), (Sum.inr 3829, 1), (Sum.inr 3840, 1), (Sum.inr 3869, 1), (Sum.inr 3871, 2), (Sum.inr 3874, 1), (Sum.inr 3882, 1), (Sum.inr 3978, 1), (Sum.inr 3979, 1), (Sum.inr 3980, 1), (Sum.inr 3990, 1), (Sum.inr 3994, 1)]

theorem sourceEq979 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm979 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA979 + difference 0 1) (sourceB979 + difference 1 0) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA979 + difference 0 1) (sourceB979 + difference 1 0) sourceC979) = raw16055 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16055; decide +kernel
    rw [ha]
    exact (canonical16055 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA979 + difference 0 2) (sourceB979 + difference 2 0) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA979 + difference 0 2) (sourceB979 + difference 2 0) sourceC979) = raw16056 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16056; decide +kernel
    rw [ha]
    exact (canonical16056 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA979 + difference 0 3) (sourceB979 + difference 3 0) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3994) := by
    have ha : (tripleCharges (sourceA979 + difference 0 3) (sourceB979 + difference 3 0) sourceC979) = raw16057 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16057; decide +kernel
    rw [ha]
    exact (canonical16057 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA979 + difference 0 4) (sourceB979 + difference 4 0) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA979 + difference 0 4) (sourceB979 + difference 4 0) sourceC979) = raw16058 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16058; decide +kernel
    rw [ha]
    exact (canonical16058 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA979 + difference 0 5) (sourceB979 + difference 5 0) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA979 + difference 0 5) (sourceB979 + difference 5 0) sourceC979) = raw16059 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16059; decide +kernel
    rw [ha]
    exact (canonical16059 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA979 + difference 1 0) (sourceB979 + difference 0 1) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA979 + difference 1 0) (sourceB979 + difference 0 1) sourceC979) = raw16060 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16060; decide +kernel
    rw [ha]
    exact (canonical16060 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA979 + difference 1 2) (sourceB979 + difference 2 1) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA979 + difference 1 2) (sourceB979 + difference 2 1) sourceC979) = raw16061 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16061; decide +kernel
    rw [ha]
    exact (canonical16061 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA979 + difference 1 3) (sourceB979 + difference 3 1) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA979 + difference 1 3) (sourceB979 + difference 3 1) sourceC979) = raw16062 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16062; decide +kernel
    rw [ha]
    exact (canonical16062 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA979 + difference 1 4) (sourceB979 + difference 4 1) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3810) := by
    have ha : (tripleCharges (sourceA979 + difference 1 4) (sourceB979 + difference 4 1) sourceC979) = raw16063 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16063; decide +kernel
    rw [ha]
    exact (canonical16063 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA979 + difference 1 5) (sourceB979 + difference 5 1) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA979 + difference 1 5) (sourceB979 + difference 5 1) sourceC979) = raw16064 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16064; decide +kernel
    rw [ha]
    exact (canonical16064 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA979 + difference 2 0) (sourceB979 + difference 0 2) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA979 + difference 2 0) (sourceB979 + difference 0 2) sourceC979) = raw16065 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16065; decide +kernel
    rw [ha]
    exact (canonical16065 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA979 + difference 2 1) (sourceB979 + difference 1 2) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3726) := by
    have ha : (tripleCharges (sourceA979 + difference 2 1) (sourceB979 + difference 1 2) sourceC979) = raw16066 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16066; decide +kernel
    rw [ha]
    exact (canonical16066 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA979 + difference 2 3) (sourceB979 + difference 3 2) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3829) := by
    have ha : (tripleCharges (sourceA979 + difference 2 3) (sourceB979 + difference 3 2) sourceC979) = raw16067 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16067; decide +kernel
    rw [ha]
    exact (canonical16067 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA979 + difference 2 4) (sourceB979 + difference 4 2) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA979 + difference 2 4) (sourceB979 + difference 4 2) sourceC979) = raw16068 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16068; decide +kernel
    rw [ha]
    exact (canonical16068 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA979 + difference 2 5) (sourceB979 + difference 5 2) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3882) := by
    have ha : (tripleCharges (sourceA979 + difference 2 5) (sourceB979 + difference 5 2) sourceC979) = raw16069 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16069; decide +kernel
    rw [ha]
    exact (canonical16069 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA979 + difference 3 0) (sourceB979 + difference 0 3) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2076) := by
    have ha : (tripleCharges (sourceA979 + difference 3 0) (sourceB979 + difference 0 3) sourceC979) = raw16070 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16070; decide +kernel
    rw [ha]
    exact (canonical16070 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA979 + difference 3 1) (sourceB979 + difference 1 3) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3720) := by
    have ha : (tripleCharges (sourceA979 + difference 3 1) (sourceB979 + difference 1 3) sourceC979) = raw16071 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16071; decide +kernel
    rw [ha]
    exact (canonical16071 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA979 + difference 3 2) (sourceB979 + difference 2 3) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3750) := by
    have ha : (tripleCharges (sourceA979 + difference 3 2) (sourceB979 + difference 2 3) sourceC979) = raw16072 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16072; decide +kernel
    rw [ha]
    exact (canonical16072 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA979 + difference 3 4) (sourceB979 + difference 4 3) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA979 + difference 3 4) (sourceB979 + difference 4 3) sourceC979) = raw16073 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16073; decide +kernel
    rw [ha]
    exact (canonical16073 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA979 + difference 3 5) (sourceB979 + difference 5 3) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA979 + difference 3 5) (sourceB979 + difference 5 3) sourceC979) = raw16074 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16074; decide +kernel
    rw [ha]
    exact (canonical16074 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA979 + difference 4 0) (sourceB979 + difference 0 4) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2073) := by
    have ha : (tripleCharges (sourceA979 + difference 4 0) (sourceB979 + difference 0 4) sourceC979) = raw16075 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16075; decide +kernel
    rw [ha]
    exact (canonical16075 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA979 + difference 4 1) (sourceB979 + difference 1 4) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3716) := by
    have ha : (tripleCharges (sourceA979 + difference 4 1) (sourceB979 + difference 1 4) sourceC979) = raw16076 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16076; decide +kernel
    rw [ha]
    exact (canonical16076 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA979 + difference 4 2) (sourceB979 + difference 2 4) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3748) := by
    have ha : (tripleCharges (sourceA979 + difference 4 2) (sourceB979 + difference 2 4) sourceC979) = raw16077 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16077; decide +kernel
    rw [ha]
    exact (canonical16077 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA979 + difference 4 3) (sourceB979 + difference 3 4) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3825) := by
    have ha : (tripleCharges (sourceA979 + difference 4 3) (sourceB979 + difference 3 4) sourceC979) = raw16078 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16078; decide +kernel
    rw [ha]
    exact (canonical16078 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA979 + difference 4 5) (sourceB979 + difference 5 4) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA979 + difference 4 5) (sourceB979 + difference 5 4) sourceC979) = raw16079 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16079; decide +kernel
    rw [ha]
    exact (canonical16079 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA979 + difference 5 0) (sourceB979 + difference 0 5) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2070) := by
    have ha : (tripleCharges (sourceA979 + difference 5 0) (sourceB979 + difference 0 5) sourceC979) = raw16080 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16080; decide +kernel
    rw [ha]
    exact (canonical16080 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA979 + difference 5 1) (sourceB979 + difference 1 5) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA979 + difference 5 1) (sourceB979 + difference 1 5) sourceC979) = raw16081 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16081; decide +kernel
    rw [ha]
    exact (canonical16081 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA979 + difference 5 2) (sourceB979 + difference 2 5) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2551) := by
    have ha : (tripleCharges (sourceA979 + difference 5 2) (sourceB979 + difference 2 5) sourceC979) = raw16082 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16082; decide +kernel
    rw [ha]
    exact (canonical16082 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA979 + difference 5 3) (sourceB979 + difference 3 5) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2566) := by
    have ha : (tripleCharges (sourceA979 + difference 5 3) (sourceB979 + difference 3 5) sourceC979) = raw16083 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16083; decide +kernel
    rw [ha]
    exact (canonical16083 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA979 + difference 5 4) (sourceB979 + difference 4 5) sourceC979) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA979 + difference 5 4) (sourceB979 + difference 4 5) sourceC979) = raw16084 := by
      apply Matrix.ext; unfold tripleCharges sourceA979 sourceB979 sourceC979 difference raw16084; decide +kernel
    rw [ha]
    exact (canonical16084 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA979 sourceB979 sourceC979
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm979, Integer.Sparse.eval]
  linarith only [hs]

def sourceA980 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB980 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC980 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceForm980 : Integer.Sparse Master := [(Sum.inr 2015, 1), (Sum.inr 2017, 1), (Sum.inr 2021, 1), (Sum.inr 2044, 1), (Sum.inr 2240, 1), (Sum.inr 3499, 1), (Sum.inr 3502, 1), (Sum.inr 3516, 1), (Sum.inr 3557, 1), (Sum.inr 3688, 1), (Sum.inr 3691, 1), (Sum.inr 3700, 1), (Sum.inr 3819, 1), (Sum.inr 3822, 1), (Sum.inr 3832, 1), (Sum.inr 3835, 1), (Sum.inr 3836, 1), (Sum.inr 3839, 1), (Sum.inr 3842, 1), (Sum.inr 3843, 1), (Sum.inr 3846, 1), (Sum.inr 3847, 1), (Sum.inr 3848, 2), (Sum.inr 3900, 1), (Sum.inr 3909, 1), (Sum.inr 3974, 1), (Sum.inr 3978, 1), (Sum.inr 3991, 1), (Sum.inr 3992, 1)]

theorem sourceEq980 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm980 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA980 + difference 0 1) (sourceB980 + difference 1 0) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA980 + difference 0 1) (sourceB980 + difference 1 0) sourceC980) = raw16085 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16085; decide +kernel
    rw [ha]
    exact (canonical16085 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA980 + difference 0 2) (sourceB980 + difference 2 0) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA980 + difference 0 2) (sourceB980 + difference 2 0) sourceC980) = raw16086 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16086; decide +kernel
    rw [ha]
    exact (canonical16086 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA980 + difference 0 3) (sourceB980 + difference 3 0) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA980 + difference 0 3) (sourceB980 + difference 3 0) sourceC980) = raw16087 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16087; decide +kernel
    rw [ha]
    exact (canonical16087 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA980 + difference 0 4) (sourceB980 + difference 4 0) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3991) := by
    have ha : (tripleCharges (sourceA980 + difference 0 4) (sourceB980 + difference 4 0) sourceC980) = raw16088 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16088; decide +kernel
    rw [ha]
    exact (canonical16088 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA980 + difference 0 5) (sourceB980 + difference 5 0) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3992) := by
    have ha : (tripleCharges (sourceA980 + difference 0 5) (sourceB980 + difference 5 0) sourceC980) = raw16089 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16089; decide +kernel
    rw [ha]
    exact (canonical16089 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA980 + difference 1 0) (sourceB980 + difference 0 1) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA980 + difference 1 0) (sourceB980 + difference 0 1) sourceC980) = raw16090 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16090; decide +kernel
    rw [ha]
    exact (canonical16090 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA980 + difference 1 2) (sourceB980 + difference 2 1) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA980 + difference 1 2) (sourceB980 + difference 2 1) sourceC980) = raw16091 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16091; decide +kernel
    rw [ha]
    exact (canonical16091 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA980 + difference 1 3) (sourceB980 + difference 3 1) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA980 + difference 1 3) (sourceB980 + difference 3 1) sourceC980) = raw16092 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16092; decide +kernel
    rw [ha]
    exact (canonical16092 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA980 + difference 1 4) (sourceB980 + difference 4 1) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3822) := by
    have ha : (tripleCharges (sourceA980 + difference 1 4) (sourceB980 + difference 4 1) sourceC980) = raw16093 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16093; decide +kernel
    rw [ha]
    exact (canonical16093 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA980 + difference 1 5) (sourceB980 + difference 5 1) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA980 + difference 1 5) (sourceB980 + difference 5 1) sourceC980) = raw16094 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16094; decide +kernel
    rw [ha]
    exact (canonical16094 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA980 + difference 2 0) (sourceB980 + difference 0 2) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA980 + difference 2 0) (sourceB980 + difference 0 2) sourceC980) = raw16095 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16095; decide +kernel
    rw [ha]
    exact (canonical16095 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA980 + difference 2 1) (sourceB980 + difference 1 2) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3836) := by
    have ha : (tripleCharges (sourceA980 + difference 2 1) (sourceB980 + difference 1 2) sourceC980) = raw16096 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16096; decide +kernel
    rw [ha]
    exact (canonical16096 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA980 + difference 2 3) (sourceB980 + difference 3 2) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3900) := by
    have ha : (tripleCharges (sourceA980 + difference 2 3) (sourceB980 + difference 3 2) sourceC980) = raw16097 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16097; decide +kernel
    rw [ha]
    exact (canonical16097 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA980 + difference 2 4) (sourceB980 + difference 4 2) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA980 + difference 2 4) (sourceB980 + difference 4 2) sourceC980) = raw16098 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16098; decide +kernel
    rw [ha]
    exact (canonical16098 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA980 + difference 2 5) (sourceB980 + difference 5 2) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA980 + difference 2 5) (sourceB980 + difference 5 2) sourceC980) = raw16099 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16099; decide +kernel
    rw [ha]
    exact (canonical16099 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA980 + difference 3 0) (sourceB980 + difference 0 3) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2017) := by
    have ha : (tripleCharges (sourceA980 + difference 3 0) (sourceB980 + difference 0 3) sourceC980) = raw16100 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16100; decide +kernel
    rw [ha]
    exact (canonical16100 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA980 + difference 3 1) (sourceB980 + difference 1 3) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA980 + difference 3 1) (sourceB980 + difference 1 3) sourceC980) = raw16101 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16101; decide +kernel
    rw [ha]
    exact (canonical16101 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA980 + difference 3 2) (sourceB980 + difference 2 3) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3688) := by
    have ha : (tripleCharges (sourceA980 + difference 3 2) (sourceB980 + difference 2 3) sourceC980) = raw16102 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16102; decide +kernel
    rw [ha]
    exact (canonical16102 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA980 + difference 3 4) (sourceB980 + difference 4 3) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3819) := by
    have ha : (tripleCharges (sourceA980 + difference 3 4) (sourceB980 + difference 4 3) sourceC980) = raw16103 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16103; decide +kernel
    rw [ha]
    exact (canonical16103 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA980 + difference 3 5) (sourceB980 + difference 5 3) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA980 + difference 3 5) (sourceB980 + difference 5 3) sourceC980) = raw16104 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16104; decide +kernel
    rw [ha]
    exact (canonical16104 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA980 + difference 4 0) (sourceB980 + difference 0 4) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2044) := by
    have ha : (tripleCharges (sourceA980 + difference 4 0) (sourceB980 + difference 0 4) sourceC980) = raw16105 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16105; decide +kernel
    rw [ha]
    exact (canonical16105 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA980 + difference 4 1) (sourceB980 + difference 1 4) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3835) := by
    have ha : (tripleCharges (sourceA980 + difference 4 1) (sourceB980 + difference 1 4) sourceC980) = raw16106 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16106; decide +kernel
    rw [ha]
    exact (canonical16106 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA980 + difference 4 2) (sourceB980 + difference 2 4) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3700) := by
    have ha : (tripleCharges (sourceA980 + difference 4 2) (sourceB980 + difference 2 4) sourceC980) = raw16107 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16107; decide +kernel
    rw [ha]
    exact (canonical16107 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA980 + difference 4 3) (sourceB980 + difference 3 4) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3842) := by
    have ha : (tripleCharges (sourceA980 + difference 4 3) (sourceB980 + difference 3 4) sourceC980) = raw16108 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16108; decide +kernel
    rw [ha]
    exact (canonical16108 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA980 + difference 4 5) (sourceB980 + difference 5 4) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA980 + difference 4 5) (sourceB980 + difference 5 4) sourceC980) = raw16109 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16109; decide +kernel
    rw [ha]
    exact (canonical16109 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA980 + difference 5 0) (sourceB980 + difference 0 5) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2015) := by
    have ha : (tripleCharges (sourceA980 + difference 5 0) (sourceB980 + difference 0 5) sourceC980) = raw16110 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16110; decide +kernel
    rw [ha]
    exact (canonical16110 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA980 + difference 5 1) (sourceB980 + difference 1 5) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA980 + difference 5 1) (sourceB980 + difference 1 5) sourceC980) = raw16111 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16111; decide +kernel
    rw [ha]
    exact (canonical16111 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA980 + difference 5 2) (sourceB980 + difference 2 5) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3499) := by
    have ha : (tripleCharges (sourceA980 + difference 5 2) (sourceB980 + difference 2 5) sourceC980) = raw16112 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16112; decide +kernel
    rw [ha]
    exact (canonical16112 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA980 + difference 5 3) (sourceB980 + difference 3 5) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA980 + difference 5 3) (sourceB980 + difference 3 5) sourceC980) = raw16113 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16113; decide +kernel
    rw [ha]
    exact (canonical16113 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA980 + difference 5 4) (sourceB980 + difference 4 5) sourceC980) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3502) := by
    have ha : (tripleCharges (sourceA980 + difference 5 4) (sourceB980 + difference 4 5) sourceC980) = raw16114 := by
      apply Matrix.ext; unfold tripleCharges sourceA980 sourceB980 sourceC980 difference raw16114; decide +kernel
    rw [ha]
    exact (canonical16114 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA980 sourceB980 sourceC980
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm980, Integer.Sparse.eval]
  linarith only [hs]

def sourceA981 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB981 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC981 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceForm981 : Integer.Sparse Master := [(Sum.inr 2915, 1), (Sum.inr 3169, 1), (Sum.inr 3172, 1), (Sum.inr 3176, 1), (Sum.inr 3202, 1), (Sum.inr 3972, 1), (Sum.inr 4091, -1)]

theorem sourceEq981 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm981 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA981 + difference 0 0) (sourceB981 + difference 0 0) sourceC981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA981 + difference 0 0) (sourceB981 + difference 0 0) sourceC981) = raw16115 := by
      apply Matrix.ext; unfold tripleCharges sourceA981 sourceB981 sourceC981 difference raw16115; decide +kernel
    rw [ha]
    exact (canonical16115 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA981 + difference 1 0) (sourceB981 + difference 0 1) sourceC981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA981 + difference 1 0) (sourceB981 + difference 0 1) sourceC981) = raw16116 := by
      apply Matrix.ext; unfold tripleCharges sourceA981 sourceB981 sourceC981 difference raw16116; decide +kernel
    rw [ha]
    exact (canonical16116 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA981 + difference 2 0) (sourceB981 + difference 0 2) sourceC981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3172) := by
    have ha : (tripleCharges (sourceA981 + difference 2 0) (sourceB981 + difference 0 2) sourceC981) = raw16117 := by
      apply Matrix.ext; unfold tripleCharges sourceA981 sourceB981 sourceC981 difference raw16117; decide +kernel
    rw [ha]
    exact (canonical16117 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA981 + difference 3 0) (sourceB981 + difference 0 3) sourceC981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3176) := by
    have ha : (tripleCharges (sourceA981 + difference 3 0) (sourceB981 + difference 0 3) sourceC981) = raw16118 := by
      apply Matrix.ext; unfold tripleCharges sourceA981 sourceB981 sourceC981 difference raw16118; decide +kernel
    rw [ha]
    exact (canonical16118 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA981 + difference 4 0) (sourceB981 + difference 0 4) sourceC981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3169) := by
    have ha : (tripleCharges (sourceA981 + difference 4 0) (sourceB981 + difference 0 4) sourceC981) = raw16119 := by
      apply Matrix.ext; unfold tripleCharges sourceA981 sourceB981 sourceC981 difference raw16119; decide +kernel
    rw [ha]
    exact (canonical16119 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA981 + difference 5 0) (sourceB981 + difference 0 5) sourceC981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2915) := by
    have ha : (tripleCharges (sourceA981 + difference 5 0) (sourceB981 + difference 0 5) sourceC981) = raw16120 := by
      apply Matrix.ext; unfold tripleCharges sourceA981 sourceB981 sourceC981 difference raw16120; decide +kernel
    rw [ha]
    exact (canonical16120 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA981 + sourceB981) sourceC981) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA981 + sourceB981) sourceC981) = raw16121 := by
      apply Matrix.ext; unfold doubleCharges sourceA981 sourceB981 sourceC981 raw16121; decide +kernel
    rw [ha]
    exact (canonical16121 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA981 sourceB981 sourceC981
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm981, Integer.Sparse.eval]
  linarith only [hs]

def sourceA982 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB982 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC982 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceForm982 : Integer.Sparse Master := [(Sum.inr 2916, 1), (Sum.inr 3716, 1), (Sum.inr 3721, 1), (Sum.inr 3724, 1), (Sum.inr 3838, 1), (Sum.inr 3972, 1), (Sum.inr 4091, -1)]

theorem sourceEq982 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm982 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA982 + difference 0 1) (sourceB982 + difference 1 0) sourceC982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA982 + difference 0 1) (sourceB982 + difference 1 0) sourceC982) = raw16122 := by
      apply Matrix.ext; unfold tripleCharges sourceA982 sourceB982 sourceC982 difference raw16122; decide +kernel
    rw [ha]
    exact (canonical16122 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA982 + difference 1 1) (sourceB982 + difference 1 1) sourceC982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA982 + difference 1 1) (sourceB982 + difference 1 1) sourceC982) = raw16115 := by
      apply Matrix.ext; unfold tripleCharges sourceA982 sourceB982 sourceC982 difference raw16115; decide +kernel
    rw [ha]
    exact (canonical16115 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA982 + difference 2 1) (sourceB982 + difference 1 2) sourceC982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA982 + difference 2 1) (sourceB982 + difference 1 2) sourceC982) = raw16123 := by
      apply Matrix.ext; unfold tripleCharges sourceA982 sourceB982 sourceC982 difference raw16123; decide +kernel
    rw [ha]
    exact (canonical16123 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA982 + difference 3 1) (sourceB982 + difference 1 3) sourceC982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA982 + difference 3 1) (sourceB982 + difference 1 3) sourceC982) = raw16124 := by
      apply Matrix.ext; unfold tripleCharges sourceA982 sourceB982 sourceC982 difference raw16124; decide +kernel
    rw [ha]
    exact (canonical16124 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA982 + difference 4 1) (sourceB982 + difference 1 4) sourceC982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3716) := by
    have ha : (tripleCharges (sourceA982 + difference 4 1) (sourceB982 + difference 1 4) sourceC982) = raw16125 := by
      apply Matrix.ext; unfold tripleCharges sourceA982 sourceB982 sourceC982 difference raw16125; decide +kernel
    rw [ha]
    exact (canonical16125 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA982 + difference 5 1) (sourceB982 + difference 1 5) sourceC982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA982 + difference 5 1) (sourceB982 + difference 1 5) sourceC982) = raw16126 := by
      apply Matrix.ext; unfold tripleCharges sourceA982 sourceB982 sourceC982 difference raw16126; decide +kernel
    rw [ha]
    exact (canonical16126 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA982 + sourceB982) sourceC982) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA982 + sourceB982) sourceC982) = raw16121 := by
      apply Matrix.ext; unfold doubleCharges sourceA982 sourceB982 sourceC982 raw16121; decide +kernel
    rw [ha]
    exact (canonical16121 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA982 sourceB982 sourceC982
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm982, Integer.Sparse.eval]
  linarith only [hs]

def sourceA983 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB983 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC983 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceForm983 : Integer.Sparse Master := [(Sum.inr 3172, 1), (Sum.inr 3721, 1), (Sum.inr 3964, 1), (Sum.inr 3972, 2), (Sum.inr 4025, 1), (Sum.inr 4091, -1)]

theorem sourceEq983 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm983 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA983 + difference 2 0) (sourceB983 + difference 0 2) sourceC983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3172) := by
    have ha : (tripleCharges (sourceA983 + difference 2 0) (sourceB983 + difference 0 2) sourceC983) = raw16117 := by
      apply Matrix.ext; unfold tripleCharges sourceA983 sourceB983 sourceC983 difference raw16117; decide +kernel
    rw [ha]
    exact (canonical16117 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA983 + difference 2 1) (sourceB983 + difference 1 2) sourceC983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA983 + difference 2 1) (sourceB983 + difference 1 2) sourceC983) = raw16123 := by
      apply Matrix.ext; unfold tripleCharges sourceA983 sourceB983 sourceC983 difference raw16123; decide +kernel
    rw [ha]
    exact (canonical16123 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA983 + difference 2 2) (sourceB983 + difference 2 2) sourceC983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA983 + difference 2 2) (sourceB983 + difference 2 2) sourceC983) = raw16115 := by
      apply Matrix.ext; unfold tripleCharges sourceA983 sourceB983 sourceC983 difference raw16115; decide +kernel
    rw [ha]
    exact (canonical16115 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA983 + difference 2 3) (sourceB983 + difference 3 2) sourceC983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3964) := by
    have ha : (tripleCharges (sourceA983 + difference 2 3) (sourceB983 + difference 3 2) sourceC983) = raw16127 := by
      apply Matrix.ext; unfold tripleCharges sourceA983 sourceB983 sourceC983 difference raw16127; decide +kernel
    rw [ha]
    exact (canonical16127 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA983 + difference 2 4) (sourceB983 + difference 4 2) sourceC983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA983 + difference 2 4) (sourceB983 + difference 4 2) sourceC983) = raw16128 := by
      apply Matrix.ext; unfold tripleCharges sourceA983 sourceB983 sourceC983 difference raw16128; decide +kernel
    rw [ha]
    exact (canonical16128 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA983 + difference 2 5) (sourceB983 + difference 5 2) sourceC983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4025) := by
    have ha : (tripleCharges (sourceA983 + difference 2 5) (sourceB983 + difference 5 2) sourceC983) = raw16129 := by
      apply Matrix.ext; unfold tripleCharges sourceA983 sourceB983 sourceC983 difference raw16129; decide +kernel
    rw [ha]
    exact (canonical16129 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA983 + sourceB983) sourceC983) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA983 + sourceB983) sourceC983) = raw16121 := by
      apply Matrix.ext; unfold doubleCharges sourceA983 sourceB983 sourceC983 raw16121; decide +kernel
    rw [ha]
    exact (canonical16121 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA983 sourceB983 sourceC983
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm983, Integer.Sparse.eval]
  linarith only [hs]

def sourceA984 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB984 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC984 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceForm984 : Integer.Sparse Master := [(Sum.inr 2935, 1), (Sum.inr 3783, 1), (Sum.inr 3924, 1), (Sum.inr 3935, 1), (Sum.inr 3972, 1), (Sum.inr 3978, 1), (Sum.inr 4091, -1)]

theorem sourceEq984 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm984 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA984 + difference 0 2) (sourceB984 + difference 2 0) sourceC984) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA984 + difference 0 2) (sourceB984 + difference 2 0) sourceC984) = raw16130 := by
      apply Matrix.ext; unfold tripleCharges sourceA984 sourceB984 sourceC984 difference raw16130; decide +kernel
    rw [ha]
    exact (canonical16130 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA984 + difference 1 2) (sourceB984 + difference 2 1) sourceC984) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3783) := by
    have ha : (tripleCharges (sourceA984 + difference 1 2) (sourceB984 + difference 2 1) sourceC984) = raw16131 := by
      apply Matrix.ext; unfold tripleCharges sourceA984 sourceB984 sourceC984 difference raw16131; decide +kernel
    rw [ha]
    exact (canonical16131 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA984 + difference 2 2) (sourceB984 + difference 2 2) sourceC984) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA984 + difference 2 2) (sourceB984 + difference 2 2) sourceC984) = raw16115 := by
      apply Matrix.ext; unfold tripleCharges sourceA984 sourceB984 sourceC984 difference raw16115; decide +kernel
    rw [ha]
    exact (canonical16115 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA984 + difference 3 2) (sourceB984 + difference 2 3) sourceC984) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3935) := by
    have ha : (tripleCharges (sourceA984 + difference 3 2) (sourceB984 + difference 2 3) sourceC984) = raw16132 := by
      apply Matrix.ext; unfold tripleCharges sourceA984 sourceB984 sourceC984 difference raw16132; decide +kernel
    rw [ha]
    exact (canonical16132 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA984 + difference 4 2) (sourceB984 + difference 2 4) sourceC984) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3924) := by
    have ha : (tripleCharges (sourceA984 + difference 4 2) (sourceB984 + difference 2 4) sourceC984) = raw16133 := by
      apply Matrix.ext; unfold tripleCharges sourceA984 sourceB984 sourceC984 difference raw16133; decide +kernel
    rw [ha]
    exact (canonical16133 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA984 + difference 5 2) (sourceB984 + difference 2 5) sourceC984) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2935) := by
    have ha : (tripleCharges (sourceA984 + difference 5 2) (sourceB984 + difference 2 5) sourceC984) = raw16134 := by
      apply Matrix.ext; unfold tripleCharges sourceA984 sourceB984 sourceC984 difference raw16134; decide +kernel
    rw [ha]
    exact (canonical16134 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA984 + sourceB984) sourceC984) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA984 + sourceB984) sourceC984) = raw16121 := by
      apply Matrix.ext; unfold doubleCharges sourceA984 sourceB984 sourceC984 raw16121; decide +kernel
    rw [ha]
    exact (canonical16121 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA984 sourceB984 sourceC984
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm984, Integer.Sparse.eval]
  linarith only [hs]

def sourceA985 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB985 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC985 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceForm985 : Integer.Sparse Master := [(Sum.inr 3169, 1), (Sum.inr 3716, 1), (Sum.inr 3922, 1), (Sum.inr 3924, 1), (Sum.inr 3972, 2), (Sum.inr 4091, -1)]

theorem sourceEq985 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm985 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA985 + difference 4 0) (sourceB985 + difference 0 4) sourceC985) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3169) := by
    have ha : (tripleCharges (sourceA985 + difference 4 0) (sourceB985 + difference 0 4) sourceC985) = raw16119 := by
      apply Matrix.ext; unfold tripleCharges sourceA985 sourceB985 sourceC985 difference raw16119; decide +kernel
    rw [ha]
    exact (canonical16119 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA985 + difference 4 1) (sourceB985 + difference 1 4) sourceC985) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3716) := by
    have ha : (tripleCharges (sourceA985 + difference 4 1) (sourceB985 + difference 1 4) sourceC985) = raw16125 := by
      apply Matrix.ext; unfold tripleCharges sourceA985 sourceB985 sourceC985 difference raw16125; decide +kernel
    rw [ha]
    exact (canonical16125 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA985 + difference 4 2) (sourceB985 + difference 2 4) sourceC985) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3924) := by
    have ha : (tripleCharges (sourceA985 + difference 4 2) (sourceB985 + difference 2 4) sourceC985) = raw16133 := by
      apply Matrix.ext; unfold tripleCharges sourceA985 sourceB985 sourceC985 difference raw16133; decide +kernel
    rw [ha]
    exact (canonical16133 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA985 + difference 4 3) (sourceB985 + difference 3 4) sourceC985) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3922) := by
    have ha : (tripleCharges (sourceA985 + difference 4 3) (sourceB985 + difference 3 4) sourceC985) = raw16135 := by
      apply Matrix.ext; unfold tripleCharges sourceA985 sourceB985 sourceC985 difference raw16135; decide +kernel
    rw [ha]
    exact (canonical16135 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA985 + difference 4 4) (sourceB985 + difference 4 4) sourceC985) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA985 + difference 4 4) (sourceB985 + difference 4 4) sourceC985) = raw16115 := by
      apply Matrix.ext; unfold tripleCharges sourceA985 sourceB985 sourceC985 difference raw16115; decide +kernel
    rw [ha]
    exact (canonical16115 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA985 + difference 4 5) (sourceB985 + difference 5 4) sourceC985) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA985 + difference 4 5) (sourceB985 + difference 5 4) sourceC985) = raw16136 := by
      apply Matrix.ext; unfold tripleCharges sourceA985 sourceB985 sourceC985 difference raw16136; decide +kernel
    rw [ha]
    exact (canonical16136 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA985 + sourceB985) sourceC985) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA985 + sourceB985) sourceC985) = raw16121 := by
      apply Matrix.ext; unfold doubleCharges sourceA985 sourceB985 sourceC985 raw16121; decide +kernel
    rw [ha]
    exact (canonical16121 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA985 sourceB985 sourceC985
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm985, Integer.Sparse.eval]
  linarith only [hs]

def sourceA986 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB986 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC986 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceForm986 : Integer.Sparse Master := [(Sum.inr 3066, 1), (Sum.inr 3789, 1), (Sum.inr 3949, 1), (Sum.inr 3972, 2), (Sum.inr 4008, 1), (Sum.inr 4091, -1)]

theorem sourceEq986 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm986 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA986 + difference 0 4) (sourceB986 + difference 4 0) sourceC986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4008) := by
    have ha : (tripleCharges (sourceA986 + difference 0 4) (sourceB986 + difference 4 0) sourceC986) = raw16137 := by
      apply Matrix.ext; unfold tripleCharges sourceA986 sourceB986 sourceC986 difference raw16137; decide +kernel
    rw [ha]
    exact (canonical16137 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA986 + difference 1 4) (sourceB986 + difference 4 1) sourceC986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3789) := by
    have ha : (tripleCharges (sourceA986 + difference 1 4) (sourceB986 + difference 4 1) sourceC986) = raw16138 := by
      apply Matrix.ext; unfold tripleCharges sourceA986 sourceB986 sourceC986 difference raw16138; decide +kernel
    rw [ha]
    exact (canonical16138 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA986 + difference 2 4) (sourceB986 + difference 4 2) sourceC986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA986 + difference 2 4) (sourceB986 + difference 4 2) sourceC986) = raw16128 := by
      apply Matrix.ext; unfold tripleCharges sourceA986 sourceB986 sourceC986 difference raw16128; decide +kernel
    rw [ha]
    exact (canonical16128 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA986 + difference 3 4) (sourceB986 + difference 4 3) sourceC986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3949) := by
    have ha : (tripleCharges (sourceA986 + difference 3 4) (sourceB986 + difference 4 3) sourceC986) = raw16139 := by
      apply Matrix.ext; unfold tripleCharges sourceA986 sourceB986 sourceC986 difference raw16139; decide +kernel
    rw [ha]
    exact (canonical16139 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA986 + difference 4 4) (sourceB986 + difference 4 4) sourceC986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA986 + difference 4 4) (sourceB986 + difference 4 4) sourceC986) = raw16115 := by
      apply Matrix.ext; unfold tripleCharges sourceA986 sourceB986 sourceC986 difference raw16115; decide +kernel
    rw [ha]
    exact (canonical16115 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA986 + difference 5 4) (sourceB986 + difference 4 5) sourceC986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3066) := by
    have ha : (tripleCharges (sourceA986 + difference 5 4) (sourceB986 + difference 4 5) sourceC986) = raw16140 := by
      apply Matrix.ext; unfold tripleCharges sourceA986 sourceB986 sourceC986 difference raw16140; decide +kernel
    rw [ha]
    exact (canonical16140 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA986 + sourceB986) sourceC986) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA986 + sourceB986) sourceC986) = raw16121 := by
      apply Matrix.ext; unfold doubleCharges sourceA986 sourceB986 sourceC986 raw16121; decide +kernel
    rw [ha]
    exact (canonical16121 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA986 sourceB986 sourceC986
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm986, Integer.Sparse.eval]
  linarith only [hs]

def sourceA987 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB987 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC987 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm987 : Integer.Sparse Master := [(Sum.inr 5082, 1), (Sum.inr 5083, 1), (Sum.inr 5086, 1), (Sum.inr 5091, 1), (Sum.inr 5144, 1), (Sum.inr 5146, 1), (Sum.inr 5160, 1), (Sum.inr 5289, 1), (Sum.inr 5299, 1), (Sum.inr 5357, 1), (Sum.inr 5358, 1), (Sum.inr 5360, 1), (Sum.inr 5381, 1), (Sum.inr 5382, 1), (Sum.inr 5395, 1), (Sum.inr 5411, 1), (Sum.inr 5420, 1), (Sum.inr 5421, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 1), (Sum.inr 5425, 2), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5438, 1), (Sum.inr 5446, 1), (Sum.inr 5451, 1), (Sum.inr 5468, 1), (Sum.inr 5473, 1), (Sum.inr 5477, 1)]

theorem sourceEq987 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm987 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA987 + difference 0 1) (sourceB987 + difference 1 0) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA987 + difference 0 1) (sourceB987 + difference 1 0) sourceC987) = raw15114 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw15114; decide +kernel
    rw [ha]
    exact (canonical15114 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA987 + difference 0 2) (sourceB987 + difference 2 0) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA987 + difference 0 2) (sourceB987 + difference 2 0) sourceC987) = raw16141 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16141; decide +kernel
    rw [ha]
    exact (canonical16141 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA987 + difference 0 3) (sourceB987 + difference 3 0) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA987 + difference 0 3) (sourceB987 + difference 3 0) sourceC987) = raw16142 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16142; decide +kernel
    rw [ha]
    exact (canonical16142 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA987 + difference 0 4) (sourceB987 + difference 4 0) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5468) := by
    have ha : (tripleCharges (sourceA987 + difference 0 4) (sourceB987 + difference 4 0) sourceC987) = raw16143 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16143; decide +kernel
    rw [ha]
    exact (canonical16143 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA987 + difference 0 5) (sourceB987 + difference 5 0) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA987 + difference 0 5) (sourceB987 + difference 5 0) sourceC987) = raw16144 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16144; decide +kernel
    rw [ha]
    exact (canonical16144 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA987 + difference 1 0) (sourceB987 + difference 0 1) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5091) := by
    have ha : (tripleCharges (sourceA987 + difference 1 0) (sourceB987 + difference 0 1) sourceC987) = raw16145 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16145; decide +kernel
    rw [ha]
    exact (canonical16145 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA987 + difference 1 2) (sourceB987 + difference 2 1) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5082) := by
    have ha : (tripleCharges (sourceA987 + difference 1 2) (sourceB987 + difference 2 1) sourceC987) = raw16146 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16146; decide +kernel
    rw [ha]
    exact (canonical16146 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA987 + difference 1 3) (sourceB987 + difference 3 1) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA987 + difference 1 3) (sourceB987 + difference 3 1) sourceC987) = raw16147 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16147; decide +kernel
    rw [ha]
    exact (canonical16147 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA987 + difference 1 4) (sourceB987 + difference 4 1) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5083) := by
    have ha : (tripleCharges (sourceA987 + difference 1 4) (sourceB987 + difference 4 1) sourceC987) = raw16148 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16148; decide +kernel
    rw [ha]
    exact (canonical16148 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA987 + difference 1 5) (sourceB987 + difference 5 1) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA987 + difference 1 5) (sourceB987 + difference 5 1) sourceC987) = raw16149 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16149; decide +kernel
    rw [ha]
    exact (canonical16149 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA987 + difference 2 0) (sourceB987 + difference 0 2) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA987 + difference 2 0) (sourceB987 + difference 0 2) sourceC987) = raw15118 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw15118; decide +kernel
    rw [ha]
    exact (canonical15118 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA987 + difference 2 1) (sourceB987 + difference 1 2) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA987 + difference 2 1) (sourceB987 + difference 1 2) sourceC987) = raw15210 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw15210; decide +kernel
    rw [ha]
    exact (canonical15210 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA987 + difference 2 3) (sourceB987 + difference 3 2) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA987 + difference 2 3) (sourceB987 + difference 3 2) sourceC987) = raw15120 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw15120; decide +kernel
    rw [ha]
    exact (canonical15120 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA987 + difference 2 4) (sourceB987 + difference 4 2) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA987 + difference 2 4) (sourceB987 + difference 4 2) sourceC987) = raw15121 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw15121; decide +kernel
    rw [ha]
    exact (canonical15121 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA987 + difference 2 5) (sourceB987 + difference 5 2) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA987 + difference 2 5) (sourceB987 + difference 5 2) sourceC987) = raw15122 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw15122; decide +kernel
    rw [ha]
    exact (canonical15122 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA987 + difference 3 0) (sourceB987 + difference 0 3) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5146) := by
    have ha : (tripleCharges (sourceA987 + difference 3 0) (sourceB987 + difference 0 3) sourceC987) = raw16150 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16150; decide +kernel
    rw [ha]
    exact (canonical16150 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA987 + difference 3 1) (sourceB987 + difference 1 3) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA987 + difference 3 1) (sourceB987 + difference 1 3) sourceC987) = raw15130 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw15130; decide +kernel
    rw [ha]
    exact (canonical15130 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA987 + difference 3 2) (sourceB987 + difference 2 3) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5357) := by
    have ha : (tripleCharges (sourceA987 + difference 3 2) (sourceB987 + difference 2 3) sourceC987) = raw16151 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16151; decide +kernel
    rw [ha]
    exact (canonical16151 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA987 + difference 3 4) (sourceB987 + difference 4 3) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5358) := by
    have ha : (tripleCharges (sourceA987 + difference 3 4) (sourceB987 + difference 4 3) sourceC987) = raw16152 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16152; decide +kernel
    rw [ha]
    exact (canonical16152 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA987 + difference 3 5) (sourceB987 + difference 5 3) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA987 + difference 3 5) (sourceB987 + difference 5 3) sourceC987) = raw16153 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16153; decide +kernel
    rw [ha]
    exact (canonical16153 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA987 + difference 4 0) (sourceB987 + difference 0 4) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA987 + difference 4 0) (sourceB987 + difference 0 4) sourceC987) = raw16154 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16154; decide +kernel
    rw [ha]
    exact (canonical16154 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA987 + difference 4 1) (sourceB987 + difference 1 4) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA987 + difference 4 1) (sourceB987 + difference 1 4) sourceC987) = raw14730 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw14730; decide +kernel
    rw [ha]
    exact (canonical14730 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA987 + difference 4 2) (sourceB987 + difference 2 4) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5382) := by
    have ha : (tripleCharges (sourceA987 + difference 4 2) (sourceB987 + difference 2 4) sourceC987) = raw16155 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16155; decide +kernel
    rw [ha]
    exact (canonical16155 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA987 + difference 4 3) (sourceB987 + difference 3 4) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA987 + difference 4 3) (sourceB987 + difference 3 4) sourceC987) = raw16156 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16156; decide +kernel
    rw [ha]
    exact (canonical16156 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA987 + difference 4 5) (sourceB987 + difference 5 4) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA987 + difference 4 5) (sourceB987 + difference 5 4) sourceC987) = raw14709 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw14709; decide +kernel
    rw [ha]
    exact (canonical14709 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA987 + difference 5 0) (sourceB987 + difference 0 5) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA987 + difference 5 0) (sourceB987 + difference 0 5) sourceC987) = raw16157 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16157; decide +kernel
    rw [ha]
    exact (canonical16157 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA987 + difference 5 1) (sourceB987 + difference 1 5) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA987 + difference 5 1) (sourceB987 + difference 1 5) sourceC987) = raw15137 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw15137; decide +kernel
    rw [ha]
    exact (canonical15137 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA987 + difference 5 2) (sourceB987 + difference 2 5) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA987 + difference 5 2) (sourceB987 + difference 2 5) sourceC987) = raw16158 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16158; decide +kernel
    rw [ha]
    exact (canonical16158 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA987 + difference 5 3) (sourceB987 + difference 3 5) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA987 + difference 5 3) (sourceB987 + difference 3 5) sourceC987) = raw16159 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16159; decide +kernel
    rw [ha]
    exact (canonical16159 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA987 + difference 5 4) (sourceB987 + difference 4 5) sourceC987) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5420) := by
    have ha : (tripleCharges (sourceA987 + difference 5 4) (sourceB987 + difference 4 5) sourceC987) = raw16160 := by
      apply Matrix.ext; unfold tripleCharges sourceA987 sourceB987 sourceC987 difference raw16160; decide +kernel
    rw [ha]
    exact (canonical16160 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA987 sourceB987 sourceC987
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm987, Integer.Sparse.eval]
  linarith only [hs]

def sourceA988 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB988 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC988 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm988 : Integer.Sparse Master := [(Sum.inr 2490, 1), (Sum.inr 2491, 1), (Sum.inr 2494, 1), (Sum.inr 2500, 1), (Sum.inr 2773, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3560, 1), (Sum.inr 3572, 1), (Sum.inr 3695, 1), (Sum.inr 3696, 1), (Sum.inr 3698, 1), (Sum.inr 3827, 1), (Sum.inr 3834, 1), (Sum.inr 3837, 1), (Sum.inr 3838, 1), (Sum.inr 3840, 1), (Sum.inr 3850, 1), (Sum.inr 3852, 1), (Sum.inr 3866, 1), (Sum.inr 3870, 1), (Sum.inr 3872, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1), (Sum.inr 3883, 1), (Sum.inr 3888, 1), (Sum.inr 3968, 1), (Sum.inr 3970, 1), (Sum.inr 3989, 1), (Sum.inr 3995, 1)]

theorem sourceEq988 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm988 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA988 + difference 0 1) (sourceB988 + difference 1 0) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3989) := by
    have ha : (tripleCharges (sourceA988 + difference 0 1) (sourceB988 + difference 1 0) sourceC988) = raw16161 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16161; decide +kernel
    rw [ha]
    exact (canonical16161 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA988 + difference 0 2) (sourceB988 + difference 2 0) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3827) := by
    have ha : (tripleCharges (sourceA988 + difference 0 2) (sourceB988 + difference 2 0) sourceC988) = raw16162 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16162; decide +kernel
    rw [ha]
    exact (canonical16162 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA988 + difference 0 3) (sourceB988 + difference 3 0) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA988 + difference 0 3) (sourceB988 + difference 3 0) sourceC988) = raw16163 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16163; decide +kernel
    rw [ha]
    exact (canonical16163 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA988 + difference 0 4) (sourceB988 + difference 4 0) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3968) := by
    have ha : (tripleCharges (sourceA988 + difference 0 4) (sourceB988 + difference 4 0) sourceC988) = raw16164 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16164; decide +kernel
    rw [ha]
    exact (canonical16164 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA988 + difference 0 5) (sourceB988 + difference 5 0) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3970) := by
    have ha : (tripleCharges (sourceA988 + difference 0 5) (sourceB988 + difference 5 0) sourceC988) = raw16165 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16165; decide +kernel
    rw [ha]
    exact (canonical16165 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA988 + difference 1 0) (sourceB988 + difference 0 1) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2500) := by
    have ha : (tripleCharges (sourceA988 + difference 1 0) (sourceB988 + difference 0 1) sourceC988) = raw16166 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16166; decide +kernel
    rw [ha]
    exact (canonical16166 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA988 + difference 1 2) (sourceB988 + difference 2 1) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2490) := by
    have ha : (tripleCharges (sourceA988 + difference 1 2) (sourceB988 + difference 2 1) sourceC988) = raw16167 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16167; decide +kernel
    rw [ha]
    exact (canonical16167 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA988 + difference 1 3) (sourceB988 + difference 3 1) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA988 + difference 1 3) (sourceB988 + difference 3 1) sourceC988) = raw16168 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16168; decide +kernel
    rw [ha]
    exact (canonical16168 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA988 + difference 1 4) (sourceB988 + difference 4 1) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2491) := by
    have ha : (tripleCharges (sourceA988 + difference 1 4) (sourceB988 + difference 4 1) sourceC988) = raw16169 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16169; decide +kernel
    rw [ha]
    exact (canonical16169 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA988 + difference 1 5) (sourceB988 + difference 5 1) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA988 + difference 1 5) (sourceB988 + difference 5 1) sourceC988) = raw16170 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16170; decide +kernel
    rw [ha]
    exact (canonical16170 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA988 + difference 2 0) (sourceB988 + difference 0 2) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA988 + difference 2 0) (sourceB988 + difference 0 2) sourceC988) = raw16171 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16171; decide +kernel
    rw [ha]
    exact (canonical16171 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA988 + difference 2 1) (sourceB988 + difference 1 2) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA988 + difference 2 1) (sourceB988 + difference 1 2) sourceC988) = raw15707 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw15707; decide +kernel
    rw [ha]
    exact (canonical15707 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA988 + difference 2 3) (sourceB988 + difference 3 2) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA988 + difference 2 3) (sourceB988 + difference 3 2) sourceC988) = raw16172 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16172; decide +kernel
    rw [ha]
    exact (canonical16172 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA988 + difference 2 4) (sourceB988 + difference 4 2) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA988 + difference 2 4) (sourceB988 + difference 4 2) sourceC988) = raw15691 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw15691; decide +kernel
    rw [ha]
    exact (canonical15691 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA988 + difference 2 5) (sourceB988 + difference 5 2) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA988 + difference 2 5) (sourceB988 + difference 5 2) sourceC988) = raw15876 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw15876; decide +kernel
    rw [ha]
    exact (canonical15876 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA988 + difference 3 0) (sourceB988 + difference 0 3) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3560) := by
    have ha : (tripleCharges (sourceA988 + difference 3 0) (sourceB988 + difference 0 3) sourceC988) = raw16173 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16173; decide +kernel
    rw [ha]
    exact (canonical16173 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA988 + difference 3 1) (sourceB988 + difference 1 3) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA988 + difference 3 1) (sourceB988 + difference 1 3) sourceC988) = raw16174 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16174; decide +kernel
    rw [ha]
    exact (canonical16174 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA988 + difference 3 2) (sourceB988 + difference 2 3) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3695) := by
    have ha : (tripleCharges (sourceA988 + difference 3 2) (sourceB988 + difference 2 3) sourceC988) = raw16175 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16175; decide +kernel
    rw [ha]
    exact (canonical16175 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA988 + difference 3 4) (sourceB988 + difference 4 3) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3696) := by
    have ha : (tripleCharges (sourceA988 + difference 3 4) (sourceB988 + difference 4 3) sourceC988) = raw16176 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16176; decide +kernel
    rw [ha]
    exact (canonical16176 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA988 + difference 3 5) (sourceB988 + difference 5 3) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3698) := by
    have ha : (tripleCharges (sourceA988 + difference 3 5) (sourceB988 + difference 5 3) sourceC988) = raw16177 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16177; decide +kernel
    rw [ha]
    exact (canonical16177 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA988 + difference 4 0) (sourceB988 + difference 0 4) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA988 + difference 4 0) (sourceB988 + difference 0 4) sourceC988) = raw16178 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16178; decide +kernel
    rw [ha]
    exact (canonical16178 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA988 + difference 4 1) (sourceB988 + difference 1 4) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA988 + difference 4 1) (sourceB988 + difference 1 4) sourceC988) = raw14760 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw14760; decide +kernel
    rw [ha]
    exact (canonical14760 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA988 + difference 4 2) (sourceB988 + difference 2 4) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA988 + difference 4 2) (sourceB988 + difference 2 4) sourceC988) = raw16179 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16179; decide +kernel
    rw [ha]
    exact (canonical16179 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA988 + difference 4 3) (sourceB988 + difference 3 4) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA988 + difference 4 3) (sourceB988 + difference 3 4) sourceC988) = raw16180 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16180; decide +kernel
    rw [ha]
    exact (canonical16180 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA988 + difference 4 5) (sourceB988 + difference 5 4) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA988 + difference 4 5) (sourceB988 + difference 5 4) sourceC988) = raw14739 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw14739; decide +kernel
    rw [ha]
    exact (canonical14739 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA988 + difference 5 0) (sourceB988 + difference 0 5) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA988 + difference 5 0) (sourceB988 + difference 0 5) sourceC988) = raw16181 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16181; decide +kernel
    rw [ha]
    exact (canonical16181 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA988 + difference 5 1) (sourceB988 + difference 1 5) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA988 + difference 5 1) (sourceB988 + difference 1 5) sourceC988) = raw16182 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16182; decide +kernel
    rw [ha]
    exact (canonical16182 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA988 + difference 5 2) (sourceB988 + difference 2 5) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA988 + difference 5 2) (sourceB988 + difference 2 5) sourceC988) = raw16183 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16183; decide +kernel
    rw [ha]
    exact (canonical16183 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA988 + difference 5 3) (sourceB988 + difference 3 5) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA988 + difference 5 3) (sourceB988 + difference 3 5) sourceC988) = raw16184 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16184; decide +kernel
    rw [ha]
    exact (canonical16184 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA988 + difference 5 4) (sourceB988 + difference 4 5) sourceC988) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3870) := by
    have ha : (tripleCharges (sourceA988 + difference 5 4) (sourceB988 + difference 4 5) sourceC988) = raw16185 := by
      apply Matrix.ext; unfold tripleCharges sourceA988 sourceB988 sourceC988 difference raw16185; decide +kernel
    rw [ha]
    exact (canonical16185 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA988 sourceB988 sourceC988
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm988, Integer.Sparse.eval]
  linarith only [hs]

def sourceA989 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB989 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC989 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm989 : Integer.Sparse Master := [(Sum.inr 2921, 1), (Sum.inr 2922, 1), (Sum.inr 2928, 1), (Sum.inr 2951, 1), (Sum.inr 3097, 1), (Sum.inr 3441, 1), (Sum.inr 3447, 1), (Sum.inr 3464, 1), (Sum.inr 3573, 1), (Sum.inr 3718, 1), (Sum.inr 3722, 1), (Sum.inr 3730, 1), (Sum.inr 3752, 1), (Sum.inr 3762, 1), (Sum.inr 3794, 1), (Sum.inr 3809, 1), (Sum.inr 3839, 1), (Sum.inr 3872, 1), (Sum.inr 3873, 1), (Sum.inr 3950, 1), (Sum.inr 3958, 1), (Sum.inr 3959, 1), (Sum.inr 3971, 1), (Sum.inr 3982, 1), (Sum.inr 3987, 1), (Sum.inr 3990, 1), (Sum.inr 3993, 1), (Sum.inr 4022, 1), (Sum.inr 4027, 1), (Sum.inr 4032, 1)]

theorem sourceEq989 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm989 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA989 + difference 0 1) (sourceB989 + difference 1 0) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3971) := by
    have ha : (tripleCharges (sourceA989 + difference 0 1) (sourceB989 + difference 1 0) sourceC989) = raw15141 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw15141; decide +kernel
    rw [ha]
    exact (canonical15141 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA989 + difference 0 2) (sourceB989 + difference 2 0) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA989 + difference 0 2) (sourceB989 + difference 2 0) sourceC989) = raw16186 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16186; decide +kernel
    rw [ha]
    exact (canonical16186 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA989 + difference 0 3) (sourceB989 + difference 3 0) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA989 + difference 0 3) (sourceB989 + difference 3 0) sourceC989) = raw16187 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16187; decide +kernel
    rw [ha]
    exact (canonical16187 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA989 + difference 0 4) (sourceB989 + difference 4 0) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3950) := by
    have ha : (tripleCharges (sourceA989 + difference 0 4) (sourceB989 + difference 4 0) sourceC989) = raw16188 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16188; decide +kernel
    rw [ha]
    exact (canonical16188 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA989 + difference 0 5) (sourceB989 + difference 5 0) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA989 + difference 0 5) (sourceB989 + difference 5 0) sourceC989) = raw16189 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16189; decide +kernel
    rw [ha]
    exact (canonical16189 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA989 + difference 1 0) (sourceB989 + difference 0 1) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2921) := by
    have ha : (tripleCharges (sourceA989 + difference 1 0) (sourceB989 + difference 0 1) sourceC989) = raw16190 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16190; decide +kernel
    rw [ha]
    exact (canonical16190 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA989 + difference 1 2) (sourceB989 + difference 2 1) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3441) := by
    have ha : (tripleCharges (sourceA989 + difference 1 2) (sourceB989 + difference 2 1) sourceC989) = raw16191 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16191; decide +kernel
    rw [ha]
    exact (canonical16191 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA989 + difference 1 3) (sourceB989 + difference 3 1) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA989 + difference 1 3) (sourceB989 + difference 3 1) sourceC989) = raw16192 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16192; decide +kernel
    rw [ha]
    exact (canonical16192 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA989 + difference 1 4) (sourceB989 + difference 4 1) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3447) := by
    have ha : (tripleCharges (sourceA989 + difference 1 4) (sourceB989 + difference 4 1) sourceC989) = raw16193 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16193; decide +kernel
    rw [ha]
    exact (canonical16193 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA989 + difference 1 5) (sourceB989 + difference 5 1) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA989 + difference 1 5) (sourceB989 + difference 5 1) sourceC989) = raw16194 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16194; decide +kernel
    rw [ha]
    exact (canonical16194 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA989 + difference 2 0) (sourceB989 + difference 0 2) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA989 + difference 2 0) (sourceB989 + difference 0 2) sourceC989) = raw15145 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw15145; decide +kernel
    rw [ha]
    exact (canonical15145 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA989 + difference 2 1) (sourceB989 + difference 1 2) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA989 + difference 2 1) (sourceB989 + difference 1 2) sourceC989) = raw15732 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw15732; decide +kernel
    rw [ha]
    exact (canonical15732 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA989 + difference 2 3) (sourceB989 + difference 3 2) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA989 + difference 2 3) (sourceB989 + difference 3 2) sourceC989) = raw15147 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw15147; decide +kernel
    rw [ha]
    exact (canonical15147 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA989 + difference 2 4) (sourceB989 + difference 4 2) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA989 + difference 2 4) (sourceB989 + difference 4 2) sourceC989) = raw15148 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw15148; decide +kernel
    rw [ha]
    exact (canonical15148 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA989 + difference 2 5) (sourceB989 + difference 5 2) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA989 + difference 2 5) (sourceB989 + difference 5 2) sourceC989) = raw15149 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw15149; decide +kernel
    rw [ha]
    exact (canonical15149 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA989 + difference 3 0) (sourceB989 + difference 0 3) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2922) := by
    have ha : (tripleCharges (sourceA989 + difference 3 0) (sourceB989 + difference 0 3) sourceC989) = raw16195 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16195; decide +kernel
    rw [ha]
    exact (canonical16195 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA989 + difference 3 1) (sourceB989 + difference 1 3) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA989 + difference 3 1) (sourceB989 + difference 1 3) sourceC989) = raw15157 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw15157; decide +kernel
    rw [ha]
    exact (canonical15157 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA989 + difference 3 2) (sourceB989 + difference 2 3) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3718) := by
    have ha : (tripleCharges (sourceA989 + difference 3 2) (sourceB989 + difference 2 3) sourceC989) = raw16196 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16196; decide +kernel
    rw [ha]
    exact (canonical16196 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA989 + difference 3 4) (sourceB989 + difference 4 3) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3752) := by
    have ha : (tripleCharges (sourceA989 + difference 3 4) (sourceB989 + difference 4 3) sourceC989) = raw16197 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16197; decide +kernel
    rw [ha]
    exact (canonical16197 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA989 + difference 3 5) (sourceB989 + difference 5 3) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA989 + difference 3 5) (sourceB989 + difference 5 3) sourceC989) = raw16198 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16198; decide +kernel
    rw [ha]
    exact (canonical16198 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA989 + difference 4 0) (sourceB989 + difference 0 4) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA989 + difference 4 0) (sourceB989 + difference 0 4) sourceC989) = raw16199 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16199; decide +kernel
    rw [ha]
    exact (canonical16199 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA989 + difference 4 1) (sourceB989 + difference 1 4) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA989 + difference 4 1) (sourceB989 + difference 1 4) sourceC989) = raw14790 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw14790; decide +kernel
    rw [ha]
    exact (canonical14790 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA989 + difference 4 2) (sourceB989 + difference 2 4) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3730) := by
    have ha : (tripleCharges (sourceA989 + difference 4 2) (sourceB989 + difference 2 4) sourceC989) = raw16200 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16200; decide +kernel
    rw [ha]
    exact (canonical16200 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA989 + difference 4 3) (sourceB989 + difference 3 4) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA989 + difference 4 3) (sourceB989 + difference 3 4) sourceC989) = raw16201 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16201; decide +kernel
    rw [ha]
    exact (canonical16201 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA989 + difference 4 5) (sourceB989 + difference 5 4) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA989 + difference 4 5) (sourceB989 + difference 5 4) sourceC989) = raw14769 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw14769; decide +kernel
    rw [ha]
    exact (canonical14769 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA989 + difference 5 0) (sourceB989 + difference 0 5) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2928) := by
    have ha : (tripleCharges (sourceA989 + difference 5 0) (sourceB989 + difference 0 5) sourceC989) = raw16202 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16202; decide +kernel
    rw [ha]
    exact (canonical16202 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA989 + difference 5 1) (sourceB989 + difference 1 5) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4032) := by
    have ha : (tripleCharges (sourceA989 + difference 5 1) (sourceB989 + difference 1 5) sourceC989) = raw15164 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw15164; decide +kernel
    rw [ha]
    exact (canonical15164 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA989 + difference 5 2) (sourceB989 + difference 2 5) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3722) := by
    have ha : (tripleCharges (sourceA989 + difference 5 2) (sourceB989 + difference 2 5) sourceC989) = raw16203 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16203; decide +kernel
    rw [ha]
    exact (canonical16203 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA989 + difference 5 3) (sourceB989 + difference 3 5) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4027) := by
    have ha : (tripleCharges (sourceA989 + difference 5 3) (sourceB989 + difference 3 5) sourceC989) = raw16204 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16204; decide +kernel
    rw [ha]
    exact (canonical16204 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA989 + difference 5 4) (sourceB989 + difference 4 5) sourceC989) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4022) := by
    have ha : (tripleCharges (sourceA989 + difference 5 4) (sourceB989 + difference 4 5) sourceC989) = raw16205 := by
      apply Matrix.ext; unfold tripleCharges sourceA989 sourceB989 sourceC989 difference raw16205; decide +kernel
    rw [ha]
    exact (canonical16205 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA989 sourceB989 sourceC989
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm989, Integer.Sparse.eval]
  linarith only [hs]

def sourceA990 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB990 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC990 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm990 : Integer.Sparse Master := [(Sum.inr 3781, 1), (Sum.inr 3848, 1), (Sum.inr 3944, 1), (Sum.inr 3946, 1), (Sum.inr 3961, 1), (Sum.inr 4044, 1), (Sum.inr 4092, -1)]

theorem sourceEq990 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm990 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA990 + difference 0 0) (sourceB990 + difference 0 0) sourceC990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA990 + difference 0 0) (sourceB990 + difference 0 0) sourceC990) = raw16206 := by
      apply Matrix.ext; unfold tripleCharges sourceA990 sourceB990 sourceC990 difference raw16206; decide +kernel
    rw [ha]
    exact (canonical16206 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA990 + difference 0 1) (sourceB990 + difference 1 0) sourceC990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4044) := by
    have ha : (tripleCharges (sourceA990 + difference 0 1) (sourceB990 + difference 1 0) sourceC990) = raw16207 := by
      apply Matrix.ext; unfold tripleCharges sourceA990 sourceB990 sourceC990 difference raw16207; decide +kernel
    rw [ha]
    exact (canonical16207 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA990 + difference 0 2) (sourceB990 + difference 2 0) sourceC990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA990 + difference 0 2) (sourceB990 + difference 2 0) sourceC990) = raw16208 := by
      apply Matrix.ext; unfold tripleCharges sourceA990 sourceB990 sourceC990 difference raw16208; decide +kernel
    rw [ha]
    exact (canonical16208 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA990 + difference 0 3) (sourceB990 + difference 3 0) sourceC990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA990 + difference 0 3) (sourceB990 + difference 3 0) sourceC990) = raw16209 := by
      apply Matrix.ext; unfold tripleCharges sourceA990 sourceB990 sourceC990 difference raw16209; decide +kernel
    rw [ha]
    exact (canonical16209 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA990 + difference 0 4) (sourceB990 + difference 4 0) sourceC990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3944) := by
    have ha : (tripleCharges (sourceA990 + difference 0 4) (sourceB990 + difference 4 0) sourceC990) = raw16210 := by
      apply Matrix.ext; unfold tripleCharges sourceA990 sourceB990 sourceC990 difference raw16210; decide +kernel
    rw [ha]
    exact (canonical16210 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA990 + difference 0 5) (sourceB990 + difference 5 0) sourceC990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3781) := by
    have ha : (tripleCharges (sourceA990 + difference 0 5) (sourceB990 + difference 5 0) sourceC990) = raw16211 := by
      apply Matrix.ext; unfold tripleCharges sourceA990 sourceB990 sourceC990 difference raw16211; decide +kernel
    rw [ha]
    exact (canonical16211 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA990 + sourceB990) sourceC990) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA990 + sourceB990) sourceC990) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA990 sourceB990 sourceC990 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA990 sourceB990 sourceC990
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm990, Integer.Sparse.eval]
  linarith only [hs]

def sourceA991 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB991 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC991 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm991 : Integer.Sparse Master := [(Sum.inr 2977, 1), (Sum.inr 3723, 1), (Sum.inr 3725, 1), (Sum.inr 3730, 1), (Sum.inr 3848, 1), (Sum.inr 3946, 1), (Sum.inr 4092, -1)]

theorem sourceEq991 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm991 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA991 + difference 0 2) (sourceB991 + difference 2 0) sourceC991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA991 + difference 0 2) (sourceB991 + difference 2 0) sourceC991) = raw16208 := by
      apply Matrix.ext; unfold tripleCharges sourceA991 sourceB991 sourceC991 difference raw16208; decide +kernel
    rw [ha]
    exact (canonical16208 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA991 + difference 1 2) (sourceB991 + difference 2 1) sourceC991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2977) := by
    have ha : (tripleCharges (sourceA991 + difference 1 2) (sourceB991 + difference 2 1) sourceC991) = raw16212 := by
      apply Matrix.ext; unfold tripleCharges sourceA991 sourceB991 sourceC991 difference raw16212; decide +kernel
    rw [ha]
    exact (canonical16212 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA991 + difference 2 2) (sourceB991 + difference 2 2) sourceC991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA991 + difference 2 2) (sourceB991 + difference 2 2) sourceC991) = raw16206 := by
      apply Matrix.ext; unfold tripleCharges sourceA991 sourceB991 sourceC991 difference raw16206; decide +kernel
    rw [ha]
    exact (canonical16206 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA991 + difference 3 2) (sourceB991 + difference 2 3) sourceC991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3725) := by
    have ha : (tripleCharges (sourceA991 + difference 3 2) (sourceB991 + difference 2 3) sourceC991) = raw16213 := by
      apply Matrix.ext; unfold tripleCharges sourceA991 sourceB991 sourceC991 difference raw16213; decide +kernel
    rw [ha]
    exact (canonical16213 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA991 + difference 4 2) (sourceB991 + difference 2 4) sourceC991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3730) := by
    have ha : (tripleCharges (sourceA991 + difference 4 2) (sourceB991 + difference 2 4) sourceC991) = raw16214 := by
      apply Matrix.ext; unfold tripleCharges sourceA991 sourceB991 sourceC991 difference raw16214; decide +kernel
    rw [ha]
    exact (canonical16214 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA991 + difference 5 2) (sourceB991 + difference 2 5) sourceC991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3723) := by
    have ha : (tripleCharges (sourceA991 + difference 5 2) (sourceB991 + difference 2 5) sourceC991) = raw16215 := by
      apply Matrix.ext; unfold tripleCharges sourceA991 sourceB991 sourceC991 difference raw16215; decide +kernel
    rw [ha]
    exact (canonical16215 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA991 + sourceB991) sourceC991) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA991 + sourceB991) sourceC991) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA991 sourceB991 sourceC991 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA991 sourceB991 sourceC991
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm991, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
