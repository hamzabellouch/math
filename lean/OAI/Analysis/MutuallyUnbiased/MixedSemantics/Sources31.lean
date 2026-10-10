import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical114
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical115
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical117
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical118
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical122
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical123
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical124
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical127
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical128
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical129
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical130

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA992 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB992 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC992 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm992 : Integer.Sparse Master := [(Sum.inr 2975, 1), (Sum.inr 3826, 1), (Sum.inr 3828, 1), (Sum.inr 3848, 1), (Sum.inr 3884, 1), (Sum.inr 3944, 1), (Sum.inr 4092, -1)]

theorem sourceEq992 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm992 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA992 + difference 0 4) (sourceB992 + difference 4 0) sourceC992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3944) := by
    have ha : (tripleCharges (sourceA992 + difference 0 4) (sourceB992 + difference 4 0) sourceC992) = raw16210 := by
      apply Matrix.ext; unfold tripleCharges sourceA992 sourceB992 sourceC992 difference raw16210; decide +kernel
    rw [ha]
    exact (canonical16210 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA992 + difference 1 4) (sourceB992 + difference 4 1) sourceC992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2975) := by
    have ha : (tripleCharges (sourceA992 + difference 1 4) (sourceB992 + difference 4 1) sourceC992) = raw16216 := by
      apply Matrix.ext; unfold tripleCharges sourceA992 sourceB992 sourceC992 difference raw16216; decide +kernel
    rw [ha]
    exact (canonical16216 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA992 + difference 2 4) (sourceB992 + difference 4 2) sourceC992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA992 + difference 2 4) (sourceB992 + difference 4 2) sourceC992) = raw15744 := by
      apply Matrix.ext; unfold tripleCharges sourceA992 sourceB992 sourceC992 difference raw15744; decide +kernel
    rw [ha]
    exact (canonical15744 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA992 + difference 3 4) (sourceB992 + difference 4 3) sourceC992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3828) := by
    have ha : (tripleCharges (sourceA992 + difference 3 4) (sourceB992 + difference 4 3) sourceC992) = raw16217 := by
      apply Matrix.ext; unfold tripleCharges sourceA992 sourceB992 sourceC992 difference raw16217; decide +kernel
    rw [ha]
    exact (canonical16217 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA992 + difference 4 4) (sourceB992 + difference 4 4) sourceC992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA992 + difference 4 4) (sourceB992 + difference 4 4) sourceC992) = raw16206 := by
      apply Matrix.ext; unfold tripleCharges sourceA992 sourceB992 sourceC992 difference raw16206; decide +kernel
    rw [ha]
    exact (canonical16206 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA992 + difference 5 4) (sourceB992 + difference 4 5) sourceC992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3826) := by
    have ha : (tripleCharges (sourceA992 + difference 5 4) (sourceB992 + difference 4 5) sourceC992) = raw16218 := by
      apply Matrix.ext; unfold tripleCharges sourceA992 sourceB992 sourceC992 difference raw16218; decide +kernel
    rw [ha]
    exact (canonical16218 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA992 + sourceB992) sourceC992) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA992 + sourceB992) sourceC992) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA992 sourceB992 sourceC992 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA992 sourceB992 sourceC992
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm992, Integer.Sparse.eval]
  linarith only [hs]

def sourceA993 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB993 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC993 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceForm993 : Integer.Sparse Master := [(Sum.inr 5105, 2), (Sum.inr 5109, 1), (Sum.inr 5110, 1), (Sum.inr 5203, 2), (Sum.inr 5207, 1), (Sum.inr 5237, 2), (Sum.inr 5238, 1), (Sum.inr 5293, 1), (Sum.inr 5304, 1), (Sum.inr 5310, 1), (Sum.inr 5370, 2), (Sum.inr 5422, 2), (Sum.inr 5434, 2), (Sum.inr 5443, 1), (Sum.inr 5450, 2), (Sum.inr 5451, 2), (Sum.inr 5454, 1), (Sum.inr 5455, 1), (Sum.inr 5484, 2), (Sum.inr 5492, 1), (Sum.inr 5494, 1)]

theorem sourceEq993 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm993 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA993 + difference 0 1) (sourceB993 + difference 1 0) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA993 + difference 0 1) (sourceB993 + difference 1 0) sourceC993) = raw16219 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16219; decide +kernel
    rw [ha]
    exact (canonical16219 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA993 + difference 0 2) (sourceB993 + difference 2 0) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA993 + difference 0 2) (sourceB993 + difference 2 0) sourceC993) = raw16220 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16220; decide +kernel
    rw [ha]
    exact (canonical16220 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA993 + difference 0 3) (sourceB993 + difference 3 0) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA993 + difference 0 3) (sourceB993 + difference 3 0) sourceC993) = raw16221 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16221; decide +kernel
    rw [ha]
    exact (canonical16221 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA993 + difference 0 4) (sourceB993 + difference 4 0) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5494) := by
    have ha : (tripleCharges (sourceA993 + difference 0 4) (sourceB993 + difference 4 0) sourceC993) = raw16222 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16222; decide +kernel
    rw [ha]
    exact (canonical16222 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA993 + difference 0 5) (sourceB993 + difference 5 0) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA993 + difference 0 5) (sourceB993 + difference 5 0) sourceC993) = raw16223 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16223; decide +kernel
    rw [ha]
    exact (canonical16223 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA993 + difference 1 0) (sourceB993 + difference 0 1) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA993 + difference 1 0) (sourceB993 + difference 0 1) sourceC993) = raw16224 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16224; decide +kernel
    rw [ha]
    exact (canonical16224 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA993 + difference 1 2) (sourceB993 + difference 2 1) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA993 + difference 1 2) (sourceB993 + difference 2 1) sourceC993) = raw16225 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16225; decide +kernel
    rw [ha]
    exact (canonical16225 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA993 + difference 1 3) (sourceB993 + difference 3 1) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA993 + difference 1 3) (sourceB993 + difference 3 1) sourceC993) = raw16226 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16226; decide +kernel
    rw [ha]
    exact (canonical16226 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA993 + difference 1 4) (sourceB993 + difference 4 1) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA993 + difference 1 4) (sourceB993 + difference 4 1) sourceC993) = raw16227 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16227; decide +kernel
    rw [ha]
    exact (canonical16227 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA993 + difference 1 5) (sourceB993 + difference 5 1) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA993 + difference 1 5) (sourceB993 + difference 5 1) sourceC993) = raw16228 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16228; decide +kernel
    rw [ha]
    exact (canonical16228 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA993 + difference 2 0) (sourceB993 + difference 0 2) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA993 + difference 2 0) (sourceB993 + difference 0 2) sourceC993) = raw16229 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16229; decide +kernel
    rw [ha]
    exact (canonical16229 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA993 + difference 2 1) (sourceB993 + difference 1 2) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA993 + difference 2 1) (sourceB993 + difference 1 2) sourceC993) = raw16230 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16230; decide +kernel
    rw [ha]
    exact (canonical16230 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA993 + difference 2 3) (sourceB993 + difference 3 2) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA993 + difference 2 3) (sourceB993 + difference 3 2) sourceC993) = raw16231 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16231; decide +kernel
    rw [ha]
    exact (canonical16231 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA993 + difference 2 4) (sourceB993 + difference 4 2) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA993 + difference 2 4) (sourceB993 + difference 4 2) sourceC993) = raw16232 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16232; decide +kernel
    rw [ha]
    exact (canonical16232 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA993 + difference 2 5) (sourceB993 + difference 5 2) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA993 + difference 2 5) (sourceB993 + difference 5 2) sourceC993) = raw16233 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16233; decide +kernel
    rw [ha]
    exact (canonical16233 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA993 + difference 3 0) (sourceB993 + difference 0 3) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA993 + difference 3 0) (sourceB993 + difference 0 3) sourceC993) = raw16234 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16234; decide +kernel
    rw [ha]
    exact (canonical16234 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA993 + difference 3 1) (sourceB993 + difference 1 3) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA993 + difference 3 1) (sourceB993 + difference 1 3) sourceC993) = raw16235 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16235; decide +kernel
    rw [ha]
    exact (canonical16235 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA993 + difference 3 2) (sourceB993 + difference 2 3) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA993 + difference 3 2) (sourceB993 + difference 2 3) sourceC993) = raw16236 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16236; decide +kernel
    rw [ha]
    exact (canonical16236 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA993 + difference 3 4) (sourceB993 + difference 4 3) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA993 + difference 3 4) (sourceB993 + difference 4 3) sourceC993) = raw16237 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16237; decide +kernel
    rw [ha]
    exact (canonical16237 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA993 + difference 3 5) (sourceB993 + difference 5 3) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA993 + difference 3 5) (sourceB993 + difference 5 3) sourceC993) = raw16238 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16238; decide +kernel
    rw [ha]
    exact (canonical16238 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA993 + difference 4 0) (sourceB993 + difference 0 4) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA993 + difference 4 0) (sourceB993 + difference 0 4) sourceC993) = raw16239 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16239; decide +kernel
    rw [ha]
    exact (canonical16239 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA993 + difference 4 1) (sourceB993 + difference 1 4) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA993 + difference 4 1) (sourceB993 + difference 1 4) sourceC993) = raw16240 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16240; decide +kernel
    rw [ha]
    exact (canonical16240 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA993 + difference 4 2) (sourceB993 + difference 2 4) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA993 + difference 4 2) (sourceB993 + difference 2 4) sourceC993) = raw16241 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16241; decide +kernel
    rw [ha]
    exact (canonical16241 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA993 + difference 4 3) (sourceB993 + difference 3 4) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA993 + difference 4 3) (sourceB993 + difference 3 4) sourceC993) = raw16242 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16242; decide +kernel
    rw [ha]
    exact (canonical16242 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA993 + difference 4 5) (sourceB993 + difference 5 4) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA993 + difference 4 5) (sourceB993 + difference 5 4) sourceC993) = raw16243 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16243; decide +kernel
    rw [ha]
    exact (canonical16243 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA993 + difference 5 0) (sourceB993 + difference 0 5) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA993 + difference 5 0) (sourceB993 + difference 0 5) sourceC993) = raw16244 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16244; decide +kernel
    rw [ha]
    exact (canonical16244 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA993 + difference 5 1) (sourceB993 + difference 1 5) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA993 + difference 5 1) (sourceB993 + difference 1 5) sourceC993) = raw16245 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16245; decide +kernel
    rw [ha]
    exact (canonical16245 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA993 + difference 5 2) (sourceB993 + difference 2 5) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA993 + difference 5 2) (sourceB993 + difference 2 5) sourceC993) = raw16246 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16246; decide +kernel
    rw [ha]
    exact (canonical16246 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA993 + difference 5 3) (sourceB993 + difference 3 5) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA993 + difference 5 3) (sourceB993 + difference 3 5) sourceC993) = raw16247 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16247; decide +kernel
    rw [ha]
    exact (canonical16247 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA993 + difference 5 4) (sourceB993 + difference 4 5) sourceC993) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA993 + difference 5 4) (sourceB993 + difference 4 5) sourceC993) = raw16248 := by
      apply Matrix.ext; unfold tripleCharges sourceA993 sourceB993 sourceC993 difference raw16248; decide +kernel
    rw [ha]
    exact (canonical16248 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA993 sourceB993 sourceC993
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm993, Integer.Sparse.eval]
  linarith only [hs]

def sourceA994 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB994 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC994 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceForm994 : Integer.Sparse Master := [(Sum.inr 2515, 2), (Sum.inr 2519, 1), (Sum.inr 2522, 1), (Sum.inr 2788, 1), (Sum.inr 2884, 2), (Sum.inr 2889, 1), (Sum.inr 3102, 1), (Sum.inr 3394, 2), (Sum.inr 3397, 1), (Sum.inr 3583, 1), (Sum.inr 3706, 2), (Sum.inr 3862, 1), (Sum.inr 3964, 2), (Sum.inr 3982, 2), (Sum.inr 3983, 2), (Sum.inr 3987, 2), (Sum.inr 4015, 1), (Sum.inr 4019, 1), (Sum.inr 4020, 1), (Sum.inr 4029, 2), (Sum.inr 4040, 1)]

theorem sourceEq994 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm994 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA994 + difference 0 1) (sourceB994 + difference 1 0) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA994 + difference 0 1) (sourceB994 + difference 1 0) sourceC994) = raw16249 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16249; decide +kernel
    rw [ha]
    exact (canonical16249 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA994 + difference 0 2) (sourceB994 + difference 2 0) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA994 + difference 0 2) (sourceB994 + difference 2 0) sourceC994) = raw16250 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16250; decide +kernel
    rw [ha]
    exact (canonical16250 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA994 + difference 0 3) (sourceB994 + difference 3 0) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA994 + difference 0 3) (sourceB994 + difference 3 0) sourceC994) = raw16251 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16251; decide +kernel
    rw [ha]
    exact (canonical16251 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA994 + difference 0 4) (sourceB994 + difference 4 0) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4020) := by
    have ha : (tripleCharges (sourceA994 + difference 0 4) (sourceB994 + difference 4 0) sourceC994) = raw16252 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16252; decide +kernel
    rw [ha]
    exact (canonical16252 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA994 + difference 0 5) (sourceB994 + difference 5 0) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4015) := by
    have ha : (tripleCharges (sourceA994 + difference 0 5) (sourceB994 + difference 5 0) sourceC994) = raw16253 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16253; decide +kernel
    rw [ha]
    exact (canonical16253 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA994 + difference 1 0) (sourceB994 + difference 0 1) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA994 + difference 1 0) (sourceB994 + difference 0 1) sourceC994) = raw16254 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16254; decide +kernel
    rw [ha]
    exact (canonical16254 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA994 + difference 1 2) (sourceB994 + difference 2 1) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA994 + difference 1 2) (sourceB994 + difference 2 1) sourceC994) = raw16255 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16255; decide +kernel
    rw [ha]
    exact (canonical16255 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA994 + difference 1 3) (sourceB994 + difference 3 1) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA994 + difference 1 3) (sourceB994 + difference 3 1) sourceC994) = raw16256 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16256; decide +kernel
    rw [ha]
    exact (canonical16256 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA994 + difference 1 4) (sourceB994 + difference 4 1) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4019) := by
    have ha : (tripleCharges (sourceA994 + difference 1 4) (sourceB994 + difference 4 1) sourceC994) = raw16257 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16257; decide +kernel
    rw [ha]
    exact (canonical16257 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA994 + difference 1 5) (sourceB994 + difference 5 1) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4040) := by
    have ha : (tripleCharges (sourceA994 + difference 1 5) (sourceB994 + difference 5 1) sourceC994) = raw16258 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16258; decide +kernel
    rw [ha]
    exact (canonical16258 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA994 + difference 2 0) (sourceB994 + difference 0 2) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA994 + difference 2 0) (sourceB994 + difference 0 2) sourceC994) = raw16259 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16259; decide +kernel
    rw [ha]
    exact (canonical16259 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA994 + difference 2 1) (sourceB994 + difference 1 2) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3394) := by
    have ha : (tripleCharges (sourceA994 + difference 2 1) (sourceB994 + difference 1 2) sourceC994) = raw16260 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16260; decide +kernel
    rw [ha]
    exact (canonical16260 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA994 + difference 2 3) (sourceB994 + difference 3 2) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3964) := by
    have ha : (tripleCharges (sourceA994 + difference 2 3) (sourceB994 + difference 3 2) sourceC994) = raw16261 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16261; decide +kernel
    rw [ha]
    exact (canonical16261 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA994 + difference 2 4) (sourceB994 + difference 4 2) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA994 + difference 2 4) (sourceB994 + difference 4 2) sourceC994) = raw16262 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16262; decide +kernel
    rw [ha]
    exact (canonical16262 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA994 + difference 2 5) (sourceB994 + difference 5 2) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA994 + difference 2 5) (sourceB994 + difference 5 2) sourceC994) = raw16263 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16263; decide +kernel
    rw [ha]
    exact (canonical16263 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA994 + difference 3 0) (sourceB994 + difference 0 3) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA994 + difference 3 0) (sourceB994 + difference 0 3) sourceC994) = raw16264 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16264; decide +kernel
    rw [ha]
    exact (canonical16264 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA994 + difference 3 1) (sourceB994 + difference 1 3) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3394) := by
    have ha : (tripleCharges (sourceA994 + difference 3 1) (sourceB994 + difference 1 3) sourceC994) = raw16265 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16265; decide +kernel
    rw [ha]
    exact (canonical16265 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA994 + difference 3 2) (sourceB994 + difference 2 3) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3964) := by
    have ha : (tripleCharges (sourceA994 + difference 3 2) (sourceB994 + difference 2 3) sourceC994) = raw16266 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16266; decide +kernel
    rw [ha]
    exact (canonical16266 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA994 + difference 3 4) (sourceB994 + difference 4 3) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA994 + difference 3 4) (sourceB994 + difference 4 3) sourceC994) = raw16267 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16267; decide +kernel
    rw [ha]
    exact (canonical16267 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA994 + difference 3 5) (sourceB994 + difference 5 3) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA994 + difference 3 5) (sourceB994 + difference 5 3) sourceC994) = raw16268 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16268; decide +kernel
    rw [ha]
    exact (canonical16268 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA994 + difference 4 0) (sourceB994 + difference 0 4) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA994 + difference 4 0) (sourceB994 + difference 0 4) sourceC994) = raw16269 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16269; decide +kernel
    rw [ha]
    exact (canonical16269 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA994 + difference 4 1) (sourceB994 + difference 1 4) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3397) := by
    have ha : (tripleCharges (sourceA994 + difference 4 1) (sourceB994 + difference 1 4) sourceC994) = raw16270 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16270; decide +kernel
    rw [ha]
    exact (canonical16270 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA994 + difference 4 2) (sourceB994 + difference 2 4) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA994 + difference 4 2) (sourceB994 + difference 2 4) sourceC994) = raw16271 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16271; decide +kernel
    rw [ha]
    exact (canonical16271 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA994 + difference 4 3) (sourceB994 + difference 3 4) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA994 + difference 4 3) (sourceB994 + difference 3 4) sourceC994) = raw16272 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16272; decide +kernel
    rw [ha]
    exact (canonical16272 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA994 + difference 4 5) (sourceB994 + difference 5 4) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA994 + difference 4 5) (sourceB994 + difference 5 4) sourceC994) = raw16273 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16273; decide +kernel
    rw [ha]
    exact (canonical16273 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA994 + difference 5 0) (sourceB994 + difference 0 5) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA994 + difference 5 0) (sourceB994 + difference 0 5) sourceC994) = raw16274 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16274; decide +kernel
    rw [ha]
    exact (canonical16274 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA994 + difference 5 1) (sourceB994 + difference 1 5) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA994 + difference 5 1) (sourceB994 + difference 1 5) sourceC994) = raw16275 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16275; decide +kernel
    rw [ha]
    exact (canonical16275 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA994 + difference 5 2) (sourceB994 + difference 2 5) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA994 + difference 5 2) (sourceB994 + difference 2 5) sourceC994) = raw16276 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16276; decide +kernel
    rw [ha]
    exact (canonical16276 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA994 + difference 5 3) (sourceB994 + difference 3 5) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA994 + difference 5 3) (sourceB994 + difference 3 5) sourceC994) = raw16277 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16277; decide +kernel
    rw [ha]
    exact (canonical16277 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA994 + difference 5 4) (sourceB994 + difference 4 5) sourceC994) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA994 + difference 5 4) (sourceB994 + difference 4 5) sourceC994) = raw16278 := by
      apply Matrix.ext; unfold tripleCharges sourceA994 sourceB994 sourceC994 difference raw16278; decide +kernel
    rw [ha]
    exact (canonical16278 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA994 sourceB994 sourceC994
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm994, Integer.Sparse.eval]
  linarith only [hs]

def sourceA995 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB995 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC995 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceForm995 : Integer.Sparse Master := [(Sum.inr 4866, 2), (Sum.inr 4868, 1), (Sum.inr 4875, 1), (Sum.inr 4896, 1), (Sum.inr 5163, 2), (Sum.inr 5176, 1), (Sum.inr 5291, 1), (Sum.inr 5388, 2), (Sum.inr 5390, 1), (Sum.inr 5401, 2), (Sum.inr 5404, 2), (Sum.inr 5411, 2), (Sum.inr 5438, 2), (Sum.inr 5442, 1), (Sum.inr 5443, 1), (Sum.inr 5450, 2), (Sum.inr 5451, 1), (Sum.inr 5453, 1), (Sum.inr 5485, 2), (Sum.inr 5492, 1), (Sum.inr 5493, 1)]

theorem sourceEq995 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm995 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA995 + difference 0 1) (sourceB995 + difference 1 0) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA995 + difference 0 1) (sourceB995 + difference 1 0) sourceC995) = raw16279 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16279; decide +kernel
    rw [ha]
    exact (canonical16279 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA995 + difference 0 2) (sourceB995 + difference 2 0) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA995 + difference 0 2) (sourceB995 + difference 2 0) sourceC995) = raw16280 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16280; decide +kernel
    rw [ha]
    exact (canonical16280 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA995 + difference 0 3) (sourceB995 + difference 3 0) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA995 + difference 0 3) (sourceB995 + difference 3 0) sourceC995) = raw16281 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16281; decide +kernel
    rw [ha]
    exact (canonical16281 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA995 + difference 0 4) (sourceB995 + difference 4 0) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA995 + difference 0 4) (sourceB995 + difference 4 0) sourceC995) = raw16282 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16282; decide +kernel
    rw [ha]
    exact (canonical16282 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA995 + difference 0 5) (sourceB995 + difference 5 0) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA995 + difference 0 5) (sourceB995 + difference 5 0) sourceC995) = raw16283 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16283; decide +kernel
    rw [ha]
    exact (canonical16283 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA995 + difference 1 0) (sourceB995 + difference 0 1) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA995 + difference 1 0) (sourceB995 + difference 0 1) sourceC995) = raw16284 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16284; decide +kernel
    rw [ha]
    exact (canonical16284 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA995 + difference 1 2) (sourceB995 + difference 2 1) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA995 + difference 1 2) (sourceB995 + difference 2 1) sourceC995) = raw10901 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw10901; decide +kernel
    rw [ha]
    exact (canonical10901 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA995 + difference 1 3) (sourceB995 + difference 3 1) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA995 + difference 1 3) (sourceB995 + difference 3 1) sourceC995) = raw10902 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw10902; decide +kernel
    rw [ha]
    exact (canonical10902 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA995 + difference 1 4) (sourceB995 + difference 4 1) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA995 + difference 1 4) (sourceB995 + difference 4 1) sourceC995) = raw10903 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw10903; decide +kernel
    rw [ha]
    exact (canonical10903 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA995 + difference 1 5) (sourceB995 + difference 5 1) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA995 + difference 1 5) (sourceB995 + difference 5 1) sourceC995) = raw10904 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw10904; decide +kernel
    rw [ha]
    exact (canonical10904 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA995 + difference 2 0) (sourceB995 + difference 0 2) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA995 + difference 2 0) (sourceB995 + difference 0 2) sourceC995) = raw10911 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw10911; decide +kernel
    rw [ha]
    exact (canonical10911 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA995 + difference 2 1) (sourceB995 + difference 1 2) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA995 + difference 2 1) (sourceB995 + difference 1 2) sourceC995) = raw16285 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16285; decide +kernel
    rw [ha]
    exact (canonical16285 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA995 + difference 2 3) (sourceB995 + difference 3 2) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA995 + difference 2 3) (sourceB995 + difference 3 2) sourceC995) = raw16286 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16286; decide +kernel
    rw [ha]
    exact (canonical16286 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA995 + difference 2 4) (sourceB995 + difference 4 2) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA995 + difference 2 4) (sourceB995 + difference 4 2) sourceC995) = raw16287 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16287; decide +kernel
    rw [ha]
    exact (canonical16287 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA995 + difference 2 5) (sourceB995 + difference 5 2) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA995 + difference 2 5) (sourceB995 + difference 5 2) sourceC995) = raw16288 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16288; decide +kernel
    rw [ha]
    exact (canonical16288 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA995 + difference 3 0) (sourceB995 + difference 0 3) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA995 + difference 3 0) (sourceB995 + difference 0 3) sourceC995) = raw10916 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw10916; decide +kernel
    rw [ha]
    exact (canonical10916 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA995 + difference 3 1) (sourceB995 + difference 1 3) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA995 + difference 3 1) (sourceB995 + difference 1 3) sourceC995) = raw16289 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16289; decide +kernel
    rw [ha]
    exact (canonical16289 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA995 + difference 3 2) (sourceB995 + difference 2 3) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA995 + difference 3 2) (sourceB995 + difference 2 3) sourceC995) = raw16290 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16290; decide +kernel
    rw [ha]
    exact (canonical16290 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA995 + difference 3 4) (sourceB995 + difference 4 3) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA995 + difference 3 4) (sourceB995 + difference 4 3) sourceC995) = raw16291 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16291; decide +kernel
    rw [ha]
    exact (canonical16291 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA995 + difference 3 5) (sourceB995 + difference 5 3) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA995 + difference 3 5) (sourceB995 + difference 5 3) sourceC995) = raw16292 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16292; decide +kernel
    rw [ha]
    exact (canonical16292 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA995 + difference 4 0) (sourceB995 + difference 0 4) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA995 + difference 4 0) (sourceB995 + difference 0 4) sourceC995) = raw10921 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw10921; decide +kernel
    rw [ha]
    exact (canonical10921 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA995 + difference 4 1) (sourceB995 + difference 1 4) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA995 + difference 4 1) (sourceB995 + difference 1 4) sourceC995) = raw16293 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16293; decide +kernel
    rw [ha]
    exact (canonical16293 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA995 + difference 4 2) (sourceB995 + difference 2 4) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA995 + difference 4 2) (sourceB995 + difference 2 4) sourceC995) = raw16294 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16294; decide +kernel
    rw [ha]
    exact (canonical16294 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA995 + difference 4 3) (sourceB995 + difference 3 4) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA995 + difference 4 3) (sourceB995 + difference 3 4) sourceC995) = raw16295 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16295; decide +kernel
    rw [ha]
    exact (canonical16295 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA995 + difference 4 5) (sourceB995 + difference 5 4) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA995 + difference 4 5) (sourceB995 + difference 5 4) sourceC995) = raw16296 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16296; decide +kernel
    rw [ha]
    exact (canonical16296 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA995 + difference 5 0) (sourceB995 + difference 0 5) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA995 + difference 5 0) (sourceB995 + difference 0 5) sourceC995) = raw10926 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw10926; decide +kernel
    rw [ha]
    exact (canonical10926 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA995 + difference 5 1) (sourceB995 + difference 1 5) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA995 + difference 5 1) (sourceB995 + difference 1 5) sourceC995) = raw16297 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16297; decide +kernel
    rw [ha]
    exact (canonical16297 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA995 + difference 5 2) (sourceB995 + difference 2 5) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA995 + difference 5 2) (sourceB995 + difference 2 5) sourceC995) = raw16298 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16298; decide +kernel
    rw [ha]
    exact (canonical16298 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA995 + difference 5 3) (sourceB995 + difference 3 5) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA995 + difference 5 3) (sourceB995 + difference 3 5) sourceC995) = raw16299 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16299; decide +kernel
    rw [ha]
    exact (canonical16299 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA995 + difference 5 4) (sourceB995 + difference 4 5) sourceC995) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA995 + difference 5 4) (sourceB995 + difference 4 5) sourceC995) = raw16300 := by
      apply Matrix.ext; unfold tripleCharges sourceA995 sourceB995 sourceC995 difference raw16300; decide +kernel
    rw [ha]
    exact (canonical16300 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA995 sourceB995 sourceC995
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm995, Integer.Sparse.eval]
  linarith only [hs]

def sourceA996 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB996 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC996 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceForm996 : Integer.Sparse Master := [(Sum.inr 2107, 2), (Sum.inr 2109, 1), (Sum.inr 2116, 1), (Sum.inr 2278, 1), (Sum.inr 2590, 2), (Sum.inr 2604, 1), (Sum.inr 2765, 1), (Sum.inr 3737, 2), (Sum.inr 3741, 1), (Sum.inr 3787, 2), (Sum.inr 3790, 2), (Sum.inr 3813, 2), (Sum.inr 3876, 2), (Sum.inr 3887, 2), (Sum.inr 3888, 1), (Sum.inr 3907, 1), (Sum.inr 3915, 1), (Sum.inr 3998, 2), (Sum.inr 4001, 1), (Sum.inr 4017, 1), (Sum.inr 4018, 1)]

theorem sourceEq996 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm996 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA996 + difference 0 1) (sourceB996 + difference 1 0) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA996 + difference 0 1) (sourceB996 + difference 1 0) sourceC996) = raw16301 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16301; decide +kernel
    rw [ha]
    exact (canonical16301 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA996 + difference 0 2) (sourceB996 + difference 2 0) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA996 + difference 0 2) (sourceB996 + difference 2 0) sourceC996) = raw16302 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16302; decide +kernel
    rw [ha]
    exact (canonical16302 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA996 + difference 0 3) (sourceB996 + difference 3 0) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA996 + difference 0 3) (sourceB996 + difference 3 0) sourceC996) = raw16303 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16303; decide +kernel
    rw [ha]
    exact (canonical16303 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA996 + difference 0 4) (sourceB996 + difference 4 0) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4017) := by
    have ha : (tripleCharges (sourceA996 + difference 0 4) (sourceB996 + difference 4 0) sourceC996) = raw16304 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16304; decide +kernel
    rw [ha]
    exact (canonical16304 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA996 + difference 0 5) (sourceB996 + difference 5 0) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4018) := by
    have ha : (tripleCharges (sourceA996 + difference 0 5) (sourceB996 + difference 5 0) sourceC996) = raw16305 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16305; decide +kernel
    rw [ha]
    exact (canonical16305 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA996 + difference 1 0) (sourceB996 + difference 0 1) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA996 + difference 1 0) (sourceB996 + difference 0 1) sourceC996) = raw16306 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16306; decide +kernel
    rw [ha]
    exact (canonical16306 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA996 + difference 1 2) (sourceB996 + difference 2 1) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA996 + difference 1 2) (sourceB996 + difference 2 1) sourceC996) = raw10931 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw10931; decide +kernel
    rw [ha]
    exact (canonical10931 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA996 + difference 1 3) (sourceB996 + difference 3 1) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA996 + difference 1 3) (sourceB996 + difference 3 1) sourceC996) = raw10932 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw10932; decide +kernel
    rw [ha]
    exact (canonical10932 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA996 + difference 1 4) (sourceB996 + difference 4 1) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA996 + difference 1 4) (sourceB996 + difference 4 1) sourceC996) = raw10933 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw10933; decide +kernel
    rw [ha]
    exact (canonical10933 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA996 + difference 1 5) (sourceB996 + difference 5 1) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3915) := by
    have ha : (tripleCharges (sourceA996 + difference 1 5) (sourceB996 + difference 5 1) sourceC996) = raw10934 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw10934; decide +kernel
    rw [ha]
    exact (canonical10934 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA996 + difference 2 0) (sourceB996 + difference 0 2) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA996 + difference 2 0) (sourceB996 + difference 0 2) sourceC996) = raw10941 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw10941; decide +kernel
    rw [ha]
    exact (canonical10941 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA996 + difference 2 1) (sourceB996 + difference 1 2) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3737) := by
    have ha : (tripleCharges (sourceA996 + difference 2 1) (sourceB996 + difference 1 2) sourceC996) = raw16307 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16307; decide +kernel
    rw [ha]
    exact (canonical16307 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA996 + difference 2 3) (sourceB996 + difference 3 2) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3787) := by
    have ha : (tripleCharges (sourceA996 + difference 2 3) (sourceB996 + difference 3 2) sourceC996) = raw16308 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16308; decide +kernel
    rw [ha]
    exact (canonical16308 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA996 + difference 2 4) (sourceB996 + difference 4 2) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA996 + difference 2 4) (sourceB996 + difference 4 2) sourceC996) = raw16309 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16309; decide +kernel
    rw [ha]
    exact (canonical16309 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA996 + difference 2 5) (sourceB996 + difference 5 2) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA996 + difference 2 5) (sourceB996 + difference 5 2) sourceC996) = raw16310 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16310; decide +kernel
    rw [ha]
    exact (canonical16310 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA996 + difference 3 0) (sourceB996 + difference 0 3) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA996 + difference 3 0) (sourceB996 + difference 0 3) sourceC996) = raw10946 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw10946; decide +kernel
    rw [ha]
    exact (canonical10946 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA996 + difference 3 1) (sourceB996 + difference 1 3) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3737) := by
    have ha : (tripleCharges (sourceA996 + difference 3 1) (sourceB996 + difference 1 3) sourceC996) = raw16311 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16311; decide +kernel
    rw [ha]
    exact (canonical16311 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA996 + difference 3 2) (sourceB996 + difference 2 3) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3787) := by
    have ha : (tripleCharges (sourceA996 + difference 3 2) (sourceB996 + difference 2 3) sourceC996) = raw16312 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16312; decide +kernel
    rw [ha]
    exact (canonical16312 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA996 + difference 3 4) (sourceB996 + difference 4 3) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA996 + difference 3 4) (sourceB996 + difference 4 3) sourceC996) = raw16313 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16313; decide +kernel
    rw [ha]
    exact (canonical16313 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA996 + difference 3 5) (sourceB996 + difference 5 3) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA996 + difference 3 5) (sourceB996 + difference 5 3) sourceC996) = raw16314 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16314; decide +kernel
    rw [ha]
    exact (canonical16314 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA996 + difference 4 0) (sourceB996 + difference 0 4) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA996 + difference 4 0) (sourceB996 + difference 0 4) sourceC996) = raw10951 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw10951; decide +kernel
    rw [ha]
    exact (canonical10951 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA996 + difference 4 1) (sourceB996 + difference 1 4) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3741) := by
    have ha : (tripleCharges (sourceA996 + difference 4 1) (sourceB996 + difference 1 4) sourceC996) = raw16315 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16315; decide +kernel
    rw [ha]
    exact (canonical16315 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA996 + difference 4 2) (sourceB996 + difference 2 4) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3790) := by
    have ha : (tripleCharges (sourceA996 + difference 4 2) (sourceB996 + difference 2 4) sourceC996) = raw16316 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16316; decide +kernel
    rw [ha]
    exact (canonical16316 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA996 + difference 4 3) (sourceB996 + difference 3 4) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3790) := by
    have ha : (tripleCharges (sourceA996 + difference 4 3) (sourceB996 + difference 3 4) sourceC996) = raw16317 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16317; decide +kernel
    rw [ha]
    exact (canonical16317 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA996 + difference 4 5) (sourceB996 + difference 5 4) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA996 + difference 4 5) (sourceB996 + difference 5 4) sourceC996) = raw16318 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16318; decide +kernel
    rw [ha]
    exact (canonical16318 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA996 + difference 5 0) (sourceB996 + difference 0 5) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA996 + difference 5 0) (sourceB996 + difference 0 5) sourceC996) = raw10956 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw10956; decide +kernel
    rw [ha]
    exact (canonical10956 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA996 + difference 5 1) (sourceB996 + difference 1 5) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2604) := by
    have ha : (tripleCharges (sourceA996 + difference 5 1) (sourceB996 + difference 1 5) sourceC996) = raw16319 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16319; decide +kernel
    rw [ha]
    exact (canonical16319 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA996 + difference 5 2) (sourceB996 + difference 2 5) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA996 + difference 5 2) (sourceB996 + difference 2 5) sourceC996) = raw16320 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16320; decide +kernel
    rw [ha]
    exact (canonical16320 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA996 + difference 5 3) (sourceB996 + difference 3 5) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA996 + difference 5 3) (sourceB996 + difference 3 5) sourceC996) = raw16321 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16321; decide +kernel
    rw [ha]
    exact (canonical16321 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA996 + difference 5 4) (sourceB996 + difference 4 5) sourceC996) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA996 + difference 5 4) (sourceB996 + difference 4 5) sourceC996) = raw16322 := by
      apply Matrix.ext; unfold tripleCharges sourceA996 sourceB996 sourceC996 difference raw16322; decide +kernel
    rw [ha]
    exact (canonical16322 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA996 sourceB996 sourceC996
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm996, Integer.Sparse.eval]
  linarith only [hs]

def sourceA997 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB997 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC997 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm997 : Integer.Sparse Master := [(Sum.inr 5289, 2), (Sum.inr 5291, 1), (Sum.inr 5295, 1), (Sum.inr 5299, 2), (Sum.inr 5300, 1), (Sum.inr 5302, 1), (Sum.inr 5304, 1), (Sum.inr 5411, 2), (Sum.inr 5413, 1), (Sum.inr 5430, 2), (Sum.inr 5432, 2), (Sum.inr 5434, 2), (Sum.inr 5438, 2), (Sum.inr 5441, 1), (Sum.inr 5442, 1), (Sum.inr 5443, 1), (Sum.inr 5446, 2), (Sum.inr 5449, 1), (Sum.inr 5473, 2), (Sum.inr 5475, 1), (Sum.inr 5487, 1)]

theorem sourceEq997 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm997 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA997 + difference 0 1) (sourceB997 + difference 1 0) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA997 + difference 0 1) (sourceB997 + difference 1 0) sourceC997) = raw15115 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw15115; decide +kernel
    rw [ha]
    exact (canonical15115 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA997 + difference 0 2) (sourceB997 + difference 2 0) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA997 + difference 0 2) (sourceB997 + difference 2 0) sourceC997) = raw16142 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16142; decide +kernel
    rw [ha]
    exact (canonical16142 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA997 + difference 0 3) (sourceB997 + difference 3 0) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA997 + difference 0 3) (sourceB997 + difference 3 0) sourceC997) = raw16323 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16323; decide +kernel
    rw [ha]
    exact (canonical16323 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA997 + difference 0 4) (sourceB997 + difference 4 0) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5475) := by
    have ha : (tripleCharges (sourceA997 + difference 0 4) (sourceB997 + difference 4 0) sourceC997) = raw16324 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16324; decide +kernel
    rw [ha]
    exact (canonical16324 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA997 + difference 0 5) (sourceB997 + difference 5 0) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA997 + difference 0 5) (sourceB997 + difference 5 0) sourceC997) = raw16325 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16325; decide +kernel
    rw [ha]
    exact (canonical16325 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA997 + difference 1 0) (sourceB997 + difference 0 1) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA997 + difference 1 0) (sourceB997 + difference 0 1) sourceC997) = raw16326 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16326; decide +kernel
    rw [ha]
    exact (canonical16326 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA997 + difference 1 2) (sourceB997 + difference 2 1) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA997 + difference 1 2) (sourceB997 + difference 2 1) sourceC997) = raw16147 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16147; decide +kernel
    rw [ha]
    exact (canonical16147 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA997 + difference 1 3) (sourceB997 + difference 3 1) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA997 + difference 1 3) (sourceB997 + difference 3 1) sourceC997) = raw16327 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16327; decide +kernel
    rw [ha]
    exact (canonical16327 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA997 + difference 1 4) (sourceB997 + difference 4 1) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA997 + difference 1 4) (sourceB997 + difference 4 1) sourceC997) = raw16328 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16328; decide +kernel
    rw [ha]
    exact (canonical16328 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA997 + difference 1 5) (sourceB997 + difference 5 1) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA997 + difference 1 5) (sourceB997 + difference 5 1) sourceC997) = raw16329 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16329; decide +kernel
    rw [ha]
    exact (canonical16329 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA997 + difference 2 0) (sourceB997 + difference 0 2) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA997 + difference 2 0) (sourceB997 + difference 0 2) sourceC997) = raw16330 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16330; decide +kernel
    rw [ha]
    exact (canonical16330 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA997 + difference 2 1) (sourceB997 + difference 1 2) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA997 + difference 2 1) (sourceB997 + difference 1 2) sourceC997) = raw15125 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw15125; decide +kernel
    rw [ha]
    exact (canonical15125 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA997 + difference 2 3) (sourceB997 + difference 3 2) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA997 + difference 2 3) (sourceB997 + difference 3 2) sourceC997) = raw16331 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16331; decide +kernel
    rw [ha]
    exact (canonical16331 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA997 + difference 2 4) (sourceB997 + difference 4 2) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA997 + difference 2 4) (sourceB997 + difference 4 2) sourceC997) = raw15669 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw15669; decide +kernel
    rw [ha]
    exact (canonical15669 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA997 + difference 2 5) (sourceB997 + difference 5 2) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA997 + difference 2 5) (sourceB997 + difference 5 2) sourceC997) = raw15862 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw15862; decide +kernel
    rw [ha]
    exact (canonical15862 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA997 + difference 3 0) (sourceB997 + difference 0 3) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA997 + difference 3 0) (sourceB997 + difference 0 3) sourceC997) = raw15118 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw15118; decide +kernel
    rw [ha]
    exact (canonical15118 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA997 + difference 3 1) (sourceB997 + difference 1 3) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA997 + difference 3 1) (sourceB997 + difference 1 3) sourceC997) = raw15210 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw15210; decide +kernel
    rw [ha]
    exact (canonical15210 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA997 + difference 3 2) (sourceB997 + difference 2 3) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA997 + difference 3 2) (sourceB997 + difference 2 3) sourceC997) = raw15119 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw15119; decide +kernel
    rw [ha]
    exact (canonical15119 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA997 + difference 3 4) (sourceB997 + difference 4 3) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA997 + difference 3 4) (sourceB997 + difference 4 3) sourceC997) = raw15121 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw15121; decide +kernel
    rw [ha]
    exact (canonical15121 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA997 + difference 3 5) (sourceB997 + difference 5 3) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA997 + difference 3 5) (sourceB997 + difference 5 3) sourceC997) = raw15122 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw15122; decide +kernel
    rw [ha]
    exact (canonical15122 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA997 + difference 4 0) (sourceB997 + difference 0 4) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA997 + difference 4 0) (sourceB997 + difference 0 4) sourceC997) = raw16332 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16332; decide +kernel
    rw [ha]
    exact (canonical16332 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA997 + difference 4 1) (sourceB997 + difference 1 4) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA997 + difference 4 1) (sourceB997 + difference 1 4) sourceC997) = raw14994 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw14994; decide +kernel
    rw [ha]
    exact (canonical14994 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA997 + difference 4 2) (sourceB997 + difference 2 4) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA997 + difference 4 2) (sourceB997 + difference 2 4) sourceC997) = raw16156 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16156; decide +kernel
    rw [ha]
    exact (canonical16156 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA997 + difference 4 3) (sourceB997 + difference 3 4) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA997 + difference 4 3) (sourceB997 + difference 3 4) sourceC997) = raw16333 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16333; decide +kernel
    rw [ha]
    exact (canonical16333 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA997 + difference 4 5) (sourceB997 + difference 5 4) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA997 + difference 4 5) (sourceB997 + difference 5 4) sourceC997) = raw14979 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw14979; decide +kernel
    rw [ha]
    exact (canonical14979 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA997 + difference 5 0) (sourceB997 + difference 0 5) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA997 + difference 5 0) (sourceB997 + difference 0 5) sourceC997) = raw16334 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16334; decide +kernel
    rw [ha]
    exact (canonical16334 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA997 + difference 5 1) (sourceB997 + difference 1 5) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA997 + difference 5 1) (sourceB997 + difference 1 5) sourceC997) = raw15138 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw15138; decide +kernel
    rw [ha]
    exact (canonical15138 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA997 + difference 5 2) (sourceB997 + difference 2 5) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA997 + difference 5 2) (sourceB997 + difference 2 5) sourceC997) = raw16159 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16159; decide +kernel
    rw [ha]
    exact (canonical16159 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA997 + difference 5 3) (sourceB997 + difference 3 5) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA997 + difference 5 3) (sourceB997 + difference 3 5) sourceC997) = raw16335 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16335; decide +kernel
    rw [ha]
    exact (canonical16335 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA997 + difference 5 4) (sourceB997 + difference 4 5) sourceC997) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5449) := by
    have ha : (tripleCharges (sourceA997 + difference 5 4) (sourceB997 + difference 4 5) sourceC997) = raw16336 := by
      apply Matrix.ext; unfold tripleCharges sourceA997 sourceB997 sourceC997 difference raw16336; decide +kernel
    rw [ha]
    exact (canonical16336 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA997 sourceB997 sourceC997
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm997, Integer.Sparse.eval]
  linarith only [hs]

def sourceA998 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB998 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC998 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceForm998 : Integer.Sparse Master := [(Sum.inr 4999, 1), (Sum.inr 5001, 1), (Sum.inr 5002, 1), (Sum.inr 5005, 1), (Sum.inr 5006, 1), (Sum.inr 5010, 1), (Sum.inr 5016, 1), (Sum.inr 5020, 1), (Sum.inr 5124, 1), (Sum.inr 5164, 1), (Sum.inr 5190, 1), (Sum.inr 5199, 1), (Sum.inr 5229, 1), (Sum.inr 5260, 1), (Sum.inr 5266, 1), (Sum.inr 5282, 1), (Sum.inr 5421, 1), (Sum.inr 5429, 1), (Sum.inr 5430, 1), (Sum.inr 5438, 1), (Sum.inr 5439, 1), (Sum.inr 5444, 1), (Sum.inr 5445, 1), (Sum.inr 5446, 1), (Sum.inr 5448, 1), (Sum.inr 5450, 1), (Sum.inr 5463, 1), (Sum.inr 5470, 1), (Sum.inr 5473, 1), (Sum.inr 5484, 1)]

theorem sourceEq998 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm998 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA998 + difference 0 1) (sourceB998 + difference 1 0) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA998 + difference 0 1) (sourceB998 + difference 1 0) sourceC998) = raw16337 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16337; decide +kernel
    rw [ha]
    exact (canonical16337 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA998 + difference 0 2) (sourceB998 + difference 2 0) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA998 + difference 0 2) (sourceB998 + difference 2 0) sourceC998) = raw16338 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16338; decide +kernel
    rw [ha]
    exact (canonical16338 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA998 + difference 0 3) (sourceB998 + difference 3 0) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5463) := by
    have ha : (tripleCharges (sourceA998 + difference 0 3) (sourceB998 + difference 3 0) sourceC998) = raw16339 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16339; decide +kernel
    rw [ha]
    exact (canonical16339 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA998 + difference 0 4) (sourceB998 + difference 4 0) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA998 + difference 0 4) (sourceB998 + difference 4 0) sourceC998) = raw16340 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16340; decide +kernel
    rw [ha]
    exact (canonical16340 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA998 + difference 0 5) (sourceB998 + difference 5 0) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA998 + difference 0 5) (sourceB998 + difference 5 0) sourceC998) = raw16341 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16341; decide +kernel
    rw [ha]
    exact (canonical16341 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA998 + difference 1 0) (sourceB998 + difference 0 1) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA998 + difference 1 0) (sourceB998 + difference 0 1) sourceC998) = raw16342 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16342; decide +kernel
    rw [ha]
    exact (canonical16342 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA998 + difference 1 2) (sourceB998 + difference 2 1) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA998 + difference 1 2) (sourceB998 + difference 2 1) sourceC998) = raw16343 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16343; decide +kernel
    rw [ha]
    exact (canonical16343 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA998 + difference 1 3) (sourceB998 + difference 3 1) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA998 + difference 1 3) (sourceB998 + difference 3 1) sourceC998) = raw16344 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16344; decide +kernel
    rw [ha]
    exact (canonical16344 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA998 + difference 1 4) (sourceB998 + difference 4 1) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA998 + difference 1 4) (sourceB998 + difference 4 1) sourceC998) = raw16345 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16345; decide +kernel
    rw [ha]
    exact (canonical16345 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA998 + difference 1 5) (sourceB998 + difference 5 1) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA998 + difference 1 5) (sourceB998 + difference 5 1) sourceC998) = raw16346 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16346; decide +kernel
    rw [ha]
    exact (canonical16346 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA998 + difference 2 0) (sourceB998 + difference 0 2) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5190) := by
    have ha : (tripleCharges (sourceA998 + difference 2 0) (sourceB998 + difference 0 2) sourceC998) = raw16347 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16347; decide +kernel
    rw [ha]
    exact (canonical16347 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA998 + difference 2 1) (sourceB998 + difference 1 2) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5124) := by
    have ha : (tripleCharges (sourceA998 + difference 2 1) (sourceB998 + difference 1 2) sourceC998) = raw16348 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16348; decide +kernel
    rw [ha]
    exact (canonical16348 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA998 + difference 2 3) (sourceB998 + difference 3 2) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5444) := by
    have ha : (tripleCharges (sourceA998 + difference 2 3) (sourceB998 + difference 3 2) sourceC998) = raw16349 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16349; decide +kernel
    rw [ha]
    exact (canonical16349 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA998 + difference 2 4) (sourceB998 + difference 4 2) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA998 + difference 2 4) (sourceB998 + difference 4 2) sourceC998) = raw16350 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16350; decide +kernel
    rw [ha]
    exact (canonical16350 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA998 + difference 2 5) (sourceB998 + difference 5 2) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA998 + difference 2 5) (sourceB998 + difference 5 2) sourceC998) = raw16351 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16351; decide +kernel
    rw [ha]
    exact (canonical16351 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA998 + difference 3 0) (sourceB998 + difference 0 3) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA998 + difference 3 0) (sourceB998 + difference 0 3) sourceC998) = raw16352 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16352; decide +kernel
    rw [ha]
    exact (canonical16352 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA998 + difference 3 1) (sourceB998 + difference 1 3) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA998 + difference 3 1) (sourceB998 + difference 1 3) sourceC998) = raw16353 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16353; decide +kernel
    rw [ha]
    exact (canonical16353 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA998 + difference 3 2) (sourceB998 + difference 2 3) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA998 + difference 3 2) (sourceB998 + difference 2 3) sourceC998) = raw16354 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16354; decide +kernel
    rw [ha]
    exact (canonical16354 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA998 + difference 3 4) (sourceB998 + difference 4 3) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA998 + difference 3 4) (sourceB998 + difference 4 3) sourceC998) = raw16355 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16355; decide +kernel
    rw [ha]
    exact (canonical16355 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA998 + difference 3 5) (sourceB998 + difference 5 3) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA998 + difference 3 5) (sourceB998 + difference 5 3) sourceC998) = raw16356 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16356; decide +kernel
    rw [ha]
    exact (canonical16356 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA998 + difference 4 0) (sourceB998 + difference 0 4) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5016) := by
    have ha : (tripleCharges (sourceA998 + difference 4 0) (sourceB998 + difference 0 4) sourceC998) = raw16357 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16357; decide +kernel
    rw [ha]
    exact (canonical16357 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA998 + difference 4 1) (sourceB998 + difference 1 4) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5006) := by
    have ha : (tripleCharges (sourceA998 + difference 4 1) (sourceB998 + difference 1 4) sourceC998) = raw16358 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16358; decide +kernel
    rw [ha]
    exact (canonical16358 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA998 + difference 4 2) (sourceB998 + difference 2 4) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5005) := by
    have ha : (tripleCharges (sourceA998 + difference 4 2) (sourceB998 + difference 2 4) sourceC998) = raw16359 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16359; decide +kernel
    rw [ha]
    exact (canonical16359 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA998 + difference 4 3) (sourceB998 + difference 3 4) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5010) := by
    have ha : (tripleCharges (sourceA998 + difference 4 3) (sourceB998 + difference 3 4) sourceC998) = raw16360 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16360; decide +kernel
    rw [ha]
    exact (canonical16360 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA998 + difference 4 5) (sourceB998 + difference 5 4) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA998 + difference 4 5) (sourceB998 + difference 5 4) sourceC998) = raw16361 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16361; decide +kernel
    rw [ha]
    exact (canonical16361 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA998 + difference 5 0) (sourceB998 + difference 0 5) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5001) := by
    have ha : (tripleCharges (sourceA998 + difference 5 0) (sourceB998 + difference 0 5) sourceC998) = raw16362 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16362; decide +kernel
    rw [ha]
    exact (canonical16362 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA998 + difference 5 1) (sourceB998 + difference 1 5) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5002) := by
    have ha : (tripleCharges (sourceA998 + difference 5 1) (sourceB998 + difference 1 5) sourceC998) = raw16363 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16363; decide +kernel
    rw [ha]
    exact (canonical16363 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA998 + difference 5 2) (sourceB998 + difference 2 5) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4999) := by
    have ha : (tripleCharges (sourceA998 + difference 5 2) (sourceB998 + difference 2 5) sourceC998) = raw16364 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16364; decide +kernel
    rw [ha]
    exact (canonical16364 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA998 + difference 5 3) (sourceB998 + difference 3 5) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5020) := by
    have ha : (tripleCharges (sourceA998 + difference 5 3) (sourceB998 + difference 3 5) sourceC998) = raw16365 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16365; decide +kernel
    rw [ha]
    exact (canonical16365 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA998 + difference 5 4) (sourceB998 + difference 4 5) sourceC998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA998 + difference 5 4) (sourceB998 + difference 4 5) sourceC998) = raw16366 := by
      apply Matrix.ext; unfold tripleCharges sourceA998 sourceB998 sourceC998 difference raw16366; decide +kernel
    rw [ha]
    exact (canonical16366 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA998 sourceB998 sourceC998
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm998, Integer.Sparse.eval]
  linarith only [hs]

def sourceA999 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB999 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC999 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceForm999 : Integer.Sparse Master := [(Sum.inr 2384, 1), (Sum.inr 2386, 1), (Sum.inr 2387, 1), (Sum.inr 2406, 1), (Sum.inr 2724, 1), (Sum.inr 2854, 1), (Sum.inr 2855, 1), (Sum.inr 2882, 1), (Sum.inr 3078, 1), (Sum.inr 3342, 1), (Sum.inr 3343, 1), (Sum.inr 3359, 1), (Sum.inr 3371, 1), (Sum.inr 3392, 1), (Sum.inr 3535, 1), (Sum.inr 3565, 1), (Sum.inr 3943, 1), (Sum.inr 3946, 1), (Sum.inr 3954, 1), (Sum.inr 3955, 1), (Sum.inr 3959, 1), (Sum.inr 3960, 1), (Sum.inr 3961, 1), (Sum.inr 3972, 1), (Sum.inr 3983, 1), (Sum.inr 3993, 1), (Sum.inr 4012, 1), (Sum.inr 4024, 1), (Sum.inr 4028, 1), (Sum.inr 4029, 1)]

theorem sourceEq999 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm999 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA999 + difference 0 1) (sourceB999 + difference 1 0) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA999 + difference 0 1) (sourceB999 + difference 1 0) sourceC999) = raw16367 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16367; decide +kernel
    rw [ha]
    exact (canonical16367 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA999 + difference 0 2) (sourceB999 + difference 2 0) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3955) := by
    have ha : (tripleCharges (sourceA999 + difference 0 2) (sourceB999 + difference 2 0) sourceC999) = raw16368 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16368; decide +kernel
    rw [ha]
    exact (canonical16368 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA999 + difference 0 3) (sourceB999 + difference 3 0) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3960) := by
    have ha : (tripleCharges (sourceA999 + difference 0 3) (sourceB999 + difference 3 0) sourceC999) = raw16369 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16369; decide +kernel
    rw [ha]
    exact (canonical16369 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA999 + difference 0 4) (sourceB999 + difference 4 0) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA999 + difference 0 4) (sourceB999 + difference 4 0) sourceC999) = raw16370 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16370; decide +kernel
    rw [ha]
    exact (canonical16370 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA999 + difference 0 5) (sourceB999 + difference 5 0) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA999 + difference 0 5) (sourceB999 + difference 5 0) sourceC999) = raw16371 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16371; decide +kernel
    rw [ha]
    exact (canonical16371 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA999 + difference 1 0) (sourceB999 + difference 0 1) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA999 + difference 1 0) (sourceB999 + difference 0 1) sourceC999) = raw16372 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16372; decide +kernel
    rw [ha]
    exact (canonical16372 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA999 + difference 1 2) (sourceB999 + difference 2 1) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA999 + difference 1 2) (sourceB999 + difference 2 1) sourceC999) = raw16373 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16373; decide +kernel
    rw [ha]
    exact (canonical16373 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA999 + difference 1 3) (sourceB999 + difference 3 1) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA999 + difference 1 3) (sourceB999 + difference 3 1) sourceC999) = raw16374 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16374; decide +kernel
    rw [ha]
    exact (canonical16374 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA999 + difference 1 4) (sourceB999 + difference 4 1) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA999 + difference 1 4) (sourceB999 + difference 4 1) sourceC999) = raw16375 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16375; decide +kernel
    rw [ha]
    exact (canonical16375 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA999 + difference 1 5) (sourceB999 + difference 5 1) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA999 + difference 1 5) (sourceB999 + difference 5 1) sourceC999) = raw16376 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16376; decide +kernel
    rw [ha]
    exact (canonical16376 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA999 + difference 2 0) (sourceB999 + difference 0 2) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2854) := by
    have ha : (tripleCharges (sourceA999 + difference 2 0) (sourceB999 + difference 0 2) sourceC999) = raw16377 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16377; decide +kernel
    rw [ha]
    exact (canonical16377 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA999 + difference 2 1) (sourceB999 + difference 1 2) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3371) := by
    have ha : (tripleCharges (sourceA999 + difference 2 1) (sourceB999 + difference 1 2) sourceC999) = raw16378 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16378; decide +kernel
    rw [ha]
    exact (canonical16378 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA999 + difference 2 3) (sourceB999 + difference 3 2) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3943) := by
    have ha : (tripleCharges (sourceA999 + difference 2 3) (sourceB999 + difference 3 2) sourceC999) = raw16379 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16379; decide +kernel
    rw [ha]
    exact (canonical16379 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA999 + difference 2 4) (sourceB999 + difference 4 2) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA999 + difference 2 4) (sourceB999 + difference 4 2) sourceC999) = raw16380 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16380; decide +kernel
    rw [ha]
    exact (canonical16380 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA999 + difference 2 5) (sourceB999 + difference 5 2) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA999 + difference 2 5) (sourceB999 + difference 5 2) sourceC999) = raw16381 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16381; decide +kernel
    rw [ha]
    exact (canonical16381 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA999 + difference 3 0) (sourceB999 + difference 0 3) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA999 + difference 3 0) (sourceB999 + difference 0 3) sourceC999) = raw16382 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16382; decide +kernel
    rw [ha]
    exact (canonical16382 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA999 + difference 3 1) (sourceB999 + difference 1 3) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA999 + difference 3 1) (sourceB999 + difference 1 3) sourceC999) = raw16383 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16383; decide +kernel
    rw [ha]
    exact (canonical16383 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA999 + difference 3 2) (sourceB999 + difference 2 3) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA999 + difference 3 2) (sourceB999 + difference 2 3) sourceC999) = raw16384 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16384; decide +kernel
    rw [ha]
    exact (canonical16384 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA999 + difference 3 4) (sourceB999 + difference 4 3) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA999 + difference 3 4) (sourceB999 + difference 4 3) sourceC999) = raw16385 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16385; decide +kernel
    rw [ha]
    exact (canonical16385 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA999 + difference 3 5) (sourceB999 + difference 5 3) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4028) := by
    have ha : (tripleCharges (sourceA999 + difference 3 5) (sourceB999 + difference 5 3) sourceC999) = raw16386 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16386; decide +kernel
    rw [ha]
    exact (canonical16386 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA999 + difference 4 0) (sourceB999 + difference 0 4) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2855) := by
    have ha : (tripleCharges (sourceA999 + difference 4 0) (sourceB999 + difference 0 4) sourceC999) = raw16387 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16387; decide +kernel
    rw [ha]
    exact (canonical16387 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA999 + difference 4 1) (sourceB999 + difference 1 4) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3343) := by
    have ha : (tripleCharges (sourceA999 + difference 4 1) (sourceB999 + difference 1 4) sourceC999) = raw16388 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16388; decide +kernel
    rw [ha]
    exact (canonical16388 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA999 + difference 4 2) (sourceB999 + difference 2 4) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3342) := by
    have ha : (tripleCharges (sourceA999 + difference 4 2) (sourceB999 + difference 2 4) sourceC999) = raw16389 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16389; decide +kernel
    rw [ha]
    exact (canonical16389 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA999 + difference 4 3) (sourceB999 + difference 3 4) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3359) := by
    have ha : (tripleCharges (sourceA999 + difference 4 3) (sourceB999 + difference 3 4) sourceC999) = raw16390 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16390; decide +kernel
    rw [ha]
    exact (canonical16390 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA999 + difference 4 5) (sourceB999 + difference 5 4) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA999 + difference 4 5) (sourceB999 + difference 5 4) sourceC999) = raw16391 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16391; decide +kernel
    rw [ha]
    exact (canonical16391 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA999 + difference 5 0) (sourceB999 + difference 0 5) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2386) := by
    have ha : (tripleCharges (sourceA999 + difference 5 0) (sourceB999 + difference 0 5) sourceC999) = raw16392 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16392; decide +kernel
    rw [ha]
    exact (canonical16392 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA999 + difference 5 1) (sourceB999 + difference 1 5) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2387) := by
    have ha : (tripleCharges (sourceA999 + difference 5 1) (sourceB999 + difference 1 5) sourceC999) = raw16393 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16393; decide +kernel
    rw [ha]
    exact (canonical16393 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA999 + difference 5 2) (sourceB999 + difference 2 5) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2384) := by
    have ha : (tripleCharges (sourceA999 + difference 5 2) (sourceB999 + difference 2 5) sourceC999) = raw16394 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16394; decide +kernel
    rw [ha]
    exact (canonical16394 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA999 + difference 5 3) (sourceB999 + difference 3 5) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2406) := by
    have ha : (tripleCharges (sourceA999 + difference 5 3) (sourceB999 + difference 3 5) sourceC999) = raw16395 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16395; decide +kernel
    rw [ha]
    exact (canonical16395 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA999 + difference 5 4) (sourceB999 + difference 4 5) sourceC999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA999 + difference 5 4) (sourceB999 + difference 4 5) sourceC999) = raw16396 := by
      apply Matrix.ext; unfold tripleCharges sourceA999 sourceB999 sourceC999 difference raw16396; decide +kernel
    rw [ha]
    exact (canonical16396 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA999 sourceB999 sourceC999
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm999, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1000 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1000 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC1000 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceForm1000 : Integer.Sparse Master := [(Sum.inr 2390, 1), (Sum.inr 2391, 1), (Sum.inr 2395, 1), (Sum.inr 2401, 1), (Sum.inr 2537, 1), (Sum.inr 2538, 1), (Sum.inr 2591, 1), (Sum.inr 2673, 1), (Sum.inr 2731, 1), (Sum.inr 3346, 1), (Sum.inr 3349, 1), (Sum.inr 3355, 1), (Sum.inr 3540, 1), (Sum.inr 3568, 1), (Sum.inr 3578, 1), (Sum.inr 3580, 1), (Sum.inr 3848, 1), (Sum.inr 3857, 1), (Sum.inr 3858, 1), (Sum.inr 3873, 1), (Sum.inr 3874, 1), (Sum.inr 3879, 1), (Sum.inr 3880, 1), (Sum.inr 3884, 1), (Sum.inr 3885, 1), (Sum.inr 3887, 1), (Sum.inr 3929, 1), (Sum.inr 3947, 1), (Sum.inr 3995, 1), (Sum.inr 3997, 1)]

theorem sourceEq1000 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1000 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1000 + difference 0 1) (sourceB1000 + difference 1 0) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA1000 + difference 0 1) (sourceB1000 + difference 1 0) sourceC1000) = raw16397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16397; decide +kernel
    rw [ha]
    exact (canonical16397 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1000 + difference 0 2) (sourceB1000 + difference 2 0) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3947) := by
    have ha : (tripleCharges (sourceA1000 + difference 0 2) (sourceB1000 + difference 2 0) sourceC1000) = raw16398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16398; decide +kernel
    rw [ha]
    exact (canonical16398 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1000 + difference 0 3) (sourceB1000 + difference 3 0) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3929) := by
    have ha : (tripleCharges (sourceA1000 + difference 0 3) (sourceB1000 + difference 3 0) sourceC1000) = raw16399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16399; decide +kernel
    rw [ha]
    exact (canonical16399 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1000 + difference 0 4) (sourceB1000 + difference 4 0) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3997) := by
    have ha : (tripleCharges (sourceA1000 + difference 0 4) (sourceB1000 + difference 4 0) sourceC1000) = raw16400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16400; decide +kernel
    rw [ha]
    exact (canonical16400 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1000 + difference 0 5) (sourceB1000 + difference 5 0) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA1000 + difference 0 5) (sourceB1000 + difference 5 0) sourceC1000) = raw16401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16401; decide +kernel
    rw [ha]
    exact (canonical16401 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1000 + difference 1 0) (sourceB1000 + difference 0 1) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA1000 + difference 1 0) (sourceB1000 + difference 0 1) sourceC1000) = raw16402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16402; decide +kernel
    rw [ha]
    exact (canonical16402 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1000 + difference 1 2) (sourceB1000 + difference 2 1) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA1000 + difference 1 2) (sourceB1000 + difference 2 1) sourceC1000) = raw16403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16403; decide +kernel
    rw [ha]
    exact (canonical16403 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1000 + difference 1 3) (sourceB1000 + difference 3 1) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA1000 + difference 1 3) (sourceB1000 + difference 3 1) sourceC1000) = raw16404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16404; decide +kernel
    rw [ha]
    exact (canonical16404 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1000 + difference 1 4) (sourceB1000 + difference 4 1) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA1000 + difference 1 4) (sourceB1000 + difference 4 1) sourceC1000) = raw16405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16405; decide +kernel
    rw [ha]
    exact (canonical16405 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1000 + difference 1 5) (sourceB1000 + difference 5 1) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA1000 + difference 1 5) (sourceB1000 + difference 5 1) sourceC1000) = raw16406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16406; decide +kernel
    rw [ha]
    exact (canonical16406 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1000 + difference 2 0) (sourceB1000 + difference 0 2) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3568) := by
    have ha : (tripleCharges (sourceA1000 + difference 2 0) (sourceB1000 + difference 0 2) sourceC1000) = raw16407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16407; decide +kernel
    rw [ha]
    exact (canonical16407 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1000 + difference 2 1) (sourceB1000 + difference 1 2) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2537) := by
    have ha : (tripleCharges (sourceA1000 + difference 2 1) (sourceB1000 + difference 1 2) sourceC1000) = raw16408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16408; decide +kernel
    rw [ha]
    exact (canonical16408 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1000 + difference 2 3) (sourceB1000 + difference 3 2) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3879) := by
    have ha : (tripleCharges (sourceA1000 + difference 2 3) (sourceB1000 + difference 3 2) sourceC1000) = raw16409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16409; decide +kernel
    rw [ha]
    exact (canonical16409 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1000 + difference 2 4) (sourceB1000 + difference 4 2) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA1000 + difference 2 4) (sourceB1000 + difference 4 2) sourceC1000) = raw16410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16410; decide +kernel
    rw [ha]
    exact (canonical16410 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1000 + difference 2 5) (sourceB1000 + difference 5 2) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1000 + difference 2 5) (sourceB1000 + difference 5 2) sourceC1000) = raw16411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16411; decide +kernel
    rw [ha]
    exact (canonical16411 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1000 + difference 3 0) (sourceB1000 + difference 0 3) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA1000 + difference 3 0) (sourceB1000 + difference 0 3) sourceC1000) = raw16412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16412; decide +kernel
    rw [ha]
    exact (canonical16412 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1000 + difference 3 1) (sourceB1000 + difference 1 3) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA1000 + difference 3 1) (sourceB1000 + difference 1 3) sourceC1000) = raw16413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16413; decide +kernel
    rw [ha]
    exact (canonical16413 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1000 + difference 3 2) (sourceB1000 + difference 2 3) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA1000 + difference 3 2) (sourceB1000 + difference 2 3) sourceC1000) = raw16414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16414; decide +kernel
    rw [ha]
    exact (canonical16414 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1000 + difference 3 4) (sourceB1000 + difference 4 3) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA1000 + difference 3 4) (sourceB1000 + difference 4 3) sourceC1000) = raw16415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16415; decide +kernel
    rw [ha]
    exact (canonical16415 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1000 + difference 3 5) (sourceB1000 + difference 5 3) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA1000 + difference 3 5) (sourceB1000 + difference 5 3) sourceC1000) = raw16416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16416; decide +kernel
    rw [ha]
    exact (canonical16416 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1000 + difference 4 0) (sourceB1000 + difference 0 4) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2401) := by
    have ha : (tripleCharges (sourceA1000 + difference 4 0) (sourceB1000 + difference 0 4) sourceC1000) = raw16417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16417; decide +kernel
    rw [ha]
    exact (canonical16417 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1000 + difference 4 1) (sourceB1000 + difference 1 4) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2391) := by
    have ha : (tripleCharges (sourceA1000 + difference 4 1) (sourceB1000 + difference 1 4) sourceC1000) = raw16418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16418; decide +kernel
    rw [ha]
    exact (canonical16418 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1000 + difference 4 2) (sourceB1000 + difference 2 4) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2390) := by
    have ha : (tripleCharges (sourceA1000 + difference 4 2) (sourceB1000 + difference 2 4) sourceC1000) = raw16419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16419; decide +kernel
    rw [ha]
    exact (canonical16419 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1000 + difference 4 3) (sourceB1000 + difference 3 4) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2395) := by
    have ha : (tripleCharges (sourceA1000 + difference 4 3) (sourceB1000 + difference 3 4) sourceC1000) = raw16420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16420; decide +kernel
    rw [ha]
    exact (canonical16420 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1000 + difference 4 5) (sourceB1000 + difference 5 4) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA1000 + difference 4 5) (sourceB1000 + difference 5 4) sourceC1000) = raw16421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16421; decide +kernel
    rw [ha]
    exact (canonical16421 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1000 + difference 5 0) (sourceB1000 + difference 0 5) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3355) := by
    have ha : (tripleCharges (sourceA1000 + difference 5 0) (sourceB1000 + difference 0 5) sourceC1000) = raw16422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16422; decide +kernel
    rw [ha]
    exact (canonical16422 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1000 + difference 5 1) (sourceB1000 + difference 1 5) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2538) := by
    have ha : (tripleCharges (sourceA1000 + difference 5 1) (sourceB1000 + difference 1 5) sourceC1000) = raw16423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16423; decide +kernel
    rw [ha]
    exact (canonical16423 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1000 + difference 5 2) (sourceB1000 + difference 2 5) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3346) := by
    have ha : (tripleCharges (sourceA1000 + difference 5 2) (sourceB1000 + difference 2 5) sourceC1000) = raw16424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16424; decide +kernel
    rw [ha]
    exact (canonical16424 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1000 + difference 5 3) (sourceB1000 + difference 3 5) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3349) := by
    have ha : (tripleCharges (sourceA1000 + difference 5 3) (sourceB1000 + difference 3 5) sourceC1000) = raw16425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16425; decide +kernel
    rw [ha]
    exact (canonical16425 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1000 + difference 5 4) (sourceB1000 + difference 4 5) sourceC1000) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA1000 + difference 5 4) (sourceB1000 + difference 4 5) sourceC1000) = raw16426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1000 sourceB1000 sourceC1000 difference raw16426; decide +kernel
    rw [ha]
    exact (canonical16426 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1000 sourceB1000 sourceC1000
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1000, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1001 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1001 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC1001 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceForm1001 : Integer.Sparse Master := [(Sum.inr 2955, 1), (Sum.inr 3881, 1), (Sum.inr 3929, 1), (Sum.inr 3947, 1), (Sum.inr 3958, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

theorem sourceEq1001 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1001 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1001 + difference 0 0) (sourceB1001 + difference 0 0) sourceC1001) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1001 + difference 0 0) (sourceB1001 + difference 0 0) sourceC1001) = raw16427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1001 sourceB1001 sourceC1001 difference raw16427; decide +kernel
    rw [ha]
    exact (canonical16427 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1001 + difference 0 1) (sourceB1001 + difference 1 0) sourceC1001) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA1001 + difference 0 1) (sourceB1001 + difference 1 0) sourceC1001) = raw16428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1001 sourceB1001 sourceC1001 difference raw16428; decide +kernel
    rw [ha]
    exact (canonical16428 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1001 + difference 0 2) (sourceB1001 + difference 2 0) sourceC1001) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3947) := by
    have ha : (tripleCharges (sourceA1001 + difference 0 2) (sourceB1001 + difference 2 0) sourceC1001) = raw16429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1001 sourceB1001 sourceC1001 difference raw16429; decide +kernel
    rw [ha]
    exact (canonical16429 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1001 + difference 0 3) (sourceB1001 + difference 3 0) sourceC1001) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3929) := by
    have ha : (tripleCharges (sourceA1001 + difference 0 3) (sourceB1001 + difference 3 0) sourceC1001) = raw16430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1001 sourceB1001 sourceC1001 difference raw16430; decide +kernel
    rw [ha]
    exact (canonical16430 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1001 + difference 0 4) (sourceB1001 + difference 4 0) sourceC1001) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA1001 + difference 0 4) (sourceB1001 + difference 4 0) sourceC1001) = raw16431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1001 sourceB1001 sourceC1001 difference raw16431; decide +kernel
    rw [ha]
    exact (canonical16431 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1001 + difference 0 5) (sourceB1001 + difference 5 0) sourceC1001) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1001 + difference 0 5) (sourceB1001 + difference 5 0) sourceC1001) = raw16432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1001 sourceB1001 sourceC1001 difference raw16432; decide +kernel
    rw [ha]
    exact (canonical16432 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1001 + sourceB1001) sourceC1001) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1001 + sourceB1001) sourceC1001) = raw16433 := by
      apply Matrix.ext; unfold doubleCharges sourceA1001 sourceB1001 sourceC1001 raw16433; decide +kernel
    rw [ha]
    exact (canonical16433 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1001 sourceB1001 sourceC1001
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1001, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1002 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1002 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC1002 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceForm1002 : Integer.Sparse Master := [(Sum.inr 2944, 1), (Sum.inr 2946, 1), (Sum.inr 2949, 1), (Sum.inr 2955, 1), (Sum.inr 3092, 1), (Sum.inr 3881, 1), (Sum.inr 4091, -1)]

theorem sourceEq1002 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1002 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1002 + difference 0 1) (sourceB1002 + difference 1 0) sourceC1002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA1002 + difference 0 1) (sourceB1002 + difference 1 0) sourceC1002) = raw16428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1002 sourceB1002 sourceC1002 difference raw16428; decide +kernel
    rw [ha]
    exact (canonical16428 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1002 + difference 1 1) (sourceB1002 + difference 1 1) sourceC1002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1002 + difference 1 1) (sourceB1002 + difference 1 1) sourceC1002) = raw16427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1002 sourceB1002 sourceC1002 difference raw16427; decide +kernel
    rw [ha]
    exact (canonical16427 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1002 + difference 2 1) (sourceB1002 + difference 1 2) sourceC1002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2944) := by
    have ha : (tripleCharges (sourceA1002 + difference 2 1) (sourceB1002 + difference 1 2) sourceC1002) = raw16434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1002 sourceB1002 sourceC1002 difference raw16434; decide +kernel
    rw [ha]
    exact (canonical16434 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1002 + difference 3 1) (sourceB1002 + difference 1 3) sourceC1002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA1002 + difference 3 1) (sourceB1002 + difference 1 3) sourceC1002) = raw16435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1002 sourceB1002 sourceC1002 difference raw16435; decide +kernel
    rw [ha]
    exact (canonical16435 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1002 + difference 4 1) (sourceB1002 + difference 1 4) sourceC1002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2946) := by
    have ha : (tripleCharges (sourceA1002 + difference 4 1) (sourceB1002 + difference 1 4) sourceC1002) = raw16436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1002 sourceB1002 sourceC1002 difference raw16436; decide +kernel
    rw [ha]
    exact (canonical16436 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1002 + difference 5 1) (sourceB1002 + difference 1 5) sourceC1002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2949) := by
    have ha : (tripleCharges (sourceA1002 + difference 5 1) (sourceB1002 + difference 1 5) sourceC1002) = raw16437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1002 sourceB1002 sourceC1002 difference raw16437; decide +kernel
    rw [ha]
    exact (canonical16437 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1002 + sourceB1002) sourceC1002) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1002 + sourceB1002) sourceC1002) = raw16433 := by
      apply Matrix.ext; unfold doubleCharges sourceA1002 sourceB1002 sourceC1002 raw16433; decide +kernel
    rw [ha]
    exact (canonical16433 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1002 sourceB1002 sourceC1002
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1002, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1003 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1003 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC1003 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceForm1003 : Integer.Sparse Master := [(Sum.inr 2633, 1), (Sum.inr 3092, 1), (Sum.inr 3827, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

theorem sourceEq1003 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1003 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1003 + difference 3 0) (sourceB1003 + difference 0 3) sourceC1003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA1003 + difference 3 0) (sourceB1003 + difference 0 3) sourceC1003) = raw16438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1003 sourceB1003 sourceC1003 difference raw16438; decide +kernel
    rw [ha]
    exact (canonical16438 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1003 + difference 3 1) (sourceB1003 + difference 1 3) sourceC1003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA1003 + difference 3 1) (sourceB1003 + difference 1 3) sourceC1003) = raw16435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1003 sourceB1003 sourceC1003 difference raw16435; decide +kernel
    rw [ha]
    exact (canonical16435 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1003 + difference 3 2) (sourceB1003 + difference 2 3) sourceC1003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3827) := by
    have ha : (tripleCharges (sourceA1003 + difference 3 2) (sourceB1003 + difference 2 3) sourceC1003) = raw16439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1003 sourceB1003 sourceC1003 difference raw16439; decide +kernel
    rw [ha]
    exact (canonical16439 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1003 + difference 3 3) (sourceB1003 + difference 3 3) sourceC1003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1003 + difference 3 3) (sourceB1003 + difference 3 3) sourceC1003) = raw16427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1003 sourceB1003 sourceC1003 difference raw16427; decide +kernel
    rw [ha]
    exact (canonical16427 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1003 + difference 3 4) (sourceB1003 + difference 4 3) sourceC1003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1003 + difference 3 4) (sourceB1003 + difference 4 3) sourceC1003) = raw16440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1003 sourceB1003 sourceC1003 difference raw16440; decide +kernel
    rw [ha]
    exact (canonical16440 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1003 + difference 3 5) (sourceB1003 + difference 5 3) sourceC1003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA1003 + difference 3 5) (sourceB1003 + difference 5 3) sourceC1003) = raw16441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1003 sourceB1003 sourceC1003 difference raw16441; decide +kernel
    rw [ha]
    exact (canonical16441 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1003 + sourceB1003) sourceC1003) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1003 + sourceB1003) sourceC1003) = raw16433 := by
      apply Matrix.ext; unfold doubleCharges sourceA1003 sourceB1003 sourceC1003 raw16433; decide +kernel
    rw [ha]
    exact (canonical16433 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1003 sourceB1003 sourceC1003
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1003, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1004 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1004 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1004 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm1004 : Integer.Sparse Master := [(Sum.inr 4849, 1), (Sum.inr 4850, 1), (Sum.inr 4856, 1), (Sum.inr 4861, 1), (Sum.inr 4867, 1), (Sum.inr 5183, 1), (Sum.inr 5188, 1), (Sum.inr 5198, 1), (Sum.inr 5264, 1), (Sum.inr 5353, 1), (Sum.inr 5355, 1), (Sum.inr 5370, 1), (Sum.inr 5379, 1), (Sum.inr 5382, 1), (Sum.inr 5384, 1), (Sum.inr 5385, 2), (Sum.inr 5399, 1), (Sum.inr 5402, 1), (Sum.inr 5411, 2), (Sum.inr 5421, 1), (Sum.inr 5428, 1), (Sum.inr 5436, 1), (Sum.inr 5438, 1), (Sum.inr 5445, 1), (Sum.inr 5446, 1), (Sum.inr 5471, 1), (Sum.inr 5473, 1), (Sum.inr 5483, 1)]

theorem sourceEq1004 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1004 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1004 + difference 0 1) (sourceB1004 + difference 1 0) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1004 + difference 0 1) (sourceB1004 + difference 1 0) sourceC1004) = raw16442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16442; decide +kernel
    rw [ha]
    exact (canonical16442 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1004 + difference 0 2) (sourceB1004 + difference 2 0) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1004 + difference 0 2) (sourceB1004 + difference 2 0) sourceC1004) = raw16443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16443; decide +kernel
    rw [ha]
    exact (canonical16443 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1004 + difference 0 3) (sourceB1004 + difference 3 0) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1004 + difference 0 3) (sourceB1004 + difference 3 0) sourceC1004) = raw16444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16444; decide +kernel
    rw [ha]
    exact (canonical16444 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1004 + difference 0 4) (sourceB1004 + difference 4 0) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1004 + difference 0 4) (sourceB1004 + difference 4 0) sourceC1004) = raw16445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16445; decide +kernel
    rw [ha]
    exact (canonical16445 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1004 + difference 0 5) (sourceB1004 + difference 5 0) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1004 + difference 0 5) (sourceB1004 + difference 5 0) sourceC1004) = raw16446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16446; decide +kernel
    rw [ha]
    exact (canonical16446 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1004 + difference 1 0) (sourceB1004 + difference 0 1) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA1004 + difference 1 0) (sourceB1004 + difference 0 1) sourceC1004) = raw16447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16447; decide +kernel
    rw [ha]
    exact (canonical16447 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1004 + difference 1 2) (sourceB1004 + difference 2 1) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5402) := by
    have ha : (tripleCharges (sourceA1004 + difference 1 2) (sourceB1004 + difference 2 1) sourceC1004) = raw16448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16448; decide +kernel
    rw [ha]
    exact (canonical16448 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1004 + difference 1 3) (sourceB1004 + difference 3 1) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA1004 + difference 1 3) (sourceB1004 + difference 3 1) sourceC1004) = raw16449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16449; decide +kernel
    rw [ha]
    exact (canonical16449 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1004 + difference 1 4) (sourceB1004 + difference 4 1) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1004 + difference 1 4) (sourceB1004 + difference 4 1) sourceC1004) = raw16450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16450; decide +kernel
    rw [ha]
    exact (canonical16450 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1004 + difference 1 5) (sourceB1004 + difference 5 1) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1004 + difference 1 5) (sourceB1004 + difference 5 1) sourceC1004) = raw16451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16451; decide +kernel
    rw [ha]
    exact (canonical16451 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1004 + difference 2 0) (sourceB1004 + difference 0 2) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4849) := by
    have ha : (tripleCharges (sourceA1004 + difference 2 0) (sourceB1004 + difference 0 2) sourceC1004) = raw16452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16452; decide +kernel
    rw [ha]
    exact (canonical16452 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1004 + difference 2 1) (sourceB1004 + difference 1 2) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA1004 + difference 2 1) (sourceB1004 + difference 1 2) sourceC1004) = raw16453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16453; decide +kernel
    rw [ha]
    exact (canonical16453 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1004 + difference 2 3) (sourceB1004 + difference 3 2) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1004 + difference 2 3) (sourceB1004 + difference 3 2) sourceC1004) = raw16454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16454; decide +kernel
    rw [ha]
    exact (canonical16454 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1004 + difference 2 4) (sourceB1004 + difference 4 2) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5382) := by
    have ha : (tripleCharges (sourceA1004 + difference 2 4) (sourceB1004 + difference 4 2) sourceC1004) = raw16455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16455; decide +kernel
    rw [ha]
    exact (canonical16455 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1004 + difference 2 5) (sourceB1004 + difference 5 2) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1004 + difference 2 5) (sourceB1004 + difference 5 2) sourceC1004) = raw16456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16456; decide +kernel
    rw [ha]
    exact (canonical16456 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1004 + difference 3 0) (sourceB1004 + difference 0 3) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4861) := by
    have ha : (tripleCharges (sourceA1004 + difference 3 0) (sourceB1004 + difference 0 3) sourceC1004) = raw16457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16457; decide +kernel
    rw [ha]
    exact (canonical16457 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1004 + difference 3 1) (sourceB1004 + difference 1 3) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5385) := by
    have ha : (tripleCharges (sourceA1004 + difference 3 1) (sourceB1004 + difference 1 3) sourceC1004) = raw16458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16458; decide +kernel
    rw [ha]
    exact (canonical16458 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1004 + difference 3 2) (sourceB1004 + difference 2 3) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5399) := by
    have ha : (tripleCharges (sourceA1004 + difference 3 2) (sourceB1004 + difference 2 3) sourceC1004) = raw16459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16459; decide +kernel
    rw [ha]
    exact (canonical16459 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1004 + difference 3 4) (sourceB1004 + difference 4 3) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5385) := by
    have ha : (tripleCharges (sourceA1004 + difference 3 4) (sourceB1004 + difference 4 3) sourceC1004) = raw16460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16460; decide +kernel
    rw [ha]
    exact (canonical16460 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1004 + difference 3 5) (sourceB1004 + difference 5 3) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1004 + difference 3 5) (sourceB1004 + difference 5 3) sourceC1004) = raw16461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16461; decide +kernel
    rw [ha]
    exact (canonical16461 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1004 + difference 4 0) (sourceB1004 + difference 0 4) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA1004 + difference 4 0) (sourceB1004 + difference 0 4) sourceC1004) = raw16462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16462; decide +kernel
    rw [ha]
    exact (canonical16462 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1004 + difference 4 1) (sourceB1004 + difference 1 4) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA1004 + difference 4 1) (sourceB1004 + difference 1 4) sourceC1004) = raw16463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16463; decide +kernel
    rw [ha]
    exact (canonical16463 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1004 + difference 4 2) (sourceB1004 + difference 2 4) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA1004 + difference 4 2) (sourceB1004 + difference 2 4) sourceC1004) = raw16464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16464; decide +kernel
    rw [ha]
    exact (canonical16464 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1004 + difference 4 3) (sourceB1004 + difference 3 4) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA1004 + difference 4 3) (sourceB1004 + difference 3 4) sourceC1004) = raw16465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16465; decide +kernel
    rw [ha]
    exact (canonical16465 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1004 + difference 4 5) (sourceB1004 + difference 5 4) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1004 + difference 4 5) (sourceB1004 + difference 5 4) sourceC1004) = raw16466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16466; decide +kernel
    rw [ha]
    exact (canonical16466 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1004 + difference 5 0) (sourceB1004 + difference 0 5) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4850) := by
    have ha : (tripleCharges (sourceA1004 + difference 5 0) (sourceB1004 + difference 0 5) sourceC1004) = raw16467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16467; decide +kernel
    rw [ha]
    exact (canonical16467 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1004 + difference 5 1) (sourceB1004 + difference 1 5) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA1004 + difference 5 1) (sourceB1004 + difference 1 5) sourceC1004) = raw16468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16468; decide +kernel
    rw [ha]
    exact (canonical16468 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1004 + difference 5 2) (sourceB1004 + difference 2 5) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5183) := by
    have ha : (tripleCharges (sourceA1004 + difference 5 2) (sourceB1004 + difference 2 5) sourceC1004) = raw16469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16469; decide +kernel
    rw [ha]
    exact (canonical16469 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1004 + difference 5 3) (sourceB1004 + difference 3 5) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA1004 + difference 5 3) (sourceB1004 + difference 3 5) sourceC1004) = raw16470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16470; decide +kernel
    rw [ha]
    exact (canonical16470 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1004 + difference 5 4) (sourceB1004 + difference 4 5) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA1004 + difference 5 4) (sourceB1004 + difference 4 5) sourceC1004) = raw16471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16471; decide +kernel
    rw [ha]
    exact (canonical16471 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1004 sourceB1004 sourceC1004
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1004, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1005 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1005 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1005 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm1005 : Integer.Sparse Master := [(Sum.inr 2086, 1), (Sum.inr 2087, 1), (Sum.inr 2094, 1), (Sum.inr 2102, 1), (Sum.inr 2251, 1), (Sum.inr 2613, 1), (Sum.inr 2620, 1), (Sum.inr 2632, 1), (Sum.inr 2729, 1), (Sum.inr 3724, 1), (Sum.inr 3728, 1), (Sum.inr 3733, 1), (Sum.inr 3783, 1), (Sum.inr 3785, 1), (Sum.inr 3802, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1), (Sum.inr 3827, 1), (Sum.inr 3831, 1), (Sum.inr 3854, 1), (Sum.inr 3866, 1), (Sum.inr 3868, 1), (Sum.inr 3876, 1), (Sum.inr 3880, 1), (Sum.inr 3883, 1), (Sum.inr 3884, 1), (Sum.inr 3976, 1), (Sum.inr 3981, 1), (Sum.inr 3995, 1), (Sum.inr 4003, 1)]

theorem sourceEq1005 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1005 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1005 + difference 0 1) (sourceB1005 + difference 1 0) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA1005 + difference 0 1) (sourceB1005 + difference 1 0) sourceC1005) = raw16472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16472; decide +kernel
    rw [ha]
    exact (canonical16472 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1005 + difference 0 2) (sourceB1005 + difference 2 0) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3976) := by
    have ha : (tripleCharges (sourceA1005 + difference 0 2) (sourceB1005 + difference 2 0) sourceC1005) = raw16473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16473; decide +kernel
    rw [ha]
    exact (canonical16473 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1005 + difference 0 3) (sourceB1005 + difference 3 0) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA1005 + difference 0 3) (sourceB1005 + difference 3 0) sourceC1005) = raw16474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16474; decide +kernel
    rw [ha]
    exact (canonical16474 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1005 + difference 0 4) (sourceB1005 + difference 4 0) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1005 + difference 0 4) (sourceB1005 + difference 4 0) sourceC1005) = raw16475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16475; decide +kernel
    rw [ha]
    exact (canonical16475 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1005 + difference 0 5) (sourceB1005 + difference 5 0) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1005 + difference 0 5) (sourceB1005 + difference 5 0) sourceC1005) = raw16476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16476; decide +kernel
    rw [ha]
    exact (canonical16476 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1005 + difference 1 0) (sourceB1005 + difference 0 1) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA1005 + difference 1 0) (sourceB1005 + difference 0 1) sourceC1005) = raw16477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16477; decide +kernel
    rw [ha]
    exact (canonical16477 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1005 + difference 1 2) (sourceB1005 + difference 2 1) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA1005 + difference 1 2) (sourceB1005 + difference 2 1) sourceC1005) = raw16478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16478; decide +kernel
    rw [ha]
    exact (canonical16478 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1005 + difference 1 3) (sourceB1005 + difference 3 1) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA1005 + difference 1 3) (sourceB1005 + difference 3 1) sourceC1005) = raw16479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16479; decide +kernel
    rw [ha]
    exact (canonical16479 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1005 + difference 1 4) (sourceB1005 + difference 4 1) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA1005 + difference 1 4) (sourceB1005 + difference 4 1) sourceC1005) = raw16480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16480; decide +kernel
    rw [ha]
    exact (canonical16480 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1005 + difference 1 5) (sourceB1005 + difference 5 1) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA1005 + difference 1 5) (sourceB1005 + difference 5 1) sourceC1005) = raw16481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16481; decide +kernel
    rw [ha]
    exact (canonical16481 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1005 + difference 2 0) (sourceB1005 + difference 0 2) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2086) := by
    have ha : (tripleCharges (sourceA1005 + difference 2 0) (sourceB1005 + difference 0 2) sourceC1005) = raw16482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16482; decide +kernel
    rw [ha]
    exact (canonical16482 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1005 + difference 2 1) (sourceB1005 + difference 1 2) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA1005 + difference 2 1) (sourceB1005 + difference 1 2) sourceC1005) = raw16483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16483; decide +kernel
    rw [ha]
    exact (canonical16483 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1005 + difference 2 3) (sourceB1005 + difference 3 2) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3827) := by
    have ha : (tripleCharges (sourceA1005 + difference 2 3) (sourceB1005 + difference 3 2) sourceC1005) = raw16484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16484; decide +kernel
    rw [ha]
    exact (canonical16484 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1005 + difference 2 4) (sourceB1005 + difference 4 2) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA1005 + difference 2 4) (sourceB1005 + difference 4 2) sourceC1005) = raw16485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16485; decide +kernel
    rw [ha]
    exact (canonical16485 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1005 + difference 2 5) (sourceB1005 + difference 5 2) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1005 + difference 2 5) (sourceB1005 + difference 5 2) sourceC1005) = raw16486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16486; decide +kernel
    rw [ha]
    exact (canonical16486 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1005 + difference 3 0) (sourceB1005 + difference 0 3) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2102) := by
    have ha : (tripleCharges (sourceA1005 + difference 3 0) (sourceB1005 + difference 0 3) sourceC1005) = raw16487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16487; decide +kernel
    rw [ha]
    exact (canonical16487 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1005 + difference 3 1) (sourceB1005 + difference 1 3) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA1005 + difference 3 1) (sourceB1005 + difference 1 3) sourceC1005) = raw16488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16488; decide +kernel
    rw [ha]
    exact (canonical16488 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1005 + difference 3 2) (sourceB1005 + difference 2 3) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3785) := by
    have ha : (tripleCharges (sourceA1005 + difference 3 2) (sourceB1005 + difference 2 3) sourceC1005) = raw16489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16489; decide +kernel
    rw [ha]
    exact (canonical16489 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1005 + difference 3 4) (sourceB1005 + difference 4 3) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3868) := by
    have ha : (tripleCharges (sourceA1005 + difference 3 4) (sourceB1005 + difference 4 3) sourceC1005) = raw16490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16490; decide +kernel
    rw [ha]
    exact (canonical16490 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1005 + difference 3 5) (sourceB1005 + difference 5 3) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA1005 + difference 3 5) (sourceB1005 + difference 5 3) sourceC1005) = raw16491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16491; decide +kernel
    rw [ha]
    exact (canonical16491 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1005 + difference 4 0) (sourceB1005 + difference 0 4) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA1005 + difference 4 0) (sourceB1005 + difference 0 4) sourceC1005) = raw16492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16492; decide +kernel
    rw [ha]
    exact (canonical16492 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1005 + difference 4 1) (sourceB1005 + difference 1 4) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3728) := by
    have ha : (tripleCharges (sourceA1005 + difference 4 1) (sourceB1005 + difference 1 4) sourceC1005) = raw16493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16493; decide +kernel
    rw [ha]
    exact (canonical16493 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1005 + difference 4 2) (sourceB1005 + difference 2 4) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3783) := by
    have ha : (tripleCharges (sourceA1005 + difference 4 2) (sourceB1005 + difference 2 4) sourceC1005) = raw16494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16494; decide +kernel
    rw [ha]
    exact (canonical16494 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1005 + difference 4 3) (sourceB1005 + difference 3 4) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3831) := by
    have ha : (tripleCharges (sourceA1005 + difference 4 3) (sourceB1005 + difference 3 4) sourceC1005) = raw16495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16495; decide +kernel
    rw [ha]
    exact (canonical16495 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1005 + difference 4 5) (sourceB1005 + difference 5 4) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA1005 + difference 4 5) (sourceB1005 + difference 5 4) sourceC1005) = raw16496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16496; decide +kernel
    rw [ha]
    exact (canonical16496 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1005 + difference 5 0) (sourceB1005 + difference 0 5) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2087) := by
    have ha : (tripleCharges (sourceA1005 + difference 5 0) (sourceB1005 + difference 0 5) sourceC1005) = raw16497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16497; decide +kernel
    rw [ha]
    exact (canonical16497 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1005 + difference 5 1) (sourceB1005 + difference 1 5) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2620) := by
    have ha : (tripleCharges (sourceA1005 + difference 5 1) (sourceB1005 + difference 1 5) sourceC1005) = raw16498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16498; decide +kernel
    rw [ha]
    exact (canonical16498 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1005 + difference 5 2) (sourceB1005 + difference 2 5) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2613) := by
    have ha : (tripleCharges (sourceA1005 + difference 5 2) (sourceB1005 + difference 2 5) sourceC1005) = raw16499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16499; decide +kernel
    rw [ha]
    exact (canonical16499 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1005 + difference 5 3) (sourceB1005 + difference 3 5) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2632) := by
    have ha : (tripleCharges (sourceA1005 + difference 5 3) (sourceB1005 + difference 3 5) sourceC1005) = raw16500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16500; decide +kernel
    rw [ha]
    exact (canonical16500 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1005 + difference 5 4) (sourceB1005 + difference 4 5) sourceC1005) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA1005 + difference 5 4) (sourceB1005 + difference 4 5) sourceC1005) = raw16501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1005 sourceB1005 sourceC1005 difference raw16501; decide +kernel
    rw [ha]
    exact (canonical16501 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1005 sourceB1005 sourceC1005
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1005, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1006 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1006 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1006 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm1006 : Integer.Sparse Master := [(Sum.inr 2098, 1), (Sum.inr 2099, 1), (Sum.inr 2102, 1), (Sum.inr 2108, 1), (Sum.inr 2274, 1), (Sum.inr 3501, 1), (Sum.inr 3506, 1), (Sum.inr 3538, 1), (Sum.inr 3570, 1), (Sum.inr 3730, 1), (Sum.inr 3733, 1), (Sum.inr 3738, 1), (Sum.inr 3761, 1), (Sum.inr 3770, 1), (Sum.inr 3771, 1), (Sum.inr 3785, 1), (Sum.inr 3788, 1), (Sum.inr 3813, 1), (Sum.inr 3832, 1), (Sum.inr 3845, 1), (Sum.inr 3868, 1), (Sum.inr 3873, 1), (Sum.inr 3877, 1), (Sum.inr 3880, 1), (Sum.inr 3881, 1), (Sum.inr 3883, 1), (Sum.inr 3953, 1), (Sum.inr 3958, 1), (Sum.inr 3981, 1), (Sum.inr 3993, 1)]

theorem sourceEq1006 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1006 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1006 + difference 0 1) (sourceB1006 + difference 1 0) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA1006 + difference 0 1) (sourceB1006 + difference 1 0) sourceC1006) = raw16502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16502; decide +kernel
    rw [ha]
    exact (canonical16502 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1006 + difference 0 2) (sourceB1006 + difference 2 0) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA1006 + difference 0 2) (sourceB1006 + difference 2 0) sourceC1006) = raw16503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16503; decide +kernel
    rw [ha]
    exact (canonical16503 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1006 + difference 0 3) (sourceB1006 + difference 3 0) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1006 + difference 0 3) (sourceB1006 + difference 3 0) sourceC1006) = raw16504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16504; decide +kernel
    rw [ha]
    exact (canonical16504 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1006 + difference 0 4) (sourceB1006 + difference 4 0) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA1006 + difference 0 4) (sourceB1006 + difference 4 0) sourceC1006) = raw16505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16505; decide +kernel
    rw [ha]
    exact (canonical16505 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1006 + difference 0 5) (sourceB1006 + difference 5 0) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1006 + difference 0 5) (sourceB1006 + difference 5 0) sourceC1006) = raw16506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16506; decide +kernel
    rw [ha]
    exact (canonical16506 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1006 + difference 1 0) (sourceB1006 + difference 0 1) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA1006 + difference 1 0) (sourceB1006 + difference 0 1) sourceC1006) = raw16507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16507; decide +kernel
    rw [ha]
    exact (canonical16507 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1006 + difference 1 2) (sourceB1006 + difference 2 1) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA1006 + difference 1 2) (sourceB1006 + difference 2 1) sourceC1006) = raw16508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16508; decide +kernel
    rw [ha]
    exact (canonical16508 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1006 + difference 1 3) (sourceB1006 + difference 3 1) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA1006 + difference 1 3) (sourceB1006 + difference 3 1) sourceC1006) = raw16509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16509; decide +kernel
    rw [ha]
    exact (canonical16509 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1006 + difference 1 4) (sourceB1006 + difference 4 1) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3738) := by
    have ha : (tripleCharges (sourceA1006 + difference 1 4) (sourceB1006 + difference 4 1) sourceC1006) = raw16510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16510; decide +kernel
    rw [ha]
    exact (canonical16510 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1006 + difference 1 5) (sourceB1006 + difference 5 1) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA1006 + difference 1 5) (sourceB1006 + difference 5 1) sourceC1006) = raw16511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16511; decide +kernel
    rw [ha]
    exact (canonical16511 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1006 + difference 2 0) (sourceB1006 + difference 0 2) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2098) := by
    have ha : (tripleCharges (sourceA1006 + difference 2 0) (sourceB1006 + difference 0 2) sourceC1006) = raw16512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16512; decide +kernel
    rw [ha]
    exact (canonical16512 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1006 + difference 2 1) (sourceB1006 + difference 1 2) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA1006 + difference 2 1) (sourceB1006 + difference 1 2) sourceC1006) = raw16513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16513; decide +kernel
    rw [ha]
    exact (canonical16513 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1006 + difference 2 3) (sourceB1006 + difference 3 2) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA1006 + difference 2 3) (sourceB1006 + difference 3 2) sourceC1006) = raw16514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16514; decide +kernel
    rw [ha]
    exact (canonical16514 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1006 + difference 2 4) (sourceB1006 + difference 4 2) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3730) := by
    have ha : (tripleCharges (sourceA1006 + difference 2 4) (sourceB1006 + difference 4 2) sourceC1006) = raw16515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16515; decide +kernel
    rw [ha]
    exact (canonical16515 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1006 + difference 2 5) (sourceB1006 + difference 5 2) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1006 + difference 2 5) (sourceB1006 + difference 5 2) sourceC1006) = raw16516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16516; decide +kernel
    rw [ha]
    exact (canonical16516 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1006 + difference 3 0) (sourceB1006 + difference 0 3) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2102) := by
    have ha : (tripleCharges (sourceA1006 + difference 3 0) (sourceB1006 + difference 0 3) sourceC1006) = raw16517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16517; decide +kernel
    rw [ha]
    exact (canonical16517 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1006 + difference 3 1) (sourceB1006 + difference 1 3) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3868) := by
    have ha : (tripleCharges (sourceA1006 + difference 3 1) (sourceB1006 + difference 1 3) sourceC1006) = raw16518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16518; decide +kernel
    rw [ha]
    exact (canonical16518 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1006 + difference 3 2) (sourceB1006 + difference 2 3) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3785) := by
    have ha : (tripleCharges (sourceA1006 + difference 3 2) (sourceB1006 + difference 2 3) sourceC1006) = raw16519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16519; decide +kernel
    rw [ha]
    exact (canonical16519 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1006 + difference 3 4) (sourceB1006 + difference 4 3) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA1006 + difference 3 4) (sourceB1006 + difference 4 3) sourceC1006) = raw16520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16520; decide +kernel
    rw [ha]
    exact (canonical16520 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1006 + difference 3 5) (sourceB1006 + difference 5 3) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1006 + difference 3 5) (sourceB1006 + difference 5 3) sourceC1006) = raw16521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16521; decide +kernel
    rw [ha]
    exact (canonical16521 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1006 + difference 4 0) (sourceB1006 + difference 0 4) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA1006 + difference 4 0) (sourceB1006 + difference 0 4) sourceC1006) = raw16522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16522; decide +kernel
    rw [ha]
    exact (canonical16522 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1006 + difference 4 1) (sourceB1006 + difference 1 4) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA1006 + difference 4 1) (sourceB1006 + difference 1 4) sourceC1006) = raw16523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16523; decide +kernel
    rw [ha]
    exact (canonical16523 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1006 + difference 4 2) (sourceB1006 + difference 2 4) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA1006 + difference 4 2) (sourceB1006 + difference 2 4) sourceC1006) = raw16524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16524; decide +kernel
    rw [ha]
    exact (canonical16524 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1006 + difference 4 3) (sourceB1006 + difference 3 4) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3771) := by
    have ha : (tripleCharges (sourceA1006 + difference 4 3) (sourceB1006 + difference 3 4) sourceC1006) = raw16525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16525; decide +kernel
    rw [ha]
    exact (canonical16525 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1006 + difference 4 5) (sourceB1006 + difference 5 4) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA1006 + difference 4 5) (sourceB1006 + difference 5 4) sourceC1006) = raw16526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16526; decide +kernel
    rw [ha]
    exact (canonical16526 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1006 + difference 5 0) (sourceB1006 + difference 0 5) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2099) := by
    have ha : (tripleCharges (sourceA1006 + difference 5 0) (sourceB1006 + difference 0 5) sourceC1006) = raw16527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16527; decide +kernel
    rw [ha]
    exact (canonical16527 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1006 + difference 5 1) (sourceB1006 + difference 1 5) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA1006 + difference 5 1) (sourceB1006 + difference 1 5) sourceC1006) = raw16528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16528; decide +kernel
    rw [ha]
    exact (canonical16528 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1006 + difference 5 2) (sourceB1006 + difference 2 5) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3501) := by
    have ha : (tripleCharges (sourceA1006 + difference 5 2) (sourceB1006 + difference 2 5) sourceC1006) = raw16529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16529; decide +kernel
    rw [ha]
    exact (canonical16529 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1006 + difference 5 3) (sourceB1006 + difference 3 5) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA1006 + difference 5 3) (sourceB1006 + difference 3 5) sourceC1006) = raw16530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16530; decide +kernel
    rw [ha]
    exact (canonical16530 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1006 + difference 5 4) (sourceB1006 + difference 4 5) sourceC1006) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3506) := by
    have ha : (tripleCharges (sourceA1006 + difference 5 4) (sourceB1006 + difference 4 5) sourceC1006) = raw16531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1006 sourceB1006 sourceC1006 difference raw16531; decide +kernel
    rw [ha]
    exact (canonical16531 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1006 sourceB1006 sourceC1006
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1006, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1007 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1007 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1007 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm1007 : Integer.Sparse Master := [(Sum.inr 2866, 1), (Sum.inr 3171, 1), (Sum.inr 3174, 1), (Sum.inr 3180, 1), (Sum.inr 3181, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

theorem sourceEq1007 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1007 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1007 + difference 0 0) (sourceB1007 + difference 0 0) sourceC1007) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1007 + difference 0 0) (sourceB1007 + difference 0 0) sourceC1007) = raw16532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1007 sourceB1007 sourceC1007 difference raw16532; decide +kernel
    rw [ha]
    exact (canonical16532 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1007 + difference 1 0) (sourceB1007 + difference 0 1) sourceC1007) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA1007 + difference 1 0) (sourceB1007 + difference 0 1) sourceC1007) = raw16533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1007 sourceB1007 sourceC1007 difference raw16533; decide +kernel
    rw [ha]
    exact (canonical16533 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1007 + difference 2 0) (sourceB1007 + difference 0 2) sourceC1007) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3171) := by
    have ha : (tripleCharges (sourceA1007 + difference 2 0) (sourceB1007 + difference 0 2) sourceC1007) = raw16534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1007 sourceB1007 sourceC1007 difference raw16534; decide +kernel
    rw [ha]
    exact (canonical16534 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1007 + difference 3 0) (sourceB1007 + difference 0 3) sourceC1007) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3181) := by
    have ha : (tripleCharges (sourceA1007 + difference 3 0) (sourceB1007 + difference 0 3) sourceC1007) = raw16535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1007 sourceB1007 sourceC1007 difference raw16535; decide +kernel
    rw [ha]
    exact (canonical16535 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1007 + difference 4 0) (sourceB1007 + difference 0 4) sourceC1007) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA1007 + difference 4 0) (sourceB1007 + difference 0 4) sourceC1007) = raw16536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1007 sourceB1007 sourceC1007 difference raw16536; decide +kernel
    rw [ha]
    exact (canonical16536 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1007 + difference 5 0) (sourceB1007 + difference 0 5) sourceC1007) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2866) := by
    have ha : (tripleCharges (sourceA1007 + difference 5 0) (sourceB1007 + difference 0 5) sourceC1007) = raw16537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1007 sourceB1007 sourceC1007 difference raw16537; decide +kernel
    rw [ha]
    exact (canonical16537 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1007 + sourceB1007) sourceC1007) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1007 + sourceB1007) sourceC1007) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA1007 sourceB1007 sourceC1007 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1007 sourceB1007 sourceC1007
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1007, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1008 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1008 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1008 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm1008 : Integer.Sparse Master := [(Sum.inr 2867, 1), (Sum.inr 3693, 1), (Sum.inr 3720, 1), (Sum.inr 3733, 1), (Sum.inr 3845, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

theorem sourceEq1008 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1008 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1008 + difference 0 1) (sourceB1008 + difference 1 0) sourceC1008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA1008 + difference 0 1) (sourceB1008 + difference 1 0) sourceC1008) = raw16539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1008 sourceB1008 sourceC1008 difference raw16539; decide +kernel
    rw [ha]
    exact (canonical16539 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1008 + difference 1 1) (sourceB1008 + difference 1 1) sourceC1008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1008 + difference 1 1) (sourceB1008 + difference 1 1) sourceC1008) = raw16532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1008 sourceB1008 sourceC1008 difference raw16532; decide +kernel
    rw [ha]
    exact (canonical16532 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1008 + difference 2 1) (sourceB1008 + difference 1 2) sourceC1008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3720) := by
    have ha : (tripleCharges (sourceA1008 + difference 2 1) (sourceB1008 + difference 1 2) sourceC1008) = raw16540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1008 sourceB1008 sourceC1008 difference raw16540; decide +kernel
    rw [ha]
    exact (canonical16540 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1008 + difference 3 1) (sourceB1008 + difference 1 3) sourceC1008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA1008 + difference 3 1) (sourceB1008 + difference 1 3) sourceC1008) = raw16541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1008 sourceB1008 sourceC1008 difference raw16541; decide +kernel
    rw [ha]
    exact (canonical16541 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1008 + difference 4 1) (sourceB1008 + difference 1 4) sourceC1008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA1008 + difference 4 1) (sourceB1008 + difference 1 4) sourceC1008) = raw16542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1008 sourceB1008 sourceC1008 difference raw16542; decide +kernel
    rw [ha]
    exact (canonical16542 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1008 + difference 5 1) (sourceB1008 + difference 1 5) sourceC1008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA1008 + difference 5 1) (sourceB1008 + difference 1 5) sourceC1008) = raw16543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1008 sourceB1008 sourceC1008 difference raw16543; decide +kernel
    rw [ha]
    exact (canonical16543 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1008 + sourceB1008) sourceC1008) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1008 + sourceB1008) sourceC1008) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA1008 sourceB1008 sourceC1008 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1008 sourceB1008 sourceC1008
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1008, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1009 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1009 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1009 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm1009 : Integer.Sparse Master := [(Sum.inr 3171, 1), (Sum.inr 3720, 1), (Sum.inr 3730, 1), (Sum.inr 3946, 1), (Sum.inr 3959, 1), (Sum.inr 4024, 1), (Sum.inr 4092, -1)]

theorem sourceEq1009 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1009 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1009 + difference 2 0) (sourceB1009 + difference 0 2) sourceC1009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3171) := by
    have ha : (tripleCharges (sourceA1009 + difference 2 0) (sourceB1009 + difference 0 2) sourceC1009) = raw16534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1009 sourceB1009 sourceC1009 difference raw16534; decide +kernel
    rw [ha]
    exact (canonical16534 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1009 + difference 2 1) (sourceB1009 + difference 1 2) sourceC1009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3720) := by
    have ha : (tripleCharges (sourceA1009 + difference 2 1) (sourceB1009 + difference 1 2) sourceC1009) = raw16540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1009 sourceB1009 sourceC1009 difference raw16540; decide +kernel
    rw [ha]
    exact (canonical16540 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1009 + difference 2 2) (sourceB1009 + difference 2 2) sourceC1009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1009 + difference 2 2) (sourceB1009 + difference 2 2) sourceC1009) = raw16532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1009 sourceB1009 sourceC1009 difference raw16532; decide +kernel
    rw [ha]
    exact (canonical16532 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1009 + difference 2 3) (sourceB1009 + difference 3 2) sourceC1009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA1009 + difference 2 3) (sourceB1009 + difference 3 2) sourceC1009) = raw16544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1009 sourceB1009 sourceC1009 difference raw16544; decide +kernel
    rw [ha]
    exact (canonical16544 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1009 + difference 2 4) (sourceB1009 + difference 4 2) sourceC1009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3730) := by
    have ha : (tripleCharges (sourceA1009 + difference 2 4) (sourceB1009 + difference 4 2) sourceC1009) = raw16545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1009 sourceB1009 sourceC1009 difference raw16545; decide +kernel
    rw [ha]
    exact (canonical16545 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1009 + difference 2 5) (sourceB1009 + difference 5 2) sourceC1009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA1009 + difference 2 5) (sourceB1009 + difference 5 2) sourceC1009) = raw16546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1009 sourceB1009 sourceC1009 difference raw16546; decide +kernel
    rw [ha]
    exact (canonical16546 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1009 + sourceB1009) sourceC1009) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1009 + sourceB1009) sourceC1009) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA1009 sourceB1009 sourceC1009 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1009 sourceB1009 sourceC1009
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1009, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1010 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1010 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1010 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm1010 : Integer.Sparse Master := [(Sum.inr 2863, 1), (Sum.inr 3691, 1), (Sum.inr 3788, 1), (Sum.inr 3948, 1), (Sum.inr 3956, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

theorem sourceEq1010 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1010 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1010 + difference 0 2) (sourceB1010 + difference 2 0) sourceC1010) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA1010 + difference 0 2) (sourceB1010 + difference 2 0) sourceC1010) = raw16547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1010 sourceB1010 sourceC1010 difference raw16547; decide +kernel
    rw [ha]
    exact (canonical16547 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1010 + difference 1 2) (sourceB1010 + difference 2 1) sourceC1010) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA1010 + difference 1 2) (sourceB1010 + difference 2 1) sourceC1010) = raw16548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1010 sourceB1010 sourceC1010 difference raw16548; decide +kernel
    rw [ha]
    exact (canonical16548 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1010 + difference 2 2) (sourceB1010 + difference 2 2) sourceC1010) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1010 + difference 2 2) (sourceB1010 + difference 2 2) sourceC1010) = raw16532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1010 sourceB1010 sourceC1010 difference raw16532; decide +kernel
    rw [ha]
    exact (canonical16532 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1010 + difference 3 2) (sourceB1010 + difference 2 3) sourceC1010) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3948) := by
    have ha : (tripleCharges (sourceA1010 + difference 3 2) (sourceB1010 + difference 2 3) sourceC1010) = raw16549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1010 sourceB1010 sourceC1010 difference raw16549; decide +kernel
    rw [ha]
    exact (canonical16549 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1010 + difference 4 2) (sourceB1010 + difference 2 4) sourceC1010) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA1010 + difference 4 2) (sourceB1010 + difference 2 4) sourceC1010) = raw16550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1010 sourceB1010 sourceC1010 difference raw16550; decide +kernel
    rw [ha]
    exact (canonical16550 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1010 + difference 5 2) (sourceB1010 + difference 2 5) sourceC1010) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2863) := by
    have ha : (tripleCharges (sourceA1010 + difference 5 2) (sourceB1010 + difference 2 5) sourceC1010) = raw16551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1010 sourceB1010 sourceC1010 difference raw16551; decide +kernel
    rw [ha]
    exact (canonical16551 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1010 + sourceB1010) sourceC1010) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1010 + sourceB1010) sourceC1010) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA1010 sourceB1010 sourceC1010 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1010 sourceB1010 sourceC1010
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1010, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1011 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1011 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1011 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm1011 : Integer.Sparse Master := [(Sum.inr 3181, 1), (Sum.inr 3733, 2), (Sum.inr 3948, 1), (Sum.inr 3959, 2), (Sum.inr 4092, -1)]

theorem sourceEq1011 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1011 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1011 + difference 3 0) (sourceB1011 + difference 0 3) sourceC1011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3181) := by
    have ha : (tripleCharges (sourceA1011 + difference 3 0) (sourceB1011 + difference 0 3) sourceC1011) = raw16535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1011 sourceB1011 sourceC1011 difference raw16535; decide +kernel
    rw [ha]
    exact (canonical16535 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1011 + difference 3 1) (sourceB1011 + difference 1 3) sourceC1011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA1011 + difference 3 1) (sourceB1011 + difference 1 3) sourceC1011) = raw16541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1011 sourceB1011 sourceC1011 difference raw16541; decide +kernel
    rw [ha]
    exact (canonical16541 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1011 + difference 3 2) (sourceB1011 + difference 2 3) sourceC1011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3948) := by
    have ha : (tripleCharges (sourceA1011 + difference 3 2) (sourceB1011 + difference 2 3) sourceC1011) = raw16549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1011 sourceB1011 sourceC1011 difference raw16549; decide +kernel
    rw [ha]
    exact (canonical16549 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1011 + difference 3 3) (sourceB1011 + difference 3 3) sourceC1011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1011 + difference 3 3) (sourceB1011 + difference 3 3) sourceC1011) = raw16532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1011 sourceB1011 sourceC1011 difference raw16532; decide +kernel
    rw [ha]
    exact (canonical16532 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1011 + difference 3 4) (sourceB1011 + difference 4 3) sourceC1011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA1011 + difference 3 4) (sourceB1011 + difference 4 3) sourceC1011) = raw16552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1011 sourceB1011 sourceC1011 difference raw16552; decide +kernel
    rw [ha]
    exact (canonical16552 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1011 + difference 3 5) (sourceB1011 + difference 5 3) sourceC1011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1011 + difference 3 5) (sourceB1011 + difference 5 3) sourceC1011) = raw16553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1011 sourceB1011 sourceC1011 difference raw16553; decide +kernel
    rw [ha]
    exact (canonical16553 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1011 + sourceB1011) sourceC1011) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1011 + sourceB1011) sourceC1011) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA1011 sourceB1011 sourceC1011 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1011 sourceB1011 sourceC1011
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1011, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1012 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1012 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1012 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm1012 : Integer.Sparse Master := [(Sum.inr 3174, 1), (Sum.inr 3691, 1), (Sum.inr 3693, 1), (Sum.inr 3706, 1), (Sum.inr 3809, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

theorem sourceEq1012 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1012 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1012 + difference 4 0) (sourceB1012 + difference 0 4) sourceC1012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA1012 + difference 4 0) (sourceB1012 + difference 0 4) sourceC1012) = raw16536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1012 sourceB1012 sourceC1012 difference raw16536; decide +kernel
    rw [ha]
    exact (canonical16536 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1012 + difference 4 1) (sourceB1012 + difference 1 4) sourceC1012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA1012 + difference 4 1) (sourceB1012 + difference 1 4) sourceC1012) = raw16542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1012 sourceB1012 sourceC1012 difference raw16542; decide +kernel
    rw [ha]
    exact (canonical16542 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1012 + difference 4 2) (sourceB1012 + difference 2 4) sourceC1012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA1012 + difference 4 2) (sourceB1012 + difference 2 4) sourceC1012) = raw16550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1012 sourceB1012 sourceC1012 difference raw16550; decide +kernel
    rw [ha]
    exact (canonical16550 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1012 + difference 4 3) (sourceB1012 + difference 3 4) sourceC1012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA1012 + difference 4 3) (sourceB1012 + difference 3 4) sourceC1012) = raw16554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1012 sourceB1012 sourceC1012 difference raw16554; decide +kernel
    rw [ha]
    exact (canonical16554 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1012 + difference 4 4) (sourceB1012 + difference 4 4) sourceC1012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1012 + difference 4 4) (sourceB1012 + difference 4 4) sourceC1012) = raw16532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1012 sourceB1012 sourceC1012 difference raw16532; decide +kernel
    rw [ha]
    exact (canonical16532 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1012 + difference 4 5) (sourceB1012 + difference 5 4) sourceC1012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA1012 + difference 4 5) (sourceB1012 + difference 5 4) sourceC1012) = raw16555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1012 sourceB1012 sourceC1012 difference raw16555; decide +kernel
    rw [ha]
    exact (canonical16555 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1012 + sourceB1012) sourceC1012) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1012 + sourceB1012) sourceC1012) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA1012 sourceB1012 sourceC1012 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1012 sourceB1012 sourceC1012
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1012, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1013 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1013 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1013 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm1013 : Integer.Sparse Master := [(Sum.inr 3040, 1), (Sum.inr 3730, 1), (Sum.inr 3732, 1), (Sum.inr 3733, 1), (Sum.inr 3857, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

theorem sourceEq1013 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1013 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1013 + difference 0 4) (sourceB1013 + difference 4 0) sourceC1013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA1013 + difference 0 4) (sourceB1013 + difference 4 0) sourceC1013) = raw16556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1013 sourceB1013 sourceC1013 difference raw16556; decide +kernel
    rw [ha]
    exact (canonical16556 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1013 + difference 1 4) (sourceB1013 + difference 4 1) sourceC1013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA1013 + difference 1 4) (sourceB1013 + difference 4 1) sourceC1013) = raw16557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1013 sourceB1013 sourceC1013 difference raw16557; decide +kernel
    rw [ha]
    exact (canonical16557 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1013 + difference 2 4) (sourceB1013 + difference 4 2) sourceC1013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3730) := by
    have ha : (tripleCharges (sourceA1013 + difference 2 4) (sourceB1013 + difference 4 2) sourceC1013) = raw16545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1013 sourceB1013 sourceC1013 difference raw16545; decide +kernel
    rw [ha]
    exact (canonical16545 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1013 + difference 3 4) (sourceB1013 + difference 4 3) sourceC1013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA1013 + difference 3 4) (sourceB1013 + difference 4 3) sourceC1013) = raw16552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1013 sourceB1013 sourceC1013 difference raw16552; decide +kernel
    rw [ha]
    exact (canonical16552 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1013 + difference 4 4) (sourceB1013 + difference 4 4) sourceC1013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1013 + difference 4 4) (sourceB1013 + difference 4 4) sourceC1013) = raw16532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1013 sourceB1013 sourceC1013 difference raw16532; decide +kernel
    rw [ha]
    exact (canonical16532 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1013 + difference 5 4) (sourceB1013 + difference 4 5) sourceC1013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3040) := by
    have ha : (tripleCharges (sourceA1013 + difference 5 4) (sourceB1013 + difference 4 5) sourceC1013) = raw16558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1013 sourceB1013 sourceC1013 difference raw16558; decide +kernel
    rw [ha]
    exact (canonical16558 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1013 + sourceB1013) sourceC1013) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1013 + sourceB1013) sourceC1013) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA1013 sourceB1013 sourceC1013 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1013 sourceB1013 sourceC1013
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1013, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1014 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB1014 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1014 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1014 : Integer.Sparse Master := [(Sum.inr 5083, 1), (Sum.inr 5084, 1), (Sum.inr 5090, 1), (Sum.inr 5096, 1), (Sum.inr 5179, 1), (Sum.inr 5180, 1), (Sum.inr 5196, 1), (Sum.inr 5198, 1), (Sum.inr 5199, 1), (Sum.inr 5200, 1), (Sum.inr 5233, 1), (Sum.inr 5289, 1), (Sum.inr 5300, 1), (Sum.inr 5358, 1), (Sum.inr 5359, 1), (Sum.inr 5361, 1), (Sum.inr 5368, 1), (Sum.inr 5411, 1), (Sum.inr 5420, 1), (Sum.inr 5429, 1), (Sum.inr 5430, 1), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5436, 1), (Sum.inr 5446, 1), (Sum.inr 5449, 1), (Sum.inr 5451, 1), (Sum.inr 5468, 1), (Sum.inr 5473, 1), (Sum.inr 5475, 1)]

theorem sourceEq1014 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1014 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1014 + difference 0 1) (sourceB1014 + difference 1 0) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1014 + difference 0 1) (sourceB1014 + difference 1 0) sourceC1014) = raw15116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw15116; decide +kernel
    rw [ha]
    exact (canonical15116 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1014 + difference 0 2) (sourceB1014 + difference 2 0) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5468) := by
    have ha : (tripleCharges (sourceA1014 + difference 0 2) (sourceB1014 + difference 2 0) sourceC1014) = raw16143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16143; decide +kernel
    rw [ha]
    exact (canonical16143 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1014 + difference 0 3) (sourceB1014 + difference 3 0) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5475) := by
    have ha : (tripleCharges (sourceA1014 + difference 0 3) (sourceB1014 + difference 3 0) sourceC1014) = raw16324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16324; decide +kernel
    rw [ha]
    exact (canonical16324 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1014 + difference 0 4) (sourceB1014 + difference 4 0) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA1014 + difference 0 4) (sourceB1014 + difference 4 0) sourceC1014) = raw16559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16559; decide +kernel
    rw [ha]
    exact (canonical16559 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1014 + difference 0 5) (sourceB1014 + difference 5 0) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1014 + difference 0 5) (sourceB1014 + difference 5 0) sourceC1014) = raw16560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16560; decide +kernel
    rw [ha]
    exact (canonical16560 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1014 + difference 1 0) (sourceB1014 + difference 0 1) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5096) := by
    have ha : (tripleCharges (sourceA1014 + difference 1 0) (sourceB1014 + difference 0 1) sourceC1014) = raw16561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16561; decide +kernel
    rw [ha]
    exact (canonical16561 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1014 + difference 1 2) (sourceB1014 + difference 2 1) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5083) := by
    have ha : (tripleCharges (sourceA1014 + difference 1 2) (sourceB1014 + difference 2 1) sourceC1014) = raw16148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16148; decide +kernel
    rw [ha]
    exact (canonical16148 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1014 + difference 1 3) (sourceB1014 + difference 3 1) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA1014 + difference 1 3) (sourceB1014 + difference 3 1) sourceC1014) = raw16328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16328; decide +kernel
    rw [ha]
    exact (canonical16328 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1014 + difference 1 4) (sourceB1014 + difference 4 1) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5084) := by
    have ha : (tripleCharges (sourceA1014 + difference 1 4) (sourceB1014 + difference 4 1) sourceC1014) = raw16562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16562; decide +kernel
    rw [ha]
    exact (canonical16562 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1014 + difference 1 5) (sourceB1014 + difference 5 1) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA1014 + difference 1 5) (sourceB1014 + difference 5 1) sourceC1014) = raw16563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16563; decide +kernel
    rw [ha]
    exact (canonical16563 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1014 + difference 2 0) (sourceB1014 + difference 0 2) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5196) := by
    have ha : (tripleCharges (sourceA1014 + difference 2 0) (sourceB1014 + difference 0 2) sourceC1014) = raw15668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw15668; decide +kernel
    rw [ha]
    exact (canonical15668 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1014 + difference 2 1) (sourceB1014 + difference 1 2) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1014 + difference 2 1) (sourceB1014 + difference 1 2) sourceC1014) = raw15126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw15126; decide +kernel
    rw [ha]
    exact (canonical15126 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1014 + difference 2 3) (sourceB1014 + difference 3 2) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1014 + difference 2 3) (sourceB1014 + difference 3 2) sourceC1014) = raw15669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw15669; decide +kernel
    rw [ha]
    exact (canonical15669 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1014 + difference 2 4) (sourceB1014 + difference 4 2) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5179) := by
    have ha : (tripleCharges (sourceA1014 + difference 2 4) (sourceB1014 + difference 4 2) sourceC1014) = raw15670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw15670; decide +kernel
    rw [ha]
    exact (canonical15670 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1014 + difference 2 5) (sourceB1014 + difference 5 2) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA1014 + difference 2 5) (sourceB1014 + difference 5 2) sourceC1014) = raw15671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw15671; decide +kernel
    rw [ha]
    exact (canonical15671 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1014 + difference 3 0) (sourceB1014 + difference 0 3) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5200) := by
    have ha : (tripleCharges (sourceA1014 + difference 3 0) (sourceB1014 + difference 0 3) sourceC1014) = raw16564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16564; decide +kernel
    rw [ha]
    exact (canonical16564 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1014 + difference 3 1) (sourceB1014 + difference 1 3) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA1014 + difference 3 1) (sourceB1014 + difference 1 3) sourceC1014) = raw15131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw15131; decide +kernel
    rw [ha]
    exact (canonical15131 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1014 + difference 3 2) (sourceB1014 + difference 2 3) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5358) := by
    have ha : (tripleCharges (sourceA1014 + difference 3 2) (sourceB1014 + difference 2 3) sourceC1014) = raw16152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16152; decide +kernel
    rw [ha]
    exact (canonical16152 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1014 + difference 3 4) (sourceB1014 + difference 4 3) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5180) := by
    have ha : (tripleCharges (sourceA1014 + difference 3 4) (sourceB1014 + difference 4 3) sourceC1014) = raw16565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16565; decide +kernel
    rw [ha]
    exact (canonical16565 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1014 + difference 3 5) (sourceB1014 + difference 5 3) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5361) := by
    have ha : (tripleCharges (sourceA1014 + difference 3 5) (sourceB1014 + difference 5 3) sourceC1014) = raw16566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16566; decide +kernel
    rw [ha]
    exact (canonical16566 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1014 + difference 4 0) (sourceB1014 + difference 0 4) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA1014 + difference 4 0) (sourceB1014 + difference 0 4) sourceC1014) = raw15118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw15118; decide +kernel
    rw [ha]
    exact (canonical15118 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1014 + difference 4 1) (sourceB1014 + difference 1 4) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1014 + difference 4 1) (sourceB1014 + difference 1 4) sourceC1014) = raw15210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw15210; decide +kernel
    rw [ha]
    exact (canonical15210 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1014 + difference 4 2) (sourceB1014 + difference 2 4) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1014 + difference 4 2) (sourceB1014 + difference 2 4) sourceC1014) = raw15119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw15119; decide +kernel
    rw [ha]
    exact (canonical15119 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1014 + difference 4 3) (sourceB1014 + difference 3 4) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1014 + difference 4 3) (sourceB1014 + difference 3 4) sourceC1014) = raw15120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw15120; decide +kernel
    rw [ha]
    exact (canonical15120 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1014 + difference 4 5) (sourceB1014 + difference 5 4) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1014 + difference 4 5) (sourceB1014 + difference 5 4) sourceC1014) = raw15122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw15122; decide +kernel
    rw [ha]
    exact (canonical15122 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1014 + difference 5 0) (sourceB1014 + difference 0 5) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA1014 + difference 5 0) (sourceB1014 + difference 0 5) sourceC1014) = raw16567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16567; decide +kernel
    rw [ha]
    exact (canonical16567 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1014 + difference 5 1) (sourceB1014 + difference 1 5) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1014 + difference 5 1) (sourceB1014 + difference 1 5) sourceC1014) = raw15139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw15139; decide +kernel
    rw [ha]
    exact (canonical15139 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1014 + difference 5 2) (sourceB1014 + difference 2 5) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5420) := by
    have ha : (tripleCharges (sourceA1014 + difference 5 2) (sourceB1014 + difference 2 5) sourceC1014) = raw16160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16160; decide +kernel
    rw [ha]
    exact (canonical16160 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1014 + difference 5 3) (sourceB1014 + difference 3 5) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5449) := by
    have ha : (tripleCharges (sourceA1014 + difference 5 3) (sourceB1014 + difference 3 5) sourceC1014) = raw16336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16336; decide +kernel
    rw [ha]
    exact (canonical16336 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1014 + difference 5 4) (sourceB1014 + difference 4 5) sourceC1014) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA1014 + difference 5 4) (sourceB1014 + difference 4 5) sourceC1014) = raw16568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1014 sourceB1014 sourceC1014 difference raw16568; decide +kernel
    rw [ha]
    exact (canonical16568 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1014 sourceB1014 sourceC1014
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1014, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1015 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB1015 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1015 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1015 : Integer.Sparse Master := [(Sum.inr 2491, 1), (Sum.inr 2492, 1), (Sum.inr 2499, 1), (Sum.inr 2506, 1), (Sum.inr 2607, 1), (Sum.inr 2608, 1), (Sum.inr 2633, 1), (Sum.inr 2678, 1), (Sum.inr 2774, 1), (Sum.inr 3566, 1), (Sum.inr 3570, 1), (Sum.inr 3572, 1), (Sum.inr 3575, 1), (Sum.inr 3696, 1), (Sum.inr 3699, 1), (Sum.inr 3846, 1), (Sum.inr 3850, 1), (Sum.inr 3852, 1), (Sum.inr 3854, 1), (Sum.inr 3870, 1), (Sum.inr 3871, 1), (Sum.inr 3878, 1), (Sum.inr 3881, 1), (Sum.inr 3883, 1), (Sum.inr 3886, 1), (Sum.inr 3888, 1), (Sum.inr 3939, 1), (Sum.inr 3968, 1), (Sum.inr 3995, 1), (Sum.inr 4004, 1)]

theorem sourceEq1015 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1015 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1015 + difference 0 1) (sourceB1015 + difference 1 0) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA1015 + difference 0 1) (sourceB1015 + difference 1 0) sourceC1015) = raw15686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw15686; decide +kernel
    rw [ha]
    exact (canonical15686 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1015 + difference 0 2) (sourceB1015 + difference 2 0) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3968) := by
    have ha : (tripleCharges (sourceA1015 + difference 0 2) (sourceB1015 + difference 2 0) sourceC1015) = raw16164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16164; decide +kernel
    rw [ha]
    exact (canonical16164 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1015 + difference 0 3) (sourceB1015 + difference 3 0) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4004) := by
    have ha : (tripleCharges (sourceA1015 + difference 0 3) (sourceB1015 + difference 3 0) sourceC1015) = raw16569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16569; decide +kernel
    rw [ha]
    exact (canonical16569 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1015 + difference 0 4) (sourceB1015 + difference 4 0) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA1015 + difference 0 4) (sourceB1015 + difference 4 0) sourceC1015) = raw16570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16570; decide +kernel
    rw [ha]
    exact (canonical16570 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1015 + difference 0 5) (sourceB1015 + difference 5 0) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3939) := by
    have ha : (tripleCharges (sourceA1015 + difference 0 5) (sourceB1015 + difference 5 0) sourceC1015) = raw16571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16571; decide +kernel
    rw [ha]
    exact (canonical16571 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1015 + difference 1 0) (sourceB1015 + difference 0 1) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2506) := by
    have ha : (tripleCharges (sourceA1015 + difference 1 0) (sourceB1015 + difference 0 1) sourceC1015) = raw16572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16572; decide +kernel
    rw [ha]
    exact (canonical16572 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1015 + difference 1 2) (sourceB1015 + difference 2 1) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2491) := by
    have ha : (tripleCharges (sourceA1015 + difference 1 2) (sourceB1015 + difference 2 1) sourceC1015) = raw16169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16169; decide +kernel
    rw [ha]
    exact (canonical16169 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1015 + difference 1 3) (sourceB1015 + difference 3 1) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA1015 + difference 1 3) (sourceB1015 + difference 3 1) sourceC1015) = raw16573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16573; decide +kernel
    rw [ha]
    exact (canonical16573 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1015 + difference 1 4) (sourceB1015 + difference 4 1) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2492) := by
    have ha : (tripleCharges (sourceA1015 + difference 1 4) (sourceB1015 + difference 4 1) sourceC1015) = raw16574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16574; decide +kernel
    rw [ha]
    exact (canonical16574 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1015 + difference 1 5) (sourceB1015 + difference 5 1) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA1015 + difference 1 5) (sourceB1015 + difference 5 1) sourceC1015) = raw16575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16575; decide +kernel
    rw [ha]
    exact (canonical16575 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1015 + difference 2 0) (sourceB1015 + difference 0 2) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3566) := by
    have ha : (tripleCharges (sourceA1015 + difference 2 0) (sourceB1015 + difference 0 2) sourceC1015) = raw15690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw15690; decide +kernel
    rw [ha]
    exact (canonical15690 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1015 + difference 2 1) (sourceB1015 + difference 1 2) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA1015 + difference 2 1) (sourceB1015 + difference 1 2) sourceC1015) = raw15891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw15891; decide +kernel
    rw [ha]
    exact (canonical15891 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1015 + difference 2 3) (sourceB1015 + difference 3 2) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1015 + difference 2 3) (sourceB1015 + difference 3 2) sourceC1015) = raw15692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw15692; decide +kernel
    rw [ha]
    exact (canonical15692 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1015 + difference 2 4) (sourceB1015 + difference 4 2) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2607) := by
    have ha : (tripleCharges (sourceA1015 + difference 2 4) (sourceB1015 + difference 4 2) sourceC1015) = raw15693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw15693; decide +kernel
    rw [ha]
    exact (canonical15693 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1015 + difference 2 5) (sourceB1015 + difference 5 2) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3878) := by
    have ha : (tripleCharges (sourceA1015 + difference 2 5) (sourceB1015 + difference 5 2) sourceC1015) = raw15694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw15694; decide +kernel
    rw [ha]
    exact (canonical15694 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1015 + difference 3 0) (sourceB1015 + difference 0 3) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3575) := by
    have ha : (tripleCharges (sourceA1015 + difference 3 0) (sourceB1015 + difference 0 3) sourceC1015) = raw16576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16576; decide +kernel
    rw [ha]
    exact (canonical16576 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1015 + difference 3 1) (sourceB1015 + difference 1 3) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA1015 + difference 3 1) (sourceB1015 + difference 1 3) sourceC1015) = raw15702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw15702; decide +kernel
    rw [ha]
    exact (canonical15702 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1015 + difference 3 2) (sourceB1015 + difference 2 3) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3696) := by
    have ha : (tripleCharges (sourceA1015 + difference 3 2) (sourceB1015 + difference 2 3) sourceC1015) = raw16176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16176; decide +kernel
    rw [ha]
    exact (canonical16176 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1015 + difference 3 4) (sourceB1015 + difference 4 3) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2608) := by
    have ha : (tripleCharges (sourceA1015 + difference 3 4) (sourceB1015 + difference 4 3) sourceC1015) = raw16577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16577; decide +kernel
    rw [ha]
    exact (canonical16577 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1015 + difference 3 5) (sourceB1015 + difference 5 3) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3699) := by
    have ha : (tripleCharges (sourceA1015 + difference 3 5) (sourceB1015 + difference 5 3) sourceC1015) = raw16578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16578; decide +kernel
    rw [ha]
    exact (canonical16578 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1015 + difference 4 0) (sourceB1015 + difference 0 4) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA1015 + difference 4 0) (sourceB1015 + difference 0 4) sourceC1015) = raw16171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16171; decide +kernel
    rw [ha]
    exact (canonical16171 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1015 + difference 4 1) (sourceB1015 + difference 1 4) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1015 + difference 4 1) (sourceB1015 + difference 1 4) sourceC1015) = raw15707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw15707; decide +kernel
    rw [ha]
    exact (canonical15707 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1015 + difference 4 2) (sourceB1015 + difference 2 4) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA1015 + difference 4 2) (sourceB1015 + difference 2 4) sourceC1015) = raw16579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16579; decide +kernel
    rw [ha]
    exact (canonical16579 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1015 + difference 4 3) (sourceB1015 + difference 3 4) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA1015 + difference 4 3) (sourceB1015 + difference 3 4) sourceC1015) = raw16172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16172; decide +kernel
    rw [ha]
    exact (canonical16172 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1015 + difference 4 5) (sourceB1015 + difference 5 4) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA1015 + difference 4 5) (sourceB1015 + difference 5 4) sourceC1015) = raw15876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw15876; decide +kernel
    rw [ha]
    exact (canonical15876 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1015 + difference 5 0) (sourceB1015 + difference 0 5) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA1015 + difference 5 0) (sourceB1015 + difference 0 5) sourceC1015) = raw16580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16580; decide +kernel
    rw [ha]
    exact (canonical16580 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1015 + difference 5 1) (sourceB1015 + difference 1 5) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA1015 + difference 5 1) (sourceB1015 + difference 1 5) sourceC1015) = raw15712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw15712; decide +kernel
    rw [ha]
    exact (canonical15712 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1015 + difference 5 2) (sourceB1015 + difference 2 5) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3870) := by
    have ha : (tripleCharges (sourceA1015 + difference 5 2) (sourceB1015 + difference 2 5) sourceC1015) = raw16185 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16185; decide +kernel
    rw [ha]
    exact (canonical16185 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1015 + difference 5 3) (sourceB1015 + difference 3 5) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA1015 + difference 5 3) (sourceB1015 + difference 3 5) sourceC1015) = raw16581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16581; decide +kernel
    rw [ha]
    exact (canonical16581 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1015 + difference 5 4) (sourceB1015 + difference 4 5) sourceC1015) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA1015 + difference 5 4) (sourceB1015 + difference 4 5) sourceC1015) = raw16582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1015 sourceB1015 sourceC1015 difference raw16582; decide +kernel
    rw [ha]
    exact (canonical16582 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1015 sourceB1015 sourceC1015
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1015, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1016 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB1016 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1016 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1016 : Integer.Sparse Master := [(Sum.inr 2874, 1), (Sum.inr 2875, 1), (Sum.inr 2876, 1), (Sum.inr 2885, 1), (Sum.inr 3097, 1), (Sum.inr 3384, 1), (Sum.inr 3385, 1), (Sum.inr 3386, 1), (Sum.inr 3395, 1), (Sum.inr 3447, 1), (Sum.inr 3480, 1), (Sum.inr 3578, 1), (Sum.inr 3584, 1), (Sum.inr 3752, 1), (Sum.inr 3759, 1), (Sum.inr 3767, 1), (Sum.inr 3772, 1), (Sum.inr 3809, 1), (Sum.inr 3877, 1), (Sum.inr 3950, 1), (Sum.inr 3954, 1), (Sum.inr 3958, 1), (Sum.inr 3959, 1), (Sum.inr 3963, 1), (Sum.inr 3972, 1), (Sum.inr 3982, 1), (Sum.inr 3987, 1), (Sum.inr 4022, 1), (Sum.inr 4027, 1), (Sum.inr 4030, 1)]

theorem sourceEq1016 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1016 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1016 + difference 0 1) (sourceB1016 + difference 1 0) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1016 + difference 0 1) (sourceB1016 + difference 1 0) sourceC1016) = raw15143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw15143; decide +kernel
    rw [ha]
    exact (canonical15143 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1016 + difference 0 2) (sourceB1016 + difference 2 0) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3950) := by
    have ha : (tripleCharges (sourceA1016 + difference 0 2) (sourceB1016 + difference 2 0) sourceC1016) = raw16188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16188; decide +kernel
    rw [ha]
    exact (canonical16188 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1016 + difference 0 3) (sourceB1016 + difference 3 0) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA1016 + difference 0 3) (sourceB1016 + difference 3 0) sourceC1016) = raw16583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16583; decide +kernel
    rw [ha]
    exact (canonical16583 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1016 + difference 0 4) (sourceB1016 + difference 4 0) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA1016 + difference 0 4) (sourceB1016 + difference 4 0) sourceC1016) = raw16584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16584; decide +kernel
    rw [ha]
    exact (canonical16584 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1016 + difference 0 5) (sourceB1016 + difference 5 0) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA1016 + difference 0 5) (sourceB1016 + difference 5 0) sourceC1016) = raw16585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16585; decide +kernel
    rw [ha]
    exact (canonical16585 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1016 + difference 1 0) (sourceB1016 + difference 0 1) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2875) := by
    have ha : (tripleCharges (sourceA1016 + difference 1 0) (sourceB1016 + difference 0 1) sourceC1016) = raw16586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16586; decide +kernel
    rw [ha]
    exact (canonical16586 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1016 + difference 1 2) (sourceB1016 + difference 2 1) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3447) := by
    have ha : (tripleCharges (sourceA1016 + difference 1 2) (sourceB1016 + difference 2 1) sourceC1016) = raw16193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16193; decide +kernel
    rw [ha]
    exact (canonical16193 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1016 + difference 1 3) (sourceB1016 + difference 3 1) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA1016 + difference 1 3) (sourceB1016 + difference 3 1) sourceC1016) = raw16587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16587; decide +kernel
    rw [ha]
    exact (canonical16587 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1016 + difference 1 4) (sourceB1016 + difference 4 1) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3385) := by
    have ha : (tripleCharges (sourceA1016 + difference 1 4) (sourceB1016 + difference 4 1) sourceC1016) = raw16588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16588; decide +kernel
    rw [ha]
    exact (canonical16588 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1016 + difference 1 5) (sourceB1016 + difference 5 1) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA1016 + difference 1 5) (sourceB1016 + difference 5 1) sourceC1016) = raw16589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16589; decide +kernel
    rw [ha]
    exact (canonical16589 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1016 + difference 2 0) (sourceB1016 + difference 0 2) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2874) := by
    have ha : (tripleCharges (sourceA1016 + difference 2 0) (sourceB1016 + difference 0 2) sourceC1016) = raw15719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw15719; decide +kernel
    rw [ha]
    exact (canonical15719 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1016 + difference 2 1) (sourceB1016 + difference 1 2) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA1016 + difference 2 1) (sourceB1016 + difference 1 2) sourceC1016) = raw15153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw15153; decide +kernel
    rw [ha]
    exact (canonical15153 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1016 + difference 2 3) (sourceB1016 + difference 3 2) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1016 + difference 2 3) (sourceB1016 + difference 3 2) sourceC1016) = raw15720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw15720; decide +kernel
    rw [ha]
    exact (canonical15720 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1016 + difference 2 4) (sourceB1016 + difference 4 2) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3384) := by
    have ha : (tripleCharges (sourceA1016 + difference 2 4) (sourceB1016 + difference 4 2) sourceC1016) = raw15721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw15721; decide +kernel
    rw [ha]
    exact (canonical15721 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1016 + difference 2 5) (sourceB1016 + difference 5 2) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3759) := by
    have ha : (tripleCharges (sourceA1016 + difference 2 5) (sourceB1016 + difference 5 2) sourceC1016) = raw15722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw15722; decide +kernel
    rw [ha]
    exact (canonical15722 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1016 + difference 3 0) (sourceB1016 + difference 0 3) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2876) := by
    have ha : (tripleCharges (sourceA1016 + difference 3 0) (sourceB1016 + difference 0 3) sourceC1016) = raw16590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16590; decide +kernel
    rw [ha]
    exact (canonical16590 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1016 + difference 3 1) (sourceB1016 + difference 1 3) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA1016 + difference 3 1) (sourceB1016 + difference 1 3) sourceC1016) = raw15158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw15158; decide +kernel
    rw [ha]
    exact (canonical15158 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1016 + difference 3 2) (sourceB1016 + difference 2 3) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3752) := by
    have ha : (tripleCharges (sourceA1016 + difference 3 2) (sourceB1016 + difference 2 3) sourceC1016) = raw16197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16197; decide +kernel
    rw [ha]
    exact (canonical16197 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1016 + difference 3 4) (sourceB1016 + difference 4 3) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3386) := by
    have ha : (tripleCharges (sourceA1016 + difference 3 4) (sourceB1016 + difference 4 3) sourceC1016) = raw16591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16591; decide +kernel
    rw [ha]
    exact (canonical16591 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1016 + difference 3 5) (sourceB1016 + difference 5 3) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3772) := by
    have ha : (tripleCharges (sourceA1016 + difference 3 5) (sourceB1016 + difference 5 3) sourceC1016) = raw16592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16592; decide +kernel
    rw [ha]
    exact (canonical16592 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1016 + difference 4 0) (sourceB1016 + difference 0 4) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA1016 + difference 4 0) (sourceB1016 + difference 0 4) sourceC1016) = raw15145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw15145; decide +kernel
    rw [ha]
    exact (canonical15145 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1016 + difference 4 1) (sourceB1016 + difference 1 4) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA1016 + difference 4 1) (sourceB1016 + difference 1 4) sourceC1016) = raw15732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw15732; decide +kernel
    rw [ha]
    exact (canonical15732 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1016 + difference 4 2) (sourceB1016 + difference 2 4) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA1016 + difference 4 2) (sourceB1016 + difference 2 4) sourceC1016) = raw15146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw15146; decide +kernel
    rw [ha]
    exact (canonical15146 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1016 + difference 4 3) (sourceB1016 + difference 3 4) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA1016 + difference 4 3) (sourceB1016 + difference 3 4) sourceC1016) = raw15147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw15147; decide +kernel
    rw [ha]
    exact (canonical15147 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1016 + difference 4 5) (sourceB1016 + difference 5 4) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA1016 + difference 4 5) (sourceB1016 + difference 5 4) sourceC1016) = raw15149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw15149; decide +kernel
    rw [ha]
    exact (canonical15149 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1016 + difference 5 0) (sourceB1016 + difference 0 5) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2885) := by
    have ha : (tripleCharges (sourceA1016 + difference 5 0) (sourceB1016 + difference 0 5) sourceC1016) = raw16593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16593; decide +kernel
    rw [ha]
    exact (canonical16593 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1016 + difference 5 1) (sourceB1016 + difference 1 5) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4027) := by
    have ha : (tripleCharges (sourceA1016 + difference 5 1) (sourceB1016 + difference 1 5) sourceC1016) = raw15166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw15166; decide +kernel
    rw [ha]
    exact (canonical15166 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1016 + difference 5 2) (sourceB1016 + difference 2 5) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4022) := by
    have ha : (tripleCharges (sourceA1016 + difference 5 2) (sourceB1016 + difference 2 5) sourceC1016) = raw16205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16205; decide +kernel
    rw [ha]
    exact (canonical16205 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1016 + difference 5 3) (sourceB1016 + difference 3 5) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4030) := by
    have ha : (tripleCharges (sourceA1016 + difference 5 3) (sourceB1016 + difference 3 5) sourceC1016) = raw16594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16594; decide +kernel
    rw [ha]
    exact (canonical16594 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1016 + difference 5 4) (sourceB1016 + difference 4 5) sourceC1016) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA1016 + difference 5 4) (sourceB1016 + difference 4 5) sourceC1016) = raw16595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1016 sourceB1016 sourceC1016 difference raw16595; decide +kernel
    rw [ha]
    exact (canonical16595 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1016 sourceB1016 sourceC1016
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1016, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1017 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB1017 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1017 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1017 : Integer.Sparse Master := [(Sum.inr 2882, 1), (Sum.inr 3705, 1), (Sum.inr 3884, 1), (Sum.inr 3944, 1), (Sum.inr 3961, 1), (Sum.inr 3963, 1), (Sum.inr 4092, -1)]

theorem sourceEq1017 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1017 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1017 + difference 0 0) (sourceB1017 + difference 0 0) sourceC1017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA1017 + difference 0 0) (sourceB1017 + difference 0 0) sourceC1017) = raw15744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1017 sourceB1017 sourceC1017 difference raw15744; decide +kernel
    rw [ha]
    exact (canonical15744 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1017 + difference 0 1) (sourceB1017 + difference 1 0) sourceC1017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA1017 + difference 0 1) (sourceB1017 + difference 1 0) sourceC1017) = raw15739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1017 sourceB1017 sourceC1017 difference raw15739; decide +kernel
    rw [ha]
    exact (canonical15739 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1017 + difference 0 2) (sourceB1017 + difference 2 0) sourceC1017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3944) := by
    have ha : (tripleCharges (sourceA1017 + difference 0 2) (sourceB1017 + difference 2 0) sourceC1017) = raw16210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1017 sourceB1017 sourceC1017 difference raw16210; decide +kernel
    rw [ha]
    exact (canonical16210 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1017 + difference 0 3) (sourceB1017 + difference 3 0) sourceC1017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA1017 + difference 0 3) (sourceB1017 + difference 3 0) sourceC1017) = raw16596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1017 sourceB1017 sourceC1017 difference raw16596; decide +kernel
    rw [ha]
    exact (canonical16596 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1017 + difference 0 4) (sourceB1017 + difference 4 0) sourceC1017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA1017 + difference 0 4) (sourceB1017 + difference 4 0) sourceC1017) = raw16597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1017 sourceB1017 sourceC1017 difference raw16597; decide +kernel
    rw [ha]
    exact (canonical16597 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1017 + difference 0 5) (sourceB1017 + difference 5 0) sourceC1017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3705) := by
    have ha : (tripleCharges (sourceA1017 + difference 0 5) (sourceB1017 + difference 5 0) sourceC1017) = raw16598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1017 sourceB1017 sourceC1017 difference raw16598; decide +kernel
    rw [ha]
    exact (canonical16598 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1017 + sourceB1017) sourceC1017) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1017 + sourceB1017) sourceC1017) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA1017 sourceB1017 sourceC1017 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1017 sourceB1017 sourceC1017
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1017, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1018 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB1018 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1018 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1018 : Integer.Sparse Master := [(Sum.inr 2869, 1), (Sum.inr 2871, 1), (Sum.inr 2873, 1), (Sum.inr 2882, 1), (Sum.inr 3044, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

theorem sourceEq1018 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1018 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1018 + difference 0 4) (sourceB1018 + difference 4 0) sourceC1018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA1018 + difference 0 4) (sourceB1018 + difference 4 0) sourceC1018) = raw16597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1018 sourceB1018 sourceC1018 difference raw16597; decide +kernel
    rw [ha]
    exact (canonical16597 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1018 + difference 1 4) (sourceB1018 + difference 4 1) sourceC1018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2871) := by
    have ha : (tripleCharges (sourceA1018 + difference 1 4) (sourceB1018 + difference 4 1) sourceC1018) = raw16599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1018 sourceB1018 sourceC1018 difference raw16599; decide +kernel
    rw [ha]
    exact (canonical16599 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1018 + difference 2 4) (sourceB1018 + difference 4 2) sourceC1018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2869) := by
    have ha : (tripleCharges (sourceA1018 + difference 2 4) (sourceB1018 + difference 4 2) sourceC1018) = raw15746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1018 sourceB1018 sourceC1018 difference raw15746; decide +kernel
    rw [ha]
    exact (canonical15746 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1018 + difference 3 4) (sourceB1018 + difference 4 3) sourceC1018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2873) := by
    have ha : (tripleCharges (sourceA1018 + difference 3 4) (sourceB1018 + difference 4 3) sourceC1018) = raw16600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1018 sourceB1018 sourceC1018 difference raw16600; decide +kernel
    rw [ha]
    exact (canonical16600 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1018 + difference 4 4) (sourceB1018 + difference 4 4) sourceC1018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA1018 + difference 4 4) (sourceB1018 + difference 4 4) sourceC1018) = raw15744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1018 sourceB1018 sourceC1018 difference raw15744; decide +kernel
    rw [ha]
    exact (canonical15744 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1018 + difference 5 4) (sourceB1018 + difference 4 5) sourceC1018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3044) := by
    have ha : (tripleCharges (sourceA1018 + difference 5 4) (sourceB1018 + difference 4 5) sourceC1018) = raw16601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1018 sourceB1018 sourceC1018 difference raw16601; decide +kernel
    rw [ha]
    exact (canonical16601 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1018 + sourceB1018) sourceC1018) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1018 + sourceB1018) sourceC1018) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA1018 sourceB1018 sourceC1018 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1018 sourceB1018 sourceC1018
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1018, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1019 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1019 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceC1019 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceForm1019 : Integer.Sparse Master := [(Sum.inr 4740, 1), (Sum.inr 4742, 1), (Sum.inr 4744, 1), (Sum.inr 4750, 1), (Sum.inr 4896, 1), (Sum.inr 5123, 1), (Sum.inr 5125, 1), (Sum.inr 5163, 1), (Sum.inr 5192, 1), (Sum.inr 5193, 1), (Sum.inr 5204, 1), (Sum.inr 5228, 1), (Sum.inr 5284, 1), (Sum.inr 5326, 1), (Sum.inr 5330, 1), (Sum.inr 5391, 1), (Sum.inr 5397, 1), (Sum.inr 5401, 1), (Sum.inr 5404, 1), (Sum.inr 5406, 1), (Sum.inr 5411, 3), (Sum.inr 5443, 1), (Sum.inr 5447, 1), (Sum.inr 5450, 1), (Sum.inr 5451, 1), (Sum.inr 5452, 1), (Sum.inr 5453, 1), (Sum.inr 5485, 1)]

theorem sourceEq1019 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1019 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1019 + difference 0 1) (sourceB1019 + difference 1 0) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA1019 + difference 0 1) (sourceB1019 + difference 1 0) sourceC1019) = raw16602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16602; decide +kernel
    rw [ha]
    exact (canonical16602 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1019 + difference 0 2) (sourceB1019 + difference 2 0) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1019 + difference 0 2) (sourceB1019 + difference 2 0) sourceC1019) = raw16603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16603; decide +kernel
    rw [ha]
    exact (canonical16603 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1019 + difference 0 3) (sourceB1019 + difference 3 0) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA1019 + difference 0 3) (sourceB1019 + difference 3 0) sourceC1019) = raw16604 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16604; decide +kernel
    rw [ha]
    exact (canonical16604 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1019 + difference 0 4) (sourceB1019 + difference 4 0) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1019 + difference 0 4) (sourceB1019 + difference 4 0) sourceC1019) = raw16605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16605; decide +kernel
    rw [ha]
    exact (canonical16605 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1019 + difference 0 5) (sourceB1019 + difference 5 0) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1019 + difference 0 5) (sourceB1019 + difference 5 0) sourceC1019) = raw16606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16606; decide +kernel
    rw [ha]
    exact (canonical16606 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1019 + difference 1 0) (sourceB1019 + difference 0 1) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA1019 + difference 1 0) (sourceB1019 + difference 0 1) sourceC1019) = raw16607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16607; decide +kernel
    rw [ha]
    exact (canonical16607 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1019 + difference 1 2) (sourceB1019 + difference 2 1) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1019 + difference 1 2) (sourceB1019 + difference 2 1) sourceC1019) = raw16608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16608; decide +kernel
    rw [ha]
    exact (canonical16608 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1019 + difference 1 3) (sourceB1019 + difference 3 1) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1019 + difference 1 3) (sourceB1019 + difference 3 1) sourceC1019) = raw16609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16609; decide +kernel
    rw [ha]
    exact (canonical16609 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1019 + difference 1 4) (sourceB1019 + difference 4 1) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA1019 + difference 1 4) (sourceB1019 + difference 4 1) sourceC1019) = raw16610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16610; decide +kernel
    rw [ha]
    exact (canonical16610 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1019 + difference 1 5) (sourceB1019 + difference 5 1) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA1019 + difference 1 5) (sourceB1019 + difference 5 1) sourceC1019) = raw16611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16611; decide +kernel
    rw [ha]
    exact (canonical16611 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1019 + difference 2 0) (sourceB1019 + difference 0 2) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA1019 + difference 2 0) (sourceB1019 + difference 0 2) sourceC1019) = raw16612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16612; decide +kernel
    rw [ha]
    exact (canonical16612 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1019 + difference 2 1) (sourceB1019 + difference 1 2) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA1019 + difference 2 1) (sourceB1019 + difference 1 2) sourceC1019) = raw16613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16613; decide +kernel
    rw [ha]
    exact (canonical16613 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1019 + difference 2 3) (sourceB1019 + difference 3 2) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5391) := by
    have ha : (tripleCharges (sourceA1019 + difference 2 3) (sourceB1019 + difference 3 2) sourceC1019) = raw16614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16614; decide +kernel
    rw [ha]
    exact (canonical16614 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1019 + difference 2 4) (sourceB1019 + difference 4 2) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1019 + difference 2 4) (sourceB1019 + difference 4 2) sourceC1019) = raw16615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16615; decide +kernel
    rw [ha]
    exact (canonical16615 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1019 + difference 2 5) (sourceB1019 + difference 5 2) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1019 + difference 2 5) (sourceB1019 + difference 5 2) sourceC1019) = raw16616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16616; decide +kernel
    rw [ha]
    exact (canonical16616 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1019 + difference 3 0) (sourceB1019 + difference 0 3) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA1019 + difference 3 0) (sourceB1019 + difference 0 3) sourceC1019) = raw16617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16617; decide +kernel
    rw [ha]
    exact (canonical16617 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1019 + difference 3 1) (sourceB1019 + difference 1 3) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA1019 + difference 3 1) (sourceB1019 + difference 1 3) sourceC1019) = raw16618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16618; decide +kernel
    rw [ha]
    exact (canonical16618 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1019 + difference 3 2) (sourceB1019 + difference 2 3) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1019 + difference 3 2) (sourceB1019 + difference 2 3) sourceC1019) = raw16619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16619; decide +kernel
    rw [ha]
    exact (canonical16619 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1019 + difference 3 4) (sourceB1019 + difference 4 3) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1019 + difference 3 4) (sourceB1019 + difference 4 3) sourceC1019) = raw16620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16620; decide +kernel
    rw [ha]
    exact (canonical16620 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1019 + difference 3 5) (sourceB1019 + difference 5 3) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1019 + difference 3 5) (sourceB1019 + difference 5 3) sourceC1019) = raw16621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16621; decide +kernel
    rw [ha]
    exact (canonical16621 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1019 + difference 4 0) (sourceB1019 + difference 0 4) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5193) := by
    have ha : (tripleCharges (sourceA1019 + difference 4 0) (sourceB1019 + difference 0 4) sourceC1019) = raw16622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16622; decide +kernel
    rw [ha]
    exact (canonical16622 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1019 + difference 4 1) (sourceB1019 + difference 1 4) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5125) := by
    have ha : (tripleCharges (sourceA1019 + difference 4 1) (sourceB1019 + difference 1 4) sourceC1019) = raw16623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16623; decide +kernel
    rw [ha]
    exact (canonical16623 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1019 + difference 4 2) (sourceB1019 + difference 2 4) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5326) := by
    have ha : (tripleCharges (sourceA1019 + difference 4 2) (sourceB1019 + difference 2 4) sourceC1019) = raw16624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16624; decide +kernel
    rw [ha]
    exact (canonical16624 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1019 + difference 4 3) (sourceB1019 + difference 3 4) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5330) := by
    have ha : (tripleCharges (sourceA1019 + difference 4 3) (sourceB1019 + difference 3 4) sourceC1019) = raw16625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16625; decide +kernel
    rw [ha]
    exact (canonical16625 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1019 + difference 4 5) (sourceB1019 + difference 5 4) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1019 + difference 4 5) (sourceB1019 + difference 5 4) sourceC1019) = raw16626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16626; decide +kernel
    rw [ha]
    exact (canonical16626 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1019 + difference 5 0) (sourceB1019 + difference 0 5) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA1019 + difference 5 0) (sourceB1019 + difference 0 5) sourceC1019) = raw16627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16627; decide +kernel
    rw [ha]
    exact (canonical16627 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1019 + difference 5 1) (sourceB1019 + difference 1 5) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA1019 + difference 5 1) (sourceB1019 + difference 1 5) sourceC1019) = raw16628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16628; decide +kernel
    rw [ha]
    exact (canonical16628 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1019 + difference 5 2) (sourceB1019 + difference 2 5) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA1019 + difference 5 2) (sourceB1019 + difference 2 5) sourceC1019) = raw16629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16629; decide +kernel
    rw [ha]
    exact (canonical16629 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1019 + difference 5 3) (sourceB1019 + difference 3 5) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4750) := by
    have ha : (tripleCharges (sourceA1019 + difference 5 3) (sourceB1019 + difference 3 5) sourceC1019) = raw16630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16630; decide +kernel
    rw [ha]
    exact (canonical16630 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1019 + difference 5 4) (sourceB1019 + difference 4 5) sourceC1019) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA1019 + difference 5 4) (sourceB1019 + difference 4 5) sourceC1019) = raw16631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1019 sourceB1019 sourceC1019 difference raw16631; decide +kernel
    rw [ha]
    exact (canonical16631 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1019 sourceB1019 sourceC1019
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1019, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1020 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1020 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceC1020 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceForm1020 : Integer.Sparse Master := [(Sum.inr 1913, 1), (Sum.inr 1915, 1), (Sum.inr 1917, 1), (Sum.inr 1949, 1), (Sum.inr 2266, 1), (Sum.inr 2853, 1), (Sum.inr 2856, 1), (Sum.inr 2881, 1), (Sum.inr 3077, 1), (Sum.inr 3370, 1), (Sum.inr 3372, 1), (Sum.inr 3391, 1), (Sum.inr 3564, 1), (Sum.inr 3653, 1), (Sum.inr 3666, 1), (Sum.inr 3778, 1), (Sum.inr 3782, 1), (Sum.inr 3801, 1), (Sum.inr 3804, 1), (Sum.inr 3809, 3), (Sum.inr 3815, 1), (Sum.inr 3862, 1), (Sum.inr 3912, 1), (Sum.inr 3913, 1), (Sum.inr 4010, 1), (Sum.inr 4025, 1), (Sum.inr 4029, 1), (Sum.inr 4039, 1)]

theorem sourceEq1020 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1020 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1020 + difference 0 1) (sourceB1020 + difference 1 0) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA1020 + difference 0 1) (sourceB1020 + difference 1 0) sourceC1020) = raw16632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16632; decide +kernel
    rw [ha]
    exact (canonical16632 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1020 + difference 0 2) (sourceB1020 + difference 2 0) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA1020 + difference 0 2) (sourceB1020 + difference 2 0) sourceC1020) = raw16633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16633; decide +kernel
    rw [ha]
    exact (canonical16633 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1020 + difference 0 3) (sourceB1020 + difference 3 0) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3815) := by
    have ha : (tripleCharges (sourceA1020 + difference 0 3) (sourceB1020 + difference 3 0) sourceC1020) = raw16634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16634; decide +kernel
    rw [ha]
    exact (canonical16634 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1020 + difference 0 4) (sourceB1020 + difference 4 0) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA1020 + difference 0 4) (sourceB1020 + difference 4 0) sourceC1020) = raw16635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16635; decide +kernel
    rw [ha]
    exact (canonical16635 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1020 + difference 0 5) (sourceB1020 + difference 5 0) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA1020 + difference 0 5) (sourceB1020 + difference 5 0) sourceC1020) = raw16636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16636; decide +kernel
    rw [ha]
    exact (canonical16636 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1020 + difference 1 0) (sourceB1020 + difference 0 1) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA1020 + difference 1 0) (sourceB1020 + difference 0 1) sourceC1020) = raw16637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16637; decide +kernel
    rw [ha]
    exact (canonical16637 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1020 + difference 1 2) (sourceB1020 + difference 2 1) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA1020 + difference 1 2) (sourceB1020 + difference 2 1) sourceC1020) = raw16638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16638; decide +kernel
    rw [ha]
    exact (canonical16638 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1020 + difference 1 3) (sourceB1020 + difference 3 1) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA1020 + difference 1 3) (sourceB1020 + difference 3 1) sourceC1020) = raw16639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16639; decide +kernel
    rw [ha]
    exact (canonical16639 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1020 + difference 1 4) (sourceB1020 + difference 4 1) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3912) := by
    have ha : (tripleCharges (sourceA1020 + difference 1 4) (sourceB1020 + difference 4 1) sourceC1020) = raw16640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16640; decide +kernel
    rw [ha]
    exact (canonical16640 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1020 + difference 1 5) (sourceB1020 + difference 5 1) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4039) := by
    have ha : (tripleCharges (sourceA1020 + difference 1 5) (sourceB1020 + difference 5 1) sourceC1020) = raw16641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16641; decide +kernel
    rw [ha]
    exact (canonical16641 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1020 + difference 2 0) (sourceB1020 + difference 0 2) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2853) := by
    have ha : (tripleCharges (sourceA1020 + difference 2 0) (sourceB1020 + difference 0 2) sourceC1020) = raw16642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16642; decide +kernel
    rw [ha]
    exact (canonical16642 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1020 + difference 2 1) (sourceB1020 + difference 1 2) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3370) := by
    have ha : (tripleCharges (sourceA1020 + difference 2 1) (sourceB1020 + difference 1 2) sourceC1020) = raw16643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16643; decide +kernel
    rw [ha]
    exact (canonical16643 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1020 + difference 2 3) (sourceB1020 + difference 3 2) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3778) := by
    have ha : (tripleCharges (sourceA1020 + difference 2 3) (sourceB1020 + difference 3 2) sourceC1020) = raw16644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16644; decide +kernel
    rw [ha]
    exact (canonical16644 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1020 + difference 2 4) (sourceB1020 + difference 4 2) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA1020 + difference 2 4) (sourceB1020 + difference 4 2) sourceC1020) = raw16645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16645; decide +kernel
    rw [ha]
    exact (canonical16645 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1020 + difference 2 5) (sourceB1020 + difference 5 2) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4025) := by
    have ha : (tripleCharges (sourceA1020 + difference 2 5) (sourceB1020 + difference 5 2) sourceC1020) = raw16646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16646; decide +kernel
    rw [ha]
    exact (canonical16646 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1020 + difference 3 0) (sourceB1020 + difference 0 3) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA1020 + difference 3 0) (sourceB1020 + difference 0 3) sourceC1020) = raw16647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16647; decide +kernel
    rw [ha]
    exact (canonical16647 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1020 + difference 3 1) (sourceB1020 + difference 1 3) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA1020 + difference 3 1) (sourceB1020 + difference 1 3) sourceC1020) = raw16648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16648; decide +kernel
    rw [ha]
    exact (canonical16648 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1020 + difference 3 2) (sourceB1020 + difference 2 3) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA1020 + difference 3 2) (sourceB1020 + difference 2 3) sourceC1020) = raw16649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16649; decide +kernel
    rw [ha]
    exact (canonical16649 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1020 + difference 3 4) (sourceB1020 + difference 4 3) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA1020 + difference 3 4) (sourceB1020 + difference 4 3) sourceC1020) = raw16650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16650; decide +kernel
    rw [ha]
    exact (canonical16650 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1020 + difference 3 5) (sourceB1020 + difference 5 3) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA1020 + difference 3 5) (sourceB1020 + difference 5 3) sourceC1020) = raw16651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16651; decide +kernel
    rw [ha]
    exact (canonical16651 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1020 + difference 4 0) (sourceB1020 + difference 0 4) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2856) := by
    have ha : (tripleCharges (sourceA1020 + difference 4 0) (sourceB1020 + difference 0 4) sourceC1020) = raw16652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16652; decide +kernel
    rw [ha]
    exact (canonical16652 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1020 + difference 4 1) (sourceB1020 + difference 1 4) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3372) := by
    have ha : (tripleCharges (sourceA1020 + difference 4 1) (sourceB1020 + difference 1 4) sourceC1020) = raw16653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16653; decide +kernel
    rw [ha]
    exact (canonical16653 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1020 + difference 4 2) (sourceB1020 + difference 2 4) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3653) := by
    have ha : (tripleCharges (sourceA1020 + difference 4 2) (sourceB1020 + difference 2 4) sourceC1020) = raw16654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16654; decide +kernel
    rw [ha]
    exact (canonical16654 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1020 + difference 4 3) (sourceB1020 + difference 3 4) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3666) := by
    have ha : (tripleCharges (sourceA1020 + difference 4 3) (sourceB1020 + difference 3 4) sourceC1020) = raw16655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16655; decide +kernel
    rw [ha]
    exact (canonical16655 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1020 + difference 4 5) (sourceB1020 + difference 5 4) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA1020 + difference 4 5) (sourceB1020 + difference 5 4) sourceC1020) = raw16656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16656; decide +kernel
    rw [ha]
    exact (canonical16656 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1020 + difference 5 0) (sourceB1020 + difference 0 5) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1915) := by
    have ha : (tripleCharges (sourceA1020 + difference 5 0) (sourceB1020 + difference 0 5) sourceC1020) = raw16657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16657; decide +kernel
    rw [ha]
    exact (canonical16657 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1020 + difference 5 1) (sourceB1020 + difference 1 5) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1917) := by
    have ha : (tripleCharges (sourceA1020 + difference 5 1) (sourceB1020 + difference 1 5) sourceC1020) = raw16658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16658; decide +kernel
    rw [ha]
    exact (canonical16658 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1020 + difference 5 2) (sourceB1020 + difference 2 5) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1913) := by
    have ha : (tripleCharges (sourceA1020 + difference 5 2) (sourceB1020 + difference 2 5) sourceC1020) = raw16659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16659; decide +kernel
    rw [ha]
    exact (canonical16659 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1020 + difference 5 3) (sourceB1020 + difference 3 5) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1949) := by
    have ha : (tripleCharges (sourceA1020 + difference 5 3) (sourceB1020 + difference 3 5) sourceC1020) = raw16660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16660; decide +kernel
    rw [ha]
    exact (canonical16660 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1020 + difference 5 4) (sourceB1020 + difference 4 5) sourceC1020) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA1020 + difference 5 4) (sourceB1020 + difference 4 5) sourceC1020) = raw16661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1020 sourceB1020 sourceC1020 difference raw16661; decide +kernel
    rw [ha]
    exact (canonical16661 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1020 sourceB1020 sourceC1020
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1020, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1021 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1021 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceC1021 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceForm1021 : Integer.Sparse Master := [(Sum.inr 4852, 1), (Sum.inr 4853, 1), (Sum.inr 4856, 1), (Sum.inr 4867, 1), (Sum.inr 4891, 1), (Sum.inr 5074, 1), (Sum.inr 5080, 1), (Sum.inr 5105, 1), (Sum.inr 5260, 1), (Sum.inr 5353, 1), (Sum.inr 5355, 1), (Sum.inr 5370, 1), (Sum.inr 5378, 1), (Sum.inr 5384, 1), (Sum.inr 5397, 1), (Sum.inr 5402, 1), (Sum.inr 5405, 1), (Sum.inr 5407, 1), (Sum.inr 5409, 1), (Sum.inr 5410, 1), (Sum.inr 5411, 1), (Sum.inr 5412, 2), (Sum.inr 5425, 1), (Sum.inr 5434, 1), (Sum.inr 5436, 1), (Sum.inr 5445, 1), (Sum.inr 5446, 2), (Sum.inr 5483, 1)]

theorem sourceEq1021 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1021 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1021 + difference 0 1) (sourceB1021 + difference 1 0) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1021 + difference 0 1) (sourceB1021 + difference 1 0) sourceC1021) = raw16662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16662; decide +kernel
    rw [ha]
    exact (canonical16662 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1021 + difference 0 2) (sourceB1021 + difference 2 0) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1021 + difference 0 2) (sourceB1021 + difference 2 0) sourceC1021) = raw16663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16663; decide +kernel
    rw [ha]
    exact (canonical16663 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1021 + difference 0 3) (sourceB1021 + difference 3 0) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1021 + difference 0 3) (sourceB1021 + difference 3 0) sourceC1021) = raw16664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16664; decide +kernel
    rw [ha]
    exact (canonical16664 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1021 + difference 0 4) (sourceB1021 + difference 4 0) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1021 + difference 0 4) (sourceB1021 + difference 4 0) sourceC1021) = raw16665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16665; decide +kernel
    rw [ha]
    exact (canonical16665 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1021 + difference 0 5) (sourceB1021 + difference 5 0) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1021 + difference 0 5) (sourceB1021 + difference 5 0) sourceC1021) = raw16666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16666; decide +kernel
    rw [ha]
    exact (canonical16666 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1021 + difference 1 0) (sourceB1021 + difference 0 1) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA1021 + difference 1 0) (sourceB1021 + difference 0 1) sourceC1021) = raw16667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16667; decide +kernel
    rw [ha]
    exact (canonical16667 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1021 + difference 1 2) (sourceB1021 + difference 2 1) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5407) := by
    have ha : (tripleCharges (sourceA1021 + difference 1 2) (sourceB1021 + difference 2 1) sourceC1021) = raw16668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16668; decide +kernel
    rw [ha]
    exact (canonical16668 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1021 + difference 1 3) (sourceB1021 + difference 3 1) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1021 + difference 1 3) (sourceB1021 + difference 3 1) sourceC1021) = raw16669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16669; decide +kernel
    rw [ha]
    exact (canonical16669 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1021 + difference 1 4) (sourceB1021 + difference 4 1) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1021 + difference 1 4) (sourceB1021 + difference 4 1) sourceC1021) = raw16670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16670; decide +kernel
    rw [ha]
    exact (canonical16670 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1021 + difference 1 5) (sourceB1021 + difference 5 1) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1021 + difference 1 5) (sourceB1021 + difference 5 1) sourceC1021) = raw16671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16671; decide +kernel
    rw [ha]
    exact (canonical16671 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1021 + difference 2 0) (sourceB1021 + difference 0 2) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA1021 + difference 2 0) (sourceB1021 + difference 0 2) sourceC1021) = raw16672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16672; decide +kernel
    rw [ha]
    exact (canonical16672 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1021 + difference 2 1) (sourceB1021 + difference 1 2) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1021 + difference 2 1) (sourceB1021 + difference 1 2) sourceC1021) = raw16673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16673; decide +kernel
    rw [ha]
    exact (canonical16673 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1021 + difference 2 3) (sourceB1021 + difference 3 2) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1021 + difference 2 3) (sourceB1021 + difference 3 2) sourceC1021) = raw16674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16674; decide +kernel
    rw [ha]
    exact (canonical16674 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1021 + difference 2 4) (sourceB1021 + difference 4 2) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1021 + difference 2 4) (sourceB1021 + difference 4 2) sourceC1021) = raw16675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16675; decide +kernel
    rw [ha]
    exact (canonical16675 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1021 + difference 2 5) (sourceB1021 + difference 5 2) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1021 + difference 2 5) (sourceB1021 + difference 5 2) sourceC1021) = raw16676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16676; decide +kernel
    rw [ha]
    exact (canonical16676 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1021 + difference 3 0) (sourceB1021 + difference 0 3) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA1021 + difference 3 0) (sourceB1021 + difference 0 3) sourceC1021) = raw16677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16677; decide +kernel
    rw [ha]
    exact (canonical16677 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1021 + difference 3 1) (sourceB1021 + difference 1 3) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1021 + difference 3 1) (sourceB1021 + difference 1 3) sourceC1021) = raw16678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16678; decide +kernel
    rw [ha]
    exact (canonical16678 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1021 + difference 3 2) (sourceB1021 + difference 2 3) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5402) := by
    have ha : (tripleCharges (sourceA1021 + difference 3 2) (sourceB1021 + difference 2 3) sourceC1021) = raw16679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16679; decide +kernel
    rw [ha]
    exact (canonical16679 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1021 + difference 3 4) (sourceB1021 + difference 4 3) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA1021 + difference 3 4) (sourceB1021 + difference 4 3) sourceC1021) = raw16680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16680; decide +kernel
    rw [ha]
    exact (canonical16680 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1021 + difference 3 5) (sourceB1021 + difference 5 3) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1021 + difference 3 5) (sourceB1021 + difference 5 3) sourceC1021) = raw16681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16681; decide +kernel
    rw [ha]
    exact (canonical16681 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1021 + difference 4 0) (sourceB1021 + difference 0 4) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA1021 + difference 4 0) (sourceB1021 + difference 0 4) sourceC1021) = raw16682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16682; decide +kernel
    rw [ha]
    exact (canonical16682 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1021 + difference 4 1) (sourceB1021 + difference 1 4) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA1021 + difference 4 1) (sourceB1021 + difference 1 4) sourceC1021) = raw16683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16683; decide +kernel
    rw [ha]
    exact (canonical16683 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1021 + difference 4 2) (sourceB1021 + difference 2 4) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA1021 + difference 4 2) (sourceB1021 + difference 2 4) sourceC1021) = raw16684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16684; decide +kernel
    rw [ha]
    exact (canonical16684 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1021 + difference 4 3) (sourceB1021 + difference 3 4) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA1021 + difference 4 3) (sourceB1021 + difference 3 4) sourceC1021) = raw16685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16685; decide +kernel
    rw [ha]
    exact (canonical16685 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1021 + difference 4 5) (sourceB1021 + difference 5 4) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1021 + difference 4 5) (sourceB1021 + difference 5 4) sourceC1021) = raw16686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16686; decide +kernel
    rw [ha]
    exact (canonical16686 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1021 + difference 5 0) (sourceB1021 + difference 0 5) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA1021 + difference 5 0) (sourceB1021 + difference 0 5) sourceC1021) = raw16687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16687; decide +kernel
    rw [ha]
    exact (canonical16687 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1021 + difference 5 1) (sourceB1021 + difference 1 5) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA1021 + difference 5 1) (sourceB1021 + difference 1 5) sourceC1021) = raw16688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16688; decide +kernel
    rw [ha]
    exact (canonical16688 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1021 + difference 5 2) (sourceB1021 + difference 2 5) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA1021 + difference 5 2) (sourceB1021 + difference 2 5) sourceC1021) = raw16689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16689; decide +kernel
    rw [ha]
    exact (canonical16689 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1021 + difference 5 3) (sourceB1021 + difference 3 5) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA1021 + difference 5 3) (sourceB1021 + difference 3 5) sourceC1021) = raw16690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16690; decide +kernel
    rw [ha]
    exact (canonical16690 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1021 + difference 5 4) (sourceB1021 + difference 4 5) sourceC1021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA1021 + difference 5 4) (sourceB1021 + difference 4 5) sourceC1021) = raw16691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1021 sourceB1021 sourceC1021 difference raw16691; decide +kernel
    rw [ha]
    exact (canonical16691 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1021 sourceB1021 sourceC1021
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1021, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1022 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1022 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceC1022 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceForm1022 : Integer.Sparse Master := [(Sum.inr 2250, 1), (Sum.inr 2251, 1), (Sum.inr 2253, 1), (Sum.inr 2259, 1), (Sum.inr 2274, 1), (Sum.inr 3463, 1), (Sum.inr 3478, 1), (Sum.inr 3479, 1), (Sum.inr 3540, 1), (Sum.inr 3761, 1), (Sum.inr 3770, 1), (Sum.inr 3771, 1), (Sum.inr 3795, 1), (Sum.inr 3796, 1), (Sum.inr 3800, 1), (Sum.inr 3802, 1), (Sum.inr 3803, 1), (Sum.inr 3807, 1), (Sum.inr 3808, 1), (Sum.inr 3811, 1), (Sum.inr 3814, 1), (Sum.inr 3840, 1), (Sum.inr 3852, 1), (Sum.inr 3854, 1), (Sum.inr 3856, 1), (Sum.inr 3880, 1), (Sum.inr 3881, 1), (Sum.inr 3883, 1), (Sum.inr 3884, 1), (Sum.inr 3981, 1)]

theorem sourceEq1022 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1022 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1022 + difference 0 1) (sourceB1022 + difference 1 0) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA1022 + difference 0 1) (sourceB1022 + difference 1 0) sourceC1022) = raw16692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16692; decide +kernel
    rw [ha]
    exact (canonical16692 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1022 + difference 0 2) (sourceB1022 + difference 2 0) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA1022 + difference 0 2) (sourceB1022 + difference 2 0) sourceC1022) = raw16693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16693; decide +kernel
    rw [ha]
    exact (canonical16693 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1022 + difference 0 3) (sourceB1022 + difference 3 0) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA1022 + difference 0 3) (sourceB1022 + difference 3 0) sourceC1022) = raw16694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16694; decide +kernel
    rw [ha]
    exact (canonical16694 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1022 + difference 0 4) (sourceB1022 + difference 4 0) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1022 + difference 0 4) (sourceB1022 + difference 4 0) sourceC1022) = raw16695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16695; decide +kernel
    rw [ha]
    exact (canonical16695 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1022 + difference 0 5) (sourceB1022 + difference 5 0) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1022 + difference 0 5) (sourceB1022 + difference 5 0) sourceC1022) = raw16696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16696; decide +kernel
    rw [ha]
    exact (canonical16696 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1022 + difference 1 0) (sourceB1022 + difference 0 1) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA1022 + difference 1 0) (sourceB1022 + difference 0 1) sourceC1022) = raw16697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16697; decide +kernel
    rw [ha]
    exact (canonical16697 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1022 + difference 1 2) (sourceB1022 + difference 2 1) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA1022 + difference 1 2) (sourceB1022 + difference 2 1) sourceC1022) = raw16698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16698; decide +kernel
    rw [ha]
    exact (canonical16698 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1022 + difference 1 3) (sourceB1022 + difference 3 1) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA1022 + difference 1 3) (sourceB1022 + difference 3 1) sourceC1022) = raw16699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16699; decide +kernel
    rw [ha]
    exact (canonical16699 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1022 + difference 1 4) (sourceB1022 + difference 4 1) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3856) := by
    have ha : (tripleCharges (sourceA1022 + difference 1 4) (sourceB1022 + difference 4 1) sourceC1022) = raw16700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16700; decide +kernel
    rw [ha]
    exact (canonical16700 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1022 + difference 1 5) (sourceB1022 + difference 5 1) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA1022 + difference 1 5) (sourceB1022 + difference 5 1) sourceC1022) = raw16701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16701; decide +kernel
    rw [ha]
    exact (canonical16701 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1022 + difference 2 0) (sourceB1022 + difference 0 2) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA1022 + difference 2 0) (sourceB1022 + difference 0 2) sourceC1022) = raw16702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16702; decide +kernel
    rw [ha]
    exact (canonical16702 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1022 + difference 2 1) (sourceB1022 + difference 1 2) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA1022 + difference 2 1) (sourceB1022 + difference 1 2) sourceC1022) = raw16703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16703; decide +kernel
    rw [ha]
    exact (canonical16703 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1022 + difference 2 3) (sourceB1022 + difference 3 2) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA1022 + difference 2 3) (sourceB1022 + difference 3 2) sourceC1022) = raw16704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16704; decide +kernel
    rw [ha]
    exact (canonical16704 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1022 + difference 2 4) (sourceB1022 + difference 4 2) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA1022 + difference 2 4) (sourceB1022 + difference 4 2) sourceC1022) = raw16705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16705; decide +kernel
    rw [ha]
    exact (canonical16705 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1022 + difference 2 5) (sourceB1022 + difference 5 2) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1022 + difference 2 5) (sourceB1022 + difference 5 2) sourceC1022) = raw16706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16706; decide +kernel
    rw [ha]
    exact (canonical16706 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1022 + difference 3 0) (sourceB1022 + difference 0 3) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA1022 + difference 3 0) (sourceB1022 + difference 0 3) sourceC1022) = raw16707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16707; decide +kernel
    rw [ha]
    exact (canonical16707 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1022 + difference 3 1) (sourceB1022 + difference 1 3) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA1022 + difference 3 1) (sourceB1022 + difference 1 3) sourceC1022) = raw16708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16708; decide +kernel
    rw [ha]
    exact (canonical16708 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1022 + difference 3 2) (sourceB1022 + difference 2 3) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA1022 + difference 3 2) (sourceB1022 + difference 2 3) sourceC1022) = raw16709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16709; decide +kernel
    rw [ha]
    exact (canonical16709 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1022 + difference 3 4) (sourceB1022 + difference 4 3) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA1022 + difference 3 4) (sourceB1022 + difference 4 3) sourceC1022) = raw16710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16710; decide +kernel
    rw [ha]
    exact (canonical16710 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1022 + difference 3 5) (sourceB1022 + difference 5 3) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1022 + difference 3 5) (sourceB1022 + difference 5 3) sourceC1022) = raw16711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16711; decide +kernel
    rw [ha]
    exact (canonical16711 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1022 + difference 4 0) (sourceB1022 + difference 0 4) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA1022 + difference 4 0) (sourceB1022 + difference 0 4) sourceC1022) = raw16712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16712; decide +kernel
    rw [ha]
    exact (canonical16712 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1022 + difference 4 1) (sourceB1022 + difference 1 4) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA1022 + difference 4 1) (sourceB1022 + difference 1 4) sourceC1022) = raw16713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16713; decide +kernel
    rw [ha]
    exact (canonical16713 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1022 + difference 4 2) (sourceB1022 + difference 2 4) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA1022 + difference 4 2) (sourceB1022 + difference 2 4) sourceC1022) = raw16714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16714; decide +kernel
    rw [ha]
    exact (canonical16714 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1022 + difference 4 3) (sourceB1022 + difference 3 4) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3771) := by
    have ha : (tripleCharges (sourceA1022 + difference 4 3) (sourceB1022 + difference 3 4) sourceC1022) = raw16715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16715; decide +kernel
    rw [ha]
    exact (canonical16715 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1022 + difference 4 5) (sourceB1022 + difference 5 4) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA1022 + difference 4 5) (sourceB1022 + difference 5 4) sourceC1022) = raw16716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16716; decide +kernel
    rw [ha]
    exact (canonical16716 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1022 + difference 5 0) (sourceB1022 + difference 0 5) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1022 + difference 5 0) (sourceB1022 + difference 0 5) sourceC1022) = raw16717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16717; decide +kernel
    rw [ha]
    exact (canonical16717 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1022 + difference 5 1) (sourceB1022 + difference 1 5) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA1022 + difference 5 1) (sourceB1022 + difference 1 5) sourceC1022) = raw16718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16718; decide +kernel
    rw [ha]
    exact (canonical16718 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1022 + difference 5 2) (sourceB1022 + difference 2 5) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA1022 + difference 5 2) (sourceB1022 + difference 2 5) sourceC1022) = raw16719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16719; decide +kernel
    rw [ha]
    exact (canonical16719 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1022 + difference 5 3) (sourceB1022 + difference 3 5) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3479) := by
    have ha : (tripleCharges (sourceA1022 + difference 5 3) (sourceB1022 + difference 3 5) sourceC1022) = raw16720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16720; decide +kernel
    rw [ha]
    exact (canonical16720 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1022 + difference 5 4) (sourceB1022 + difference 4 5) sourceC1022) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA1022 + difference 5 4) (sourceB1022 + difference 4 5) sourceC1022) = raw16721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1022 sourceB1022 sourceC1022 difference raw16721; decide +kernel
    rw [ha]
    exact (canonical16721 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1022 sourceB1022 sourceC1022
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1022, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1023 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceB1023 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceC1023 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1023 : Integer.Sparse Master := [(Sum.inr 5085, 1), (Sum.inr 5086, 1), (Sum.inr 5087, 1), (Sum.inr 5090, 2), (Sum.inr 5102, 1), (Sum.inr 5103, 1), (Sum.inr 5266, 1), (Sum.inr 5286, 1), (Sum.inr 5287, 1), (Sum.inr 5289, 1), (Sum.inr 5299, 1), (Sum.inr 5302, 1), (Sum.inr 5359, 1), (Sum.inr 5360, 1), (Sum.inr 5361, 1), (Sum.inr 5368, 1), (Sum.inr 5395, 1), (Sum.inr 5406, 1), (Sum.inr 5410, 1), (Sum.inr 5411, 1), (Sum.inr 5412, 1), (Sum.inr 5413, 1), (Sum.inr 5425, 1), (Sum.inr 5430, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 1), (Sum.inr 5443, 1), (Sum.inr 5446, 1), (Sum.inr 5451, 1)]

theorem sourceEq1023 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1023 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1023 + difference 0 1) (sourceB1023 + difference 1 0) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1023 + difference 0 1) (sourceB1023 + difference 1 0) sourceC1023) = raw15117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw15117; decide +kernel
    rw [ha]
    exact (canonical15117 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1023 + difference 0 2) (sourceB1023 + difference 2 0) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1023 + difference 0 2) (sourceB1023 + difference 2 0) sourceC1023) = raw16144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw16144; decide +kernel
    rw [ha]
    exact (canonical16144 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1023 + difference 0 3) (sourceB1023 + difference 3 0) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA1023 + difference 0 3) (sourceB1023 + difference 3 0) sourceC1023) = raw16325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw16325; decide +kernel
    rw [ha]
    exact (canonical16325 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1023 + difference 0 4) (sourceB1023 + difference 4 0) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1023 + difference 0 4) (sourceB1023 + difference 4 0) sourceC1023) = raw16560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw16560; decide +kernel
    rw [ha]
    exact (canonical16560 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1023 + difference 0 5) (sourceB1023 + difference 5 0) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA1023 + difference 0 5) (sourceB1023 + difference 5 0) sourceC1023) = raw16722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw16722; decide +kernel
    rw [ha]
    exact (canonical16722 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1023 + difference 1 0) (sourceB1023 + difference 0 1) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA1023 + difference 1 0) (sourceB1023 + difference 0 1) sourceC1023) = raw16723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw16723; decide +kernel
    rw [ha]
    exact (canonical16723 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1023 + difference 1 2) (sourceB1023 + difference 2 1) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA1023 + difference 1 2) (sourceB1023 + difference 2 1) sourceC1023) = raw16149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw16149; decide +kernel
    rw [ha]
    exact (canonical16149 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1023 + difference 1 3) (sourceB1023 + difference 3 1) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA1023 + difference 1 3) (sourceB1023 + difference 3 1) sourceC1023) = raw16329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw16329; decide +kernel
    rw [ha]
    exact (canonical16329 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1023 + difference 1 4) (sourceB1023 + difference 4 1) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA1023 + difference 1 4) (sourceB1023 + difference 4 1) sourceC1023) = raw16563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw16563; decide +kernel
    rw [ha]
    exact (canonical16563 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1023 + difference 1 5) (sourceB1023 + difference 5 1) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5087) := by
    have ha : (tripleCharges (sourceA1023 + difference 1 5) (sourceB1023 + difference 5 1) sourceC1023) = raw16724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw16724; decide +kernel
    rw [ha]
    exact (canonical16724 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1023 + difference 2 0) (sourceB1023 + difference 0 2) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA1023 + difference 2 0) (sourceB1023 + difference 0 2) sourceC1023) = raw15861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw15861; decide +kernel
    rw [ha]
    exact (canonical15861 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1023 + difference 2 1) (sourceB1023 + difference 1 2) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1023 + difference 2 1) (sourceB1023 + difference 1 2) sourceC1023) = raw15127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw15127; decide +kernel
    rw [ha]
    exact (canonical15127 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1023 + difference 2 3) (sourceB1023 + difference 3 2) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1023 + difference 2 3) (sourceB1023 + difference 3 2) sourceC1023) = raw15862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw15862; decide +kernel
    rw [ha]
    exact (canonical15862 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1023 + difference 2 4) (sourceB1023 + difference 4 2) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA1023 + difference 2 4) (sourceB1023 + difference 4 2) sourceC1023) = raw15671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw15671; decide +kernel
    rw [ha]
    exact (canonical15671 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1023 + difference 2 5) (sourceB1023 + difference 5 2) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA1023 + difference 2 5) (sourceB1023 + difference 5 2) sourceC1023) = raw15863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw15863; decide +kernel
    rw [ha]
    exact (canonical15863 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1023 + difference 3 0) (sourceB1023 + difference 0 3) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA1023 + difference 3 0) (sourceB1023 + difference 0 3) sourceC1023) = raw16725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw16725; decide +kernel
    rw [ha]
    exact (canonical16725 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1023 + difference 3 1) (sourceB1023 + difference 1 3) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1023 + difference 3 1) (sourceB1023 + difference 1 3) sourceC1023) = raw15132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw15132; decide +kernel
    rw [ha]
    exact (canonical15132 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1023 + difference 3 2) (sourceB1023 + difference 2 3) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA1023 + difference 3 2) (sourceB1023 + difference 2 3) sourceC1023) = raw16153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw16153; decide +kernel
    rw [ha]
    exact (canonical16153 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1023 + difference 3 4) (sourceB1023 + difference 4 3) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5361) := by
    have ha : (tripleCharges (sourceA1023 + difference 3 4) (sourceB1023 + difference 4 3) sourceC1023) = raw16566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw16566; decide +kernel
    rw [ha]
    exact (canonical16566 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1023 + difference 3 5) (sourceB1023 + difference 5 3) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA1023 + difference 3 5) (sourceB1023 + difference 5 3) sourceC1023) = raw16726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw16726; decide +kernel
    rw [ha]
    exact (canonical16726 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1023 + difference 4 0) (sourceB1023 + difference 0 4) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA1023 + difference 4 0) (sourceB1023 + difference 0 4) sourceC1023) = raw15202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw15202; decide +kernel
    rw [ha]
    exact (canonical15202 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1023 + difference 4 1) (sourceB1023 + difference 1 4) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1023 + difference 4 1) (sourceB1023 + difference 1 4) sourceC1023) = raw14714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw14714; decide +kernel
    rw [ha]
    exact (canonical14714 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1023 + difference 4 2) (sourceB1023 + difference 2 4) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1023 + difference 4 2) (sourceB1023 + difference 2 4) sourceC1023) = raw14709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw14709; decide +kernel
    rw [ha]
    exact (canonical14709 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1023 + difference 4 3) (sourceB1023 + difference 3 4) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1023 + difference 4 3) (sourceB1023 + difference 3 4) sourceC1023) = raw14979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw14979; decide +kernel
    rw [ha]
    exact (canonical14979 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1023 + difference 4 5) (sourceB1023 + difference 5 4) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA1023 + difference 4 5) (sourceB1023 + difference 5 4) sourceC1023) = raw15203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw15203; decide +kernel
    rw [ha]
    exact (canonical15203 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1023 + difference 5 0) (sourceB1023 + difference 0 5) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA1023 + difference 5 0) (sourceB1023 + difference 0 5) sourceC1023) = raw15118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw15118; decide +kernel
    rw [ha]
    exact (canonical15118 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1023 + difference 5 1) (sourceB1023 + difference 1 5) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1023 + difference 5 1) (sourceB1023 + difference 1 5) sourceC1023) = raw15210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw15210; decide +kernel
    rw [ha]
    exact (canonical15210 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1023 + difference 5 2) (sourceB1023 + difference 2 5) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1023 + difference 5 2) (sourceB1023 + difference 2 5) sourceC1023) = raw15119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw15119; decide +kernel
    rw [ha]
    exact (canonical15119 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1023 + difference 5 3) (sourceB1023 + difference 3 5) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1023 + difference 5 3) (sourceB1023 + difference 3 5) sourceC1023) = raw15120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw15120; decide +kernel
    rw [ha]
    exact (canonical15120 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1023 + difference 5 4) (sourceB1023 + difference 4 5) sourceC1023) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1023 + difference 5 4) (sourceB1023 + difference 4 5) sourceC1023) = raw15121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1023 sourceB1023 sourceC1023 difference raw15121; decide +kernel
    rw [ha]
    exact (canonical15121 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1023 sourceB1023 sourceC1023
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1023, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
