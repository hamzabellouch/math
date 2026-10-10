import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical88
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical102
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical112
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical172
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical174
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical177
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical180
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical183
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical184
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical186

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1568 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1568 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1568 : Charge := ![4, -1, -1, 0, -1, -1]
def sourceForm1568 : Integer.Sparse Master := [(Sum.inr 544, 1), (Sum.inr 704, 1), (Sum.inr 739, 1), (Sum.inr 790, 1), (Sum.inr 810, 2), (Sum.inr 4068, -1)]

theorem sourceEq1568 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1568 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1568 + difference 1 0) (sourceB1568 + difference 0 1) sourceC1568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 544) := by
    have ha : (tripleCharges (sourceA1568 + difference 1 0) (sourceB1568 + difference 0 1) sourceC1568) = raw23690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1568 sourceB1568 sourceC1568 difference raw23690; decide +kernel
    rw [ha]
    exact (canonical23690 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1568 + difference 1 1) (sourceB1568 + difference 1 1) sourceC1568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 790) := by
    have ha : (tripleCharges (sourceA1568 + difference 1 1) (sourceB1568 + difference 1 1) sourceC1568) = raw22093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1568 sourceB1568 sourceC1568 difference raw22093; decide +kernel
    rw [ha]
    exact (canonical22093 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1568 + difference 1 2) (sourceB1568 + difference 2 1) sourceC1568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 739) := by
    have ha : (tripleCharges (sourceA1568 + difference 1 2) (sourceB1568 + difference 2 1) sourceC1568) = raw23691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1568 sourceB1568 sourceC1568 difference raw23691; decide +kernel
    rw [ha]
    exact (canonical23691 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1568 + difference 1 3) (sourceB1568 + difference 3 1) sourceC1568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 704) := by
    have ha : (tripleCharges (sourceA1568 + difference 1 3) (sourceB1568 + difference 3 1) sourceC1568) = raw23692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1568 sourceB1568 sourceC1568 difference raw23692; decide +kernel
    rw [ha]
    exact (canonical23692 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1568 + difference 1 4) (sourceB1568 + difference 4 1) sourceC1568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1568 + difference 1 4) (sourceB1568 + difference 4 1) sourceC1568) = raw22090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1568 sourceB1568 sourceC1568 difference raw22090; decide +kernel
    rw [ha]
    exact (canonical22090 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1568 + difference 1 5) (sourceB1568 + difference 5 1) sourceC1568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1568 + difference 1 5) (sourceB1568 + difference 5 1) sourceC1568) = raw23693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1568 sourceB1568 sourceC1568 difference raw23693; decide +kernel
    rw [ha]
    exact (canonical23693 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1568 + sourceB1568) sourceC1568) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1568 + sourceB1568) sourceC1568) = raw22085 := by
      apply Matrix.ext; unfold doubleCharges sourceA1568 sourceB1568 sourceC1568 raw22085; decide +kernel
    rw [ha]
    exact (canonical22085 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1568 sourceB1568 sourceC1568
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1568, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1569 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1569 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1569 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceForm1569 : Integer.Sparse Master := [(Sum.inr 4069, 1), (Sum.inr 4102, 2), (Sum.inr 4110, 1), (Sum.inr 4111, 1), (Sum.inr 4130, 1), (Sum.inr 4197, 2), (Sum.inr 4204, 2), (Sum.inr 4205, 2), (Sum.inr 4221, 2), (Sum.inr 4234, 2), (Sum.inr 4242, 1), (Sum.inr 4243, 1), (Sum.inr 4264, 2), (Sum.inr 4265, 2), (Sum.inr 4269, 1), (Sum.inr 4270, 1), (Sum.inr 4283, 1), (Sum.inr 4419, 2), (Sum.inr 4491, 1), (Sum.inr 4498, 1), (Sum.inr 4499, 1)]

theorem sourceEq1569 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1569 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1569 + difference 0 1) (sourceB1569 + difference 1 0) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA1569 + difference 0 1) (sourceB1569 + difference 1 0) sourceC1569) = raw23694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23694; decide +kernel
    rw [ha]
    exact (canonical23694 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1569 + difference 0 2) (sourceB1569 + difference 2 0) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1569 + difference 0 2) (sourceB1569 + difference 2 0) sourceC1569) = raw23695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23695; decide +kernel
    rw [ha]
    exact (canonical23695 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1569 + difference 0 3) (sourceB1569 + difference 3 0) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1569 + difference 0 3) (sourceB1569 + difference 3 0) sourceC1569) = raw23696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23696; decide +kernel
    rw [ha]
    exact (canonical23696 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1569 + difference 0 4) (sourceB1569 + difference 4 0) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1569 + difference 0 4) (sourceB1569 + difference 4 0) sourceC1569) = raw23697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23697; decide +kernel
    rw [ha]
    exact (canonical23697 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1569 + difference 0 5) (sourceB1569 + difference 5 0) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1569 + difference 0 5) (sourceB1569 + difference 5 0) sourceC1569) = raw23698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23698; decide +kernel
    rw [ha]
    exact (canonical23698 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1569 + difference 1 0) (sourceB1569 + difference 0 1) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4130) := by
    have ha : (tripleCharges (sourceA1569 + difference 1 0) (sourceB1569 + difference 0 1) sourceC1569) = raw23699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23699; decide +kernel
    rw [ha]
    exact (canonical23699 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1569 + difference 1 2) (sourceB1569 + difference 2 1) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4221) := by
    have ha : (tripleCharges (sourceA1569 + difference 1 2) (sourceB1569 + difference 2 1) sourceC1569) = raw23700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23700; decide +kernel
    rw [ha]
    exact (canonical23700 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1569 + difference 1 3) (sourceB1569 + difference 3 1) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4221) := by
    have ha : (tripleCharges (sourceA1569 + difference 1 3) (sourceB1569 + difference 3 1) sourceC1569) = raw23701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23701; decide +kernel
    rw [ha]
    exact (canonical23701 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1569 + difference 1 4) (sourceB1569 + difference 4 1) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4283) := by
    have ha : (tripleCharges (sourceA1569 + difference 1 4) (sourceB1569 + difference 4 1) sourceC1569) = raw23702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23702; decide +kernel
    rw [ha]
    exact (canonical23702 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1569 + difference 1 5) (sourceB1569 + difference 5 1) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1569 + difference 1 5) (sourceB1569 + difference 5 1) sourceC1569) = raw23703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23703; decide +kernel
    rw [ha]
    exact (canonical23703 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1569 + difference 2 0) (sourceB1569 + difference 0 2) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4102) := by
    have ha : (tripleCharges (sourceA1569 + difference 2 0) (sourceB1569 + difference 0 2) sourceC1569) = raw23704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23704; decide +kernel
    rw [ha]
    exact (canonical23704 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1569 + difference 2 1) (sourceB1569 + difference 1 2) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4234) := by
    have ha : (tripleCharges (sourceA1569 + difference 2 1) (sourceB1569 + difference 1 2) sourceC1569) = raw23705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23705; decide +kernel
    rw [ha]
    exact (canonical23705 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1569 + difference 2 3) (sourceB1569 + difference 3 2) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4197) := by
    have ha : (tripleCharges (sourceA1569 + difference 2 3) (sourceB1569 + difference 3 2) sourceC1569) = raw23706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23706; decide +kernel
    rw [ha]
    exact (canonical23706 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1569 + difference 2 4) (sourceB1569 + difference 4 2) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA1569 + difference 2 4) (sourceB1569 + difference 4 2) sourceC1569) = raw23707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23707; decide +kernel
    rw [ha]
    exact (canonical23707 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1569 + difference 2 5) (sourceB1569 + difference 5 2) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1569 + difference 2 5) (sourceB1569 + difference 5 2) sourceC1569) = raw23708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23708; decide +kernel
    rw [ha]
    exact (canonical23708 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1569 + difference 3 0) (sourceB1569 + difference 0 3) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4102) := by
    have ha : (tripleCharges (sourceA1569 + difference 3 0) (sourceB1569 + difference 0 3) sourceC1569) = raw23709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23709; decide +kernel
    rw [ha]
    exact (canonical23709 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1569 + difference 3 1) (sourceB1569 + difference 1 3) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4234) := by
    have ha : (tripleCharges (sourceA1569 + difference 3 1) (sourceB1569 + difference 1 3) sourceC1569) = raw23710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23710; decide +kernel
    rw [ha]
    exact (canonical23710 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1569 + difference 3 2) (sourceB1569 + difference 2 3) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4197) := by
    have ha : (tripleCharges (sourceA1569 + difference 3 2) (sourceB1569 + difference 2 3) sourceC1569) = raw23711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23711; decide +kernel
    rw [ha]
    exact (canonical23711 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1569 + difference 3 4) (sourceB1569 + difference 4 3) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA1569 + difference 3 4) (sourceB1569 + difference 4 3) sourceC1569) = raw23712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23712; decide +kernel
    rw [ha]
    exact (canonical23712 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1569 + difference 3 5) (sourceB1569 + difference 5 3) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1569 + difference 3 5) (sourceB1569 + difference 5 3) sourceC1569) = raw23713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23713; decide +kernel
    rw [ha]
    exact (canonical23713 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1569 + difference 4 0) (sourceB1569 + difference 0 4) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4110) := by
    have ha : (tripleCharges (sourceA1569 + difference 4 0) (sourceB1569 + difference 0 4) sourceC1569) = raw23714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23714; decide +kernel
    rw [ha]
    exact (canonical23714 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1569 + difference 4 1) (sourceB1569 + difference 1 4) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4242) := by
    have ha : (tripleCharges (sourceA1569 + difference 4 1) (sourceB1569 + difference 1 4) sourceC1569) = raw23715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23715; decide +kernel
    rw [ha]
    exact (canonical23715 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1569 + difference 4 2) (sourceB1569 + difference 2 4) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4204) := by
    have ha : (tripleCharges (sourceA1569 + difference 4 2) (sourceB1569 + difference 2 4) sourceC1569) = raw23716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23716; decide +kernel
    rw [ha]
    exact (canonical23716 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1569 + difference 4 3) (sourceB1569 + difference 3 4) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4204) := by
    have ha : (tripleCharges (sourceA1569 + difference 4 3) (sourceB1569 + difference 3 4) sourceC1569) = raw23717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23717; decide +kernel
    rw [ha]
    exact (canonical23717 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1569 + difference 4 5) (sourceB1569 + difference 5 4) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1569 + difference 4 5) (sourceB1569 + difference 5 4) sourceC1569) = raw23718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23718; decide +kernel
    rw [ha]
    exact (canonical23718 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1569 + difference 5 0) (sourceB1569 + difference 0 5) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4111) := by
    have ha : (tripleCharges (sourceA1569 + difference 5 0) (sourceB1569 + difference 0 5) sourceC1569) = raw23719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23719; decide +kernel
    rw [ha]
    exact (canonical23719 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1569 + difference 5 1) (sourceB1569 + difference 1 5) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4243) := by
    have ha : (tripleCharges (sourceA1569 + difference 5 1) (sourceB1569 + difference 1 5) sourceC1569) = raw23720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23720; decide +kernel
    rw [ha]
    exact (canonical23720 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1569 + difference 5 2) (sourceB1569 + difference 2 5) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4205) := by
    have ha : (tripleCharges (sourceA1569 + difference 5 2) (sourceB1569 + difference 2 5) sourceC1569) = raw23721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23721; decide +kernel
    rw [ha]
    exact (canonical23721 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1569 + difference 5 3) (sourceB1569 + difference 3 5) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4205) := by
    have ha : (tripleCharges (sourceA1569 + difference 5 3) (sourceB1569 + difference 3 5) sourceC1569) = raw23722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23722; decide +kernel
    rw [ha]
    exact (canonical23722 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1569 + difference 5 4) (sourceB1569 + difference 4 5) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1569 + difference 5 4) (sourceB1569 + difference 4 5) sourceC1569) = raw23723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23723; decide +kernel
    rw [ha]
    exact (canonical23723 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1569 sourceB1569 sourceC1569
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1569, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1570 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1570 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1570 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceForm1570 : Integer.Sparse Master := [(Sum.inr 664, 2), (Sum.inr 684, 1), (Sum.inr 685, 1), (Sum.inr 689, 1), (Sum.inr 749, 2), (Sum.inr 763, 2), (Sum.inr 764, 2), (Sum.inr 768, 2), (Sum.inr 800, 2), (Sum.inr 806, 2), (Sum.inr 807, 2), (Sum.inr 843, 1), (Sum.inr 844, 1), (Sum.inr 851, 1), (Sum.inr 853, 1), (Sum.inr 856, 1), (Sum.inr 1000, 2), (Sum.inr 1075, 1), (Sum.inr 1082, 1), (Sum.inr 1083, 1), (Sum.inr 4069, 1)]

theorem sourceEq1570 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1570 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1570 + difference 0 1) (sourceB1570 + difference 1 0) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1075) := by
    have ha : (tripleCharges (sourceA1570 + difference 0 1) (sourceB1570 + difference 1 0) sourceC1570) = raw23724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23724; decide +kernel
    rw [ha]
    exact (canonical23724 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1570 + difference 0 2) (sourceB1570 + difference 2 0) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1570 + difference 0 2) (sourceB1570 + difference 2 0) sourceC1570) = raw23725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23725; decide +kernel
    rw [ha]
    exact (canonical23725 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1570 + difference 0 3) (sourceB1570 + difference 3 0) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1570 + difference 0 3) (sourceB1570 + difference 3 0) sourceC1570) = raw23726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23726; decide +kernel
    rw [ha]
    exact (canonical23726 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1570 + difference 0 4) (sourceB1570 + difference 4 0) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1570 + difference 0 4) (sourceB1570 + difference 4 0) sourceC1570) = raw23727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23727; decide +kernel
    rw [ha]
    exact (canonical23727 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1570 + difference 0 5) (sourceB1570 + difference 5 0) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1082) := by
    have ha : (tripleCharges (sourceA1570 + difference 0 5) (sourceB1570 + difference 5 0) sourceC1570) = raw23728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23728; decide +kernel
    rw [ha]
    exact (canonical23728 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1570 + difference 1 0) (sourceB1570 + difference 0 1) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 689) := by
    have ha : (tripleCharges (sourceA1570 + difference 1 0) (sourceB1570 + difference 0 1) sourceC1570) = raw23729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23729; decide +kernel
    rw [ha]
    exact (canonical23729 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1570 + difference 1 2) (sourceB1570 + difference 2 1) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 768) := by
    have ha : (tripleCharges (sourceA1570 + difference 1 2) (sourceB1570 + difference 2 1) sourceC1570) = raw23730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23730; decide +kernel
    rw [ha]
    exact (canonical23730 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1570 + difference 1 3) (sourceB1570 + difference 3 1) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 768) := by
    have ha : (tripleCharges (sourceA1570 + difference 1 3) (sourceB1570 + difference 3 1) sourceC1570) = raw23731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23731; decide +kernel
    rw [ha]
    exact (canonical23731 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1570 + difference 1 4) (sourceB1570 + difference 4 1) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 856) := by
    have ha : (tripleCharges (sourceA1570 + difference 1 4) (sourceB1570 + difference 4 1) sourceC1570) = raw23732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23732; decide +kernel
    rw [ha]
    exact (canonical23732 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1570 + difference 1 5) (sourceB1570 + difference 5 1) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1570 + difference 1 5) (sourceB1570 + difference 5 1) sourceC1570) = raw23733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23733; decide +kernel
    rw [ha]
    exact (canonical23733 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1570 + difference 2 0) (sourceB1570 + difference 0 2) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 664) := by
    have ha : (tripleCharges (sourceA1570 + difference 2 0) (sourceB1570 + difference 0 2) sourceC1570) = raw23734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23734; decide +kernel
    rw [ha]
    exact (canonical23734 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1570 + difference 2 1) (sourceB1570 + difference 1 2) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 800) := by
    have ha : (tripleCharges (sourceA1570 + difference 2 1) (sourceB1570 + difference 1 2) sourceC1570) = raw23735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23735; decide +kernel
    rw [ha]
    exact (canonical23735 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1570 + difference 2 3) (sourceB1570 + difference 3 2) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 749) := by
    have ha : (tripleCharges (sourceA1570 + difference 2 3) (sourceB1570 + difference 3 2) sourceC1570) = raw23736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23736; decide +kernel
    rw [ha]
    exact (canonical23736 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1570 + difference 2 4) (sourceB1570 + difference 4 2) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 807) := by
    have ha : (tripleCharges (sourceA1570 + difference 2 4) (sourceB1570 + difference 4 2) sourceC1570) = raw23737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23737; decide +kernel
    rw [ha]
    exact (canonical23737 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1570 + difference 2 5) (sourceB1570 + difference 5 2) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1570 + difference 2 5) (sourceB1570 + difference 5 2) sourceC1570) = raw23738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23738; decide +kernel
    rw [ha]
    exact (canonical23738 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1570 + difference 3 0) (sourceB1570 + difference 0 3) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 664) := by
    have ha : (tripleCharges (sourceA1570 + difference 3 0) (sourceB1570 + difference 0 3) sourceC1570) = raw23739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23739; decide +kernel
    rw [ha]
    exact (canonical23739 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1570 + difference 3 1) (sourceB1570 + difference 1 3) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 800) := by
    have ha : (tripleCharges (sourceA1570 + difference 3 1) (sourceB1570 + difference 1 3) sourceC1570) = raw23740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23740; decide +kernel
    rw [ha]
    exact (canonical23740 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1570 + difference 3 2) (sourceB1570 + difference 2 3) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 749) := by
    have ha : (tripleCharges (sourceA1570 + difference 3 2) (sourceB1570 + difference 2 3) sourceC1570) = raw23741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23741; decide +kernel
    rw [ha]
    exact (canonical23741 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1570 + difference 3 4) (sourceB1570 + difference 4 3) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 807) := by
    have ha : (tripleCharges (sourceA1570 + difference 3 4) (sourceB1570 + difference 4 3) sourceC1570) = raw23742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23742; decide +kernel
    rw [ha]
    exact (canonical23742 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1570 + difference 3 5) (sourceB1570 + difference 5 3) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1570 + difference 3 5) (sourceB1570 + difference 5 3) sourceC1570) = raw23743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23743; decide +kernel
    rw [ha]
    exact (canonical23743 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1570 + difference 4 0) (sourceB1570 + difference 0 4) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 684) := by
    have ha : (tripleCharges (sourceA1570 + difference 4 0) (sourceB1570 + difference 0 4) sourceC1570) = raw23744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23744; decide +kernel
    rw [ha]
    exact (canonical23744 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1570 + difference 4 1) (sourceB1570 + difference 1 4) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 843) := by
    have ha : (tripleCharges (sourceA1570 + difference 4 1) (sourceB1570 + difference 1 4) sourceC1570) = raw23745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23745; decide +kernel
    rw [ha]
    exact (canonical23745 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1570 + difference 4 2) (sourceB1570 + difference 2 4) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 763) := by
    have ha : (tripleCharges (sourceA1570 + difference 4 2) (sourceB1570 + difference 2 4) sourceC1570) = raw23746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23746; decide +kernel
    rw [ha]
    exact (canonical23746 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1570 + difference 4 3) (sourceB1570 + difference 3 4) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 763) := by
    have ha : (tripleCharges (sourceA1570 + difference 4 3) (sourceB1570 + difference 3 4) sourceC1570) = raw23747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23747; decide +kernel
    rw [ha]
    exact (canonical23747 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1570 + difference 4 5) (sourceB1570 + difference 5 4) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 851) := by
    have ha : (tripleCharges (sourceA1570 + difference 4 5) (sourceB1570 + difference 5 4) sourceC1570) = raw23748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23748; decide +kernel
    rw [ha]
    exact (canonical23748 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1570 + difference 5 0) (sourceB1570 + difference 0 5) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 685) := by
    have ha : (tripleCharges (sourceA1570 + difference 5 0) (sourceB1570 + difference 0 5) sourceC1570) = raw23749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23749; decide +kernel
    rw [ha]
    exact (canonical23749 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1570 + difference 5 1) (sourceB1570 + difference 1 5) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 844) := by
    have ha : (tripleCharges (sourceA1570 + difference 5 1) (sourceB1570 + difference 1 5) sourceC1570) = raw23750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23750; decide +kernel
    rw [ha]
    exact (canonical23750 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1570 + difference 5 2) (sourceB1570 + difference 2 5) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 764) := by
    have ha : (tripleCharges (sourceA1570 + difference 5 2) (sourceB1570 + difference 2 5) sourceC1570) = raw23751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23751; decide +kernel
    rw [ha]
    exact (canonical23751 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1570 + difference 5 3) (sourceB1570 + difference 3 5) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 764) := by
    have ha : (tripleCharges (sourceA1570 + difference 5 3) (sourceB1570 + difference 3 5) sourceC1570) = raw23752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23752; decide +kernel
    rw [ha]
    exact (canonical23752 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1570 + difference 5 4) (sourceB1570 + difference 4 5) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 853) := by
    have ha : (tripleCharges (sourceA1570 + difference 5 4) (sourceB1570 + difference 4 5) sourceC1570) = raw23753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23753; decide +kernel
    rw [ha]
    exact (canonical23753 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1570 sourceB1570 sourceC1570
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1570, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1571 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1571 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1571 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceForm1571 : Integer.Sparse Master := [(Sum.inr 816, 1), (Sum.inr 1605, 2), (Sum.inr 1653, 1), (Sum.inr 1727, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

theorem sourceEq1571 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1571 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1571 + difference 0 0) (sourceB1571 + difference 0 0) sourceC1571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 816) := by
    have ha : (tripleCharges (sourceA1571 + difference 0 0) (sourceB1571 + difference 0 0) sourceC1571) = raw22125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1571 sourceB1571 sourceC1571 difference raw22125; decide +kernel
    rw [ha]
    exact (canonical22125 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1571 + difference 0 1) (sourceB1571 + difference 1 0) sourceC1571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1653) := by
    have ha : (tripleCharges (sourceA1571 + difference 0 1) (sourceB1571 + difference 1 0) sourceC1571) = raw23754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1571 sourceB1571 sourceC1571 difference raw23754; decide +kernel
    rw [ha]
    exact (canonical23754 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1571 + difference 0 2) (sourceB1571 + difference 2 0) sourceC1571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1605) := by
    have ha : (tripleCharges (sourceA1571 + difference 0 2) (sourceB1571 + difference 2 0) sourceC1571) = raw23755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1571 sourceB1571 sourceC1571 difference raw23755; decide +kernel
    rw [ha]
    exact (canonical23755 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1571 + difference 0 3) (sourceB1571 + difference 3 0) sourceC1571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1605) := by
    have ha : (tripleCharges (sourceA1571 + difference 0 3) (sourceB1571 + difference 3 0) sourceC1571) = raw23756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1571 sourceB1571 sourceC1571 difference raw23756; decide +kernel
    rw [ha]
    exact (canonical23756 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1571 + difference 0 4) (sourceB1571 + difference 4 0) sourceC1571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1571 + difference 0 4) (sourceB1571 + difference 4 0) sourceC1571) = raw22119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1571 sourceB1571 sourceC1571 difference raw22119; decide +kernel
    rw [ha]
    exact (canonical22119 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1571 + difference 0 5) (sourceB1571 + difference 5 0) sourceC1571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1571 + difference 0 5) (sourceB1571 + difference 5 0) sourceC1571) = raw23757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1571 sourceB1571 sourceC1571 difference raw23757; decide +kernel
    rw [ha]
    exact (canonical23757 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1571 + sourceB1571) sourceC1571) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1571 + sourceB1571) sourceC1571) = raw22120 := by
      apply Matrix.ext; unfold doubleCharges sourceA1571 sourceB1571 sourceC1571 raw22120; decide +kernel
    rw [ha]
    exact (canonical22120 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1571 sourceB1571 sourceC1571
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1571, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1572 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1572 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1572 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceForm1572 : Integer.Sparse Master := [(Sum.inr 539, 2), (Sum.inr 547, 1), (Sum.inr 548, 1), (Sum.inr 561, 1), (Sum.inr 816, 1), (Sum.inr 4069, -1)]

theorem sourceEq1572 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1572 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1572 + difference 0 0) (sourceB1572 + difference 0 0) sourceC1572) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 816) := by
    have ha : (tripleCharges (sourceA1572 + difference 0 0) (sourceB1572 + difference 0 0) sourceC1572) = raw22125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1572 sourceB1572 sourceC1572 difference raw22125; decide +kernel
    rw [ha]
    exact (canonical22125 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1572 + difference 1 0) (sourceB1572 + difference 0 1) sourceC1572) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 561) := by
    have ha : (tripleCharges (sourceA1572 + difference 1 0) (sourceB1572 + difference 0 1) sourceC1572) = raw23758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1572 sourceB1572 sourceC1572 difference raw23758; decide +kernel
    rw [ha]
    exact (canonical23758 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1572 + difference 2 0) (sourceB1572 + difference 0 2) sourceC1572) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 539) := by
    have ha : (tripleCharges (sourceA1572 + difference 2 0) (sourceB1572 + difference 0 2) sourceC1572) = raw23759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1572 sourceB1572 sourceC1572 difference raw23759; decide +kernel
    rw [ha]
    exact (canonical23759 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1572 + difference 3 0) (sourceB1572 + difference 0 3) sourceC1572) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 539) := by
    have ha : (tripleCharges (sourceA1572 + difference 3 0) (sourceB1572 + difference 0 3) sourceC1572) = raw23760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1572 sourceB1572 sourceC1572 difference raw23760; decide +kernel
    rw [ha]
    exact (canonical23760 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1572 + difference 4 0) (sourceB1572 + difference 0 4) sourceC1572) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 547) := by
    have ha : (tripleCharges (sourceA1572 + difference 4 0) (sourceB1572 + difference 0 4) sourceC1572) = raw23761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1572 sourceB1572 sourceC1572 difference raw23761; decide +kernel
    rw [ha]
    exact (canonical23761 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1572 + difference 5 0) (sourceB1572 + difference 0 5) sourceC1572) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 548) := by
    have ha : (tripleCharges (sourceA1572 + difference 5 0) (sourceB1572 + difference 0 5) sourceC1572) = raw22121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1572 sourceB1572 sourceC1572 difference raw22121; decide +kernel
    rw [ha]
    exact (canonical22121 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1572 + sourceB1572) sourceC1572) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1572 + sourceB1572) sourceC1572) = raw22120 := by
      apply Matrix.ext; unfold doubleCharges sourceA1572 sourceB1572 sourceC1572 raw22120; decide +kernel
    rw [ha]
    exact (canonical22120 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1572 sourceB1572 sourceC1572
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1572, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1573 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1573 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1573 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceForm1573 : Integer.Sparse Master := [(Sum.inr 734, 2), (Sum.inr 742, 1), (Sum.inr 743, 1), (Sum.inr 816, 1), (Sum.inr 1653, 1), (Sum.inr 4069, -1)]

theorem sourceEq1573 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1573 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1573 + difference 0 1) (sourceB1573 + difference 1 0) sourceC1573) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1653) := by
    have ha : (tripleCharges (sourceA1573 + difference 0 1) (sourceB1573 + difference 1 0) sourceC1573) = raw23754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1573 sourceB1573 sourceC1573 difference raw23754; decide +kernel
    rw [ha]
    exact (canonical23754 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1573 + difference 1 1) (sourceB1573 + difference 1 1) sourceC1573) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 816) := by
    have ha : (tripleCharges (sourceA1573 + difference 1 1) (sourceB1573 + difference 1 1) sourceC1573) = raw22125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1573 sourceB1573 sourceC1573 difference raw22125; decide +kernel
    rw [ha]
    exact (canonical22125 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1573 + difference 2 1) (sourceB1573 + difference 1 2) sourceC1573) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 734) := by
    have ha : (tripleCharges (sourceA1573 + difference 2 1) (sourceB1573 + difference 1 2) sourceC1573) = raw23762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1573 sourceB1573 sourceC1573 difference raw23762; decide +kernel
    rw [ha]
    exact (canonical23762 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1573 + difference 3 1) (sourceB1573 + difference 1 3) sourceC1573) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 734) := by
    have ha : (tripleCharges (sourceA1573 + difference 3 1) (sourceB1573 + difference 1 3) sourceC1573) = raw23763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1573 sourceB1573 sourceC1573 difference raw23763; decide +kernel
    rw [ha]
    exact (canonical23763 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1573 + difference 4 1) (sourceB1573 + difference 1 4) sourceC1573) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 742) := by
    have ha : (tripleCharges (sourceA1573 + difference 4 1) (sourceB1573 + difference 1 4) sourceC1573) = raw23764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1573 sourceB1573 sourceC1573 difference raw23764; decide +kernel
    rw [ha]
    exact (canonical23764 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1573 + difference 5 1) (sourceB1573 + difference 1 5) sourceC1573) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 743) := by
    have ha : (tripleCharges (sourceA1573 + difference 5 1) (sourceB1573 + difference 1 5) sourceC1573) = raw22122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1573 sourceB1573 sourceC1573 difference raw22122; decide +kernel
    rw [ha]
    exact (canonical22122 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1573 + sourceB1573) sourceC1573) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1573 + sourceB1573) sourceC1573) = raw22120 := by
      apply Matrix.ext; unfold doubleCharges sourceA1573 sourceB1573 sourceC1573 raw22120; decide +kernel
    rw [ha]
    exact (canonical22120 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1573 sourceB1573 sourceC1573
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1573, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1574 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceB1574 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceC1574 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1574 : Integer.Sparse Master := [(Sum.inr 4071, 1), (Sum.inr 4115, 2), (Sum.inr 4121, 1), (Sum.inr 4123, 1), (Sum.inr 4132, 1), (Sum.inr 4207, 2), (Sum.inr 4212, 2), (Sum.inr 4214, 2), (Sum.inr 4223, 2), (Sum.inr 4255, 2), (Sum.inr 4256, 2), (Sum.inr 4272, 1), (Sum.inr 4273, 3), (Sum.inr 4278, 1), (Sum.inr 4279, 1), (Sum.inr 4284, 1), (Sum.inr 4404, 2), (Sum.inr 4466, 1), (Sum.inr 4467, 1), (Sum.inr 4511, 1)]

theorem sourceEq1574 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1574 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1574 + difference 0 1) (sourceB1574 + difference 1 0) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1574 + difference 0 1) (sourceB1574 + difference 1 0) sourceC1574) = raw22623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw22623; decide +kernel
    rw [ha]
    exact (canonical22623 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1574 + difference 0 2) (sourceB1574 + difference 2 0) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1574 + difference 0 2) (sourceB1574 + difference 2 0) sourceC1574) = raw23098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23098; decide +kernel
    rw [ha]
    exact (canonical23098 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1574 + difference 0 3) (sourceB1574 + difference 3 0) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1574 + difference 0 3) (sourceB1574 + difference 3 0) sourceC1574) = raw22775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw22775; decide +kernel
    rw [ha]
    exact (canonical22775 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1574 + difference 0 4) (sourceB1574 + difference 4 0) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1574 + difference 0 4) (sourceB1574 + difference 4 0) sourceC1574) = raw22611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw22611; decide +kernel
    rw [ha]
    exact (canonical22611 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1574 + difference 0 5) (sourceB1574 + difference 5 0) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1574 + difference 0 5) (sourceB1574 + difference 5 0) sourceC1574) = raw23270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23270; decide +kernel
    rw [ha]
    exact (canonical23270 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1574 + difference 1 0) (sourceB1574 + difference 0 1) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4132) := by
    have ha : (tripleCharges (sourceA1574 + difference 1 0) (sourceB1574 + difference 0 1) sourceC1574) = raw23765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23765; decide +kernel
    rw [ha]
    exact (canonical23765 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1574 + difference 1 2) (sourceB1574 + difference 2 1) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4223) := by
    have ha : (tripleCharges (sourceA1574 + difference 1 2) (sourceB1574 + difference 2 1) sourceC1574) = raw23766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23766; decide +kernel
    rw [ha]
    exact (canonical23766 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1574 + difference 1 3) (sourceB1574 + difference 3 1) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4223) := by
    have ha : (tripleCharges (sourceA1574 + difference 1 3) (sourceB1574 + difference 3 1) sourceC1574) = raw23767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23767; decide +kernel
    rw [ha]
    exact (canonical23767 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1574 + difference 1 4) (sourceB1574 + difference 4 1) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4279) := by
    have ha : (tripleCharges (sourceA1574 + difference 1 4) (sourceB1574 + difference 4 1) sourceC1574) = raw23260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23260; decide +kernel
    rw [ha]
    exact (canonical23260 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1574 + difference 1 5) (sourceB1574 + difference 5 1) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4278) := by
    have ha : (tripleCharges (sourceA1574 + difference 1 5) (sourceB1574 + difference 5 1) sourceC1574) = raw23077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23077; decide +kernel
    rw [ha]
    exact (canonical23077 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1574 + difference 2 0) (sourceB1574 + difference 0 2) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4115) := by
    have ha : (tripleCharges (sourceA1574 + difference 2 0) (sourceB1574 + difference 0 2) sourceC1574) = raw23768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23768; decide +kernel
    rw [ha]
    exact (canonical23768 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1574 + difference 2 1) (sourceB1574 + difference 1 2) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1574 + difference 2 1) (sourceB1574 + difference 1 2) sourceC1574) = raw23563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23563; decide +kernel
    rw [ha]
    exact (canonical23563 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1574 + difference 2 3) (sourceB1574 + difference 3 2) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4207) := by
    have ha : (tripleCharges (sourceA1574 + difference 2 3) (sourceB1574 + difference 3 2) sourceC1574) = raw23769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23769; decide +kernel
    rw [ha]
    exact (canonical23769 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1574 + difference 2 4) (sourceB1574 + difference 4 2) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4256) := by
    have ha : (tripleCharges (sourceA1574 + difference 2 4) (sourceB1574 + difference 4 2) sourceC1574) = raw23264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23264; decide +kernel
    rw [ha]
    exact (canonical23264 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1574 + difference 2 5) (sourceB1574 + difference 5 2) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4255) := by
    have ha : (tripleCharges (sourceA1574 + difference 2 5) (sourceB1574 + difference 5 2) sourceC1574) = raw23082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23082; decide +kernel
    rw [ha]
    exact (canonical23082 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1574 + difference 3 0) (sourceB1574 + difference 0 3) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4115) := by
    have ha : (tripleCharges (sourceA1574 + difference 3 0) (sourceB1574 + difference 0 3) sourceC1574) = raw23770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23770; decide +kernel
    rw [ha]
    exact (canonical23770 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1574 + difference 3 1) (sourceB1574 + difference 1 3) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1574 + difference 3 1) (sourceB1574 + difference 1 3) sourceC1574) = raw23565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23565; decide +kernel
    rw [ha]
    exact (canonical23565 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1574 + difference 3 2) (sourceB1574 + difference 2 3) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4207) := by
    have ha : (tripleCharges (sourceA1574 + difference 3 2) (sourceB1574 + difference 2 3) sourceC1574) = raw23771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23771; decide +kernel
    rw [ha]
    exact (canonical23771 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1574 + difference 3 4) (sourceB1574 + difference 4 3) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4256) := by
    have ha : (tripleCharges (sourceA1574 + difference 3 4) (sourceB1574 + difference 4 3) sourceC1574) = raw23267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23267; decide +kernel
    rw [ha]
    exact (canonical23267 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1574 + difference 3 5) (sourceB1574 + difference 5 3) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4255) := by
    have ha : (tripleCharges (sourceA1574 + difference 3 5) (sourceB1574 + difference 5 3) sourceC1574) = raw23087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23087; decide +kernel
    rw [ha]
    exact (canonical23087 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1574 + difference 4 0) (sourceB1574 + difference 0 4) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4121) := by
    have ha : (tripleCharges (sourceA1574 + difference 4 0) (sourceB1574 + difference 0 4) sourceC1574) = raw23772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23772; decide +kernel
    rw [ha]
    exact (canonical23772 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1574 + difference 4 1) (sourceB1574 + difference 1 4) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4284) := by
    have ha : (tripleCharges (sourceA1574 + difference 4 1) (sourceB1574 + difference 1 4) sourceC1574) = raw23477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23477; decide +kernel
    rw [ha]
    exact (canonical23477 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1574 + difference 4 2) (sourceB1574 + difference 2 4) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4212) := by
    have ha : (tripleCharges (sourceA1574 + difference 4 2) (sourceB1574 + difference 2 4) sourceC1574) = raw23773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23773; decide +kernel
    rw [ha]
    exact (canonical23773 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1574 + difference 4 3) (sourceB1574 + difference 3 4) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4212) := by
    have ha : (tripleCharges (sourceA1574 + difference 4 3) (sourceB1574 + difference 3 4) sourceC1574) = raw23774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23774; decide +kernel
    rw [ha]
    exact (canonical23774 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1574 + difference 4 5) (sourceB1574 + difference 5 4) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA1574 + difference 4 5) (sourceB1574 + difference 5 4) sourceC1574) = raw23092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23092; decide +kernel
    rw [ha]
    exact (canonical23092 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1574 + difference 5 0) (sourceB1574 + difference 0 5) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4123) := by
    have ha : (tripleCharges (sourceA1574 + difference 5 0) (sourceB1574 + difference 0 5) sourceC1574) = raw23775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23775; decide +kernel
    rw [ha]
    exact (canonical23775 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1574 + difference 5 1) (sourceB1574 + difference 1 5) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (tripleCharges (sourceA1574 + difference 5 1) (sourceB1574 + difference 1 5) sourceC1574) = raw23568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23568; decide +kernel
    rw [ha]
    exact (canonical23568 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1574 + difference 5 2) (sourceB1574 + difference 2 5) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4214) := by
    have ha : (tripleCharges (sourceA1574 + difference 5 2) (sourceB1574 + difference 2 5) sourceC1574) = raw23776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23776; decide +kernel
    rw [ha]
    exact (canonical23776 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1574 + difference 5 3) (sourceB1574 + difference 3 5) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4214) := by
    have ha : (tripleCharges (sourceA1574 + difference 5 3) (sourceB1574 + difference 3 5) sourceC1574) = raw23646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23646; decide +kernel
    rw [ha]
    exact (canonical23646 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1574 + difference 5 4) (sourceB1574 + difference 4 5) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1574 + difference 5 4) (sourceB1574 + difference 4 5) sourceC1574) = raw23271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23271; decide +kernel
    rw [ha]
    exact (canonical23271 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1574 sourceB1574 sourceC1574
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1574, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1575 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1575 : Charge := ![4, 0, 0, 0, -2, -2]
def sourceC1575 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm1575 : Integer.Sparse Master := [(Sum.inr 4059, 3), (Sum.inr 4061, 2), (Sum.inr 4065, 6), (Sum.inr 4067, 6), (Sum.inr 4069, 6), (Sum.inr 4070, 2), (Sum.inr 4082, 3), (Sum.inr 4084, 2)]

theorem sourceEq1575 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1575 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1575 + difference 0 1) (sourceB1575 + difference 1 0) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA1575 + difference 0 1) (sourceB1575 + difference 1 0) sourceC1575) = raw11541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw11541; decide +kernel
    rw [ha]
    exact (canonical11541 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1575 + difference 0 2) (sourceB1575 + difference 2 0) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA1575 + difference 0 2) (sourceB1575 + difference 2 0) sourceC1575) = raw11542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw11542; decide +kernel
    rw [ha]
    exact (canonical11542 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1575 + difference 0 3) (sourceB1575 + difference 3 0) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA1575 + difference 0 3) (sourceB1575 + difference 3 0) sourceC1575) = raw11543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw11543; decide +kernel
    rw [ha]
    exact (canonical11543 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1575 + difference 0 4) (sourceB1575 + difference 4 0) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1575 + difference 0 4) (sourceB1575 + difference 4 0) sourceC1575) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1575 + difference 0 5) (sourceB1575 + difference 5 0) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1575 + difference 0 5) (sourceB1575 + difference 5 0) sourceC1575) = raw3335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw3335; decide +kernel
    rw [ha]
    exact (canonical3335 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1575 + difference 1 0) (sourceB1575 + difference 0 1) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (tripleCharges (sourceA1575 + difference 1 0) (sourceB1575 + difference 0 1) sourceC1575) = raw23777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23777; decide +kernel
    rw [ha]
    exact (canonical23777 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1575 + difference 1 2) (sourceB1575 + difference 2 1) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1575 + difference 1 2) (sourceB1575 + difference 2 1) sourceC1575) = raw23778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23778; decide +kernel
    rw [ha]
    exact (canonical23778 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1575 + difference 1 3) (sourceB1575 + difference 3 1) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1575 + difference 1 3) (sourceB1575 + difference 3 1) sourceC1575) = raw23779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23779; decide +kernel
    rw [ha]
    exact (canonical23779 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1575 + difference 1 4) (sourceB1575 + difference 4 1) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1575 + difference 1 4) (sourceB1575 + difference 4 1) sourceC1575) = raw11531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw11531; decide +kernel
    rw [ha]
    exact (canonical11531 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1575 + difference 1 5) (sourceB1575 + difference 5 1) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1575 + difference 1 5) (sourceB1575 + difference 5 1) sourceC1575) = raw23780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23780; decide +kernel
    rw [ha]
    exact (canonical23780 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1575 + difference 2 0) (sourceB1575 + difference 0 2) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (tripleCharges (sourceA1575 + difference 2 0) (sourceB1575 + difference 0 2) sourceC1575) = raw23781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23781; decide +kernel
    rw [ha]
    exact (canonical23781 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1575 + difference 2 1) (sourceB1575 + difference 1 2) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1575 + difference 2 1) (sourceB1575 + difference 1 2) sourceC1575) = raw23782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23782; decide +kernel
    rw [ha]
    exact (canonical23782 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1575 + difference 2 3) (sourceB1575 + difference 3 2) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1575 + difference 2 3) (sourceB1575 + difference 3 2) sourceC1575) = raw23783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23783; decide +kernel
    rw [ha]
    exact (canonical23783 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1575 + difference 2 4) (sourceB1575 + difference 4 2) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1575 + difference 2 4) (sourceB1575 + difference 4 2) sourceC1575) = raw11534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw11534; decide +kernel
    rw [ha]
    exact (canonical11534 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1575 + difference 2 5) (sourceB1575 + difference 5 2) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1575 + difference 2 5) (sourceB1575 + difference 5 2) sourceC1575) = raw23784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23784; decide +kernel
    rw [ha]
    exact (canonical23784 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1575 + difference 3 0) (sourceB1575 + difference 0 3) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (tripleCharges (sourceA1575 + difference 3 0) (sourceB1575 + difference 0 3) sourceC1575) = raw23785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23785; decide +kernel
    rw [ha]
    exact (canonical23785 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1575 + difference 3 1) (sourceB1575 + difference 1 3) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1575 + difference 3 1) (sourceB1575 + difference 1 3) sourceC1575) = raw23786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23786; decide +kernel
    rw [ha]
    exact (canonical23786 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1575 + difference 3 2) (sourceB1575 + difference 2 3) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1575 + difference 3 2) (sourceB1575 + difference 2 3) sourceC1575) = raw23787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23787; decide +kernel
    rw [ha]
    exact (canonical23787 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1575 + difference 3 4) (sourceB1575 + difference 4 3) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1575 + difference 3 4) (sourceB1575 + difference 4 3) sourceC1575) = raw11537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw11537; decide +kernel
    rw [ha]
    exact (canonical11537 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1575 + difference 3 5) (sourceB1575 + difference 5 3) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1575 + difference 3 5) (sourceB1575 + difference 5 3) sourceC1575) = raw14373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw14373; decide +kernel
    rw [ha]
    exact (canonical14373 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1575 + difference 4 0) (sourceB1575 + difference 0 4) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (tripleCharges (sourceA1575 + difference 4 0) (sourceB1575 + difference 0 4) sourceC1575) = raw23788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23788; decide +kernel
    rw [ha]
    exact (canonical23788 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1575 + difference 4 1) (sourceB1575 + difference 1 4) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1575 + difference 4 1) (sourceB1575 + difference 1 4) sourceC1575) = raw23789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23789; decide +kernel
    rw [ha]
    exact (canonical23789 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1575 + difference 4 2) (sourceB1575 + difference 2 4) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1575 + difference 4 2) (sourceB1575 + difference 2 4) sourceC1575) = raw23790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23790; decide +kernel
    rw [ha]
    exact (canonical23790 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1575 + difference 4 3) (sourceB1575 + difference 3 4) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1575 + difference 4 3) (sourceB1575 + difference 3 4) sourceC1575) = raw23791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23791; decide +kernel
    rw [ha]
    exact (canonical23791 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1575 + difference 4 5) (sourceB1575 + difference 5 4) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1575 + difference 4 5) (sourceB1575 + difference 5 4) sourceC1575) = raw23792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23792; decide +kernel
    rw [ha]
    exact (canonical23792 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1575 + difference 5 0) (sourceB1575 + difference 0 5) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (tripleCharges (sourceA1575 + difference 5 0) (sourceB1575 + difference 0 5) sourceC1575) = raw22310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw22310; decide +kernel
    rw [ha]
    exact (canonical22310 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1575 + difference 5 1) (sourceB1575 + difference 1 5) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1575 + difference 5 1) (sourceB1575 + difference 1 5) sourceC1575) = raw22311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw22311; decide +kernel
    rw [ha]
    exact (canonical22311 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1575 + difference 5 2) (sourceB1575 + difference 2 5) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1575 + difference 5 2) (sourceB1575 + difference 2 5) sourceC1575) = raw22312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw22312; decide +kernel
    rw [ha]
    exact (canonical22312 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1575 + difference 5 3) (sourceB1575 + difference 3 5) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1575 + difference 5 3) (sourceB1575 + difference 3 5) sourceC1575) = raw22313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw22313; decide +kernel
    rw [ha]
    exact (canonical22313 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1575 + difference 5 4) (sourceB1575 + difference 4 5) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1575 + difference 5 4) (sourceB1575 + difference 4 5) sourceC1575) = raw5209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw5209; decide +kernel
    rw [ha]
    exact (canonical5209 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1575 sourceB1575 sourceC1575
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1575, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1576 : Charge := ![1, 0, 0, -1, 2, -2]
def sourceB1576 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1576 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1576 : Integer.Sparse Master := [(Sum.inr 1716, 1), (Sum.inr 2521, 1), (Sum.inr 3022, 2), (Sum.inr 3049, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

theorem sourceEq1576 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1576 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1576 + difference 0 0) (sourceB1576 + difference 0 0) sourceC1576) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1576 + difference 0 0) (sourceB1576 + difference 0 0) sourceC1576) = raw23793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1576 sourceB1576 sourceC1576 difference raw23793; decide +kernel
    rw [ha]
    exact (canonical23793 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1576 + difference 0 1) (sourceB1576 + difference 1 0) sourceC1576) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3022) := by
    have ha : (tripleCharges (sourceA1576 + difference 0 1) (sourceB1576 + difference 1 0) sourceC1576) = raw23794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1576 sourceB1576 sourceC1576 difference raw23794; decide +kernel
    rw [ha]
    exact (canonical23794 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1576 + difference 0 2) (sourceB1576 + difference 2 0) sourceC1576) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3022) := by
    have ha : (tripleCharges (sourceA1576 + difference 0 2) (sourceB1576 + difference 2 0) sourceC1576) = raw23795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1576 sourceB1576 sourceC1576 difference raw23795; decide +kernel
    rw [ha]
    exact (canonical23795 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1576 + difference 0 3) (sourceB1576 + difference 3 0) sourceC1576) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3049) := by
    have ha : (tripleCharges (sourceA1576 + difference 0 3) (sourceB1576 + difference 3 0) sourceC1576) = raw23796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1576 sourceB1576 sourceC1576 difference raw23796; decide +kernel
    rw [ha]
    exact (canonical23796 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1576 + difference 0 4) (sourceB1576 + difference 4 0) sourceC1576) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1576 + difference 0 4) (sourceB1576 + difference 4 0) sourceC1576) = raw23797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1576 sourceB1576 sourceC1576 difference raw23797; decide +kernel
    rw [ha]
    exact (canonical23797 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1576 + difference 0 5) (sourceB1576 + difference 5 0) sourceC1576) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2521) := by
    have ha : (tripleCharges (sourceA1576 + difference 0 5) (sourceB1576 + difference 5 0) sourceC1576) = raw23798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1576 sourceB1576 sourceC1576 difference raw23798; decide +kernel
    rw [ha]
    exact (canonical23798 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1576 + sourceB1576) sourceC1576) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1576 + sourceB1576) sourceC1576) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1576 sourceB1576 sourceC1576 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1576 sourceB1576 sourceC1576
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1576, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1577 : Charge := ![1, 0, 0, -1, 2, -2]
def sourceB1577 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1577 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1577 : Integer.Sparse Master := [(Sum.inr 1714, 2), (Sum.inr 1716, 1), (Sum.inr 1728, 1), (Sum.inr 1739, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

theorem sourceEq1577 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1577 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1577 + difference 0 4) (sourceB1577 + difference 4 0) sourceC1577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1577 + difference 0 4) (sourceB1577 + difference 4 0) sourceC1577) = raw23797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1577 sourceB1577 sourceC1577 difference raw23797; decide +kernel
    rw [ha]
    exact (canonical23797 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1577 + difference 1 4) (sourceB1577 + difference 4 1) sourceC1577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1577 + difference 1 4) (sourceB1577 + difference 4 1) sourceC1577) = raw23800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1577 sourceB1577 sourceC1577 difference raw23800; decide +kernel
    rw [ha]
    exact (canonical23800 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1577 + difference 2 4) (sourceB1577 + difference 4 2) sourceC1577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1577 + difference 2 4) (sourceB1577 + difference 4 2) sourceC1577) = raw23801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1577 sourceB1577 sourceC1577 difference raw23801; decide +kernel
    rw [ha]
    exact (canonical23801 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1577 + difference 3 4) (sourceB1577 + difference 4 3) sourceC1577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1577 + difference 3 4) (sourceB1577 + difference 4 3) sourceC1577) = raw23802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1577 sourceB1577 sourceC1577 difference raw23802; decide +kernel
    rw [ha]
    exact (canonical23802 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1577 + difference 4 4) (sourceB1577 + difference 4 4) sourceC1577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1577 + difference 4 4) (sourceB1577 + difference 4 4) sourceC1577) = raw23793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1577 sourceB1577 sourceC1577 difference raw23793; decide +kernel
    rw [ha]
    exact (canonical23793 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1577 + difference 5 4) (sourceB1577 + difference 4 5) sourceC1577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1577 + difference 5 4) (sourceB1577 + difference 4 5) sourceC1577) = raw23803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1577 sourceB1577 sourceC1577 difference raw23803; decide +kernel
    rw [ha]
    exact (canonical23803 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1577 + sourceB1577) sourceC1577) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1577 + sourceB1577) sourceC1577) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1577 sourceB1577 sourceC1577 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1577 sourceB1577 sourceC1577
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1577, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1578 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1578 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceC1578 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceForm1578 : Integer.Sparse Master := [(Sum.inr 604, 1), (Sum.inr 923, 1), (Sum.inr 1042, 1), (Sum.inr 1058, 1), (Sum.inr 1079, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

theorem sourceEq1578 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1578 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1578 + difference 2 0) (sourceB1578 + difference 0 2) sourceC1578) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 604) := by
    have ha : (tripleCharges (sourceA1578 + difference 2 0) (sourceB1578 + difference 0 2) sourceC1578) = raw23804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1578 sourceB1578 sourceC1578 difference raw23804; decide +kernel
    rw [ha]
    exact (canonical23804 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1578 + difference 2 1) (sourceB1578 + difference 1 2) sourceC1578) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 923) := by
    have ha : (tripleCharges (sourceA1578 + difference 2 1) (sourceB1578 + difference 1 2) sourceC1578) = raw23805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1578 sourceB1578 sourceC1578 difference raw23805; decide +kernel
    rw [ha]
    exact (canonical23805 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1578 + difference 2 2) (sourceB1578 + difference 2 2) sourceC1578) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA1578 + difference 2 2) (sourceB1578 + difference 2 2) sourceC1578) = raw23806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1578 sourceB1578 sourceC1578 difference raw23806; decide +kernel
    rw [ha]
    exact (canonical23806 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1578 + difference 2 3) (sourceB1578 + difference 3 2) sourceC1578) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1578 + difference 2 3) (sourceB1578 + difference 3 2) sourceC1578) = raw23807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1578 sourceB1578 sourceC1578 difference raw23807; decide +kernel
    rw [ha]
    exact (canonical23807 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1578 + difference 2 4) (sourceB1578 + difference 4 2) sourceC1578) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA1578 + difference 2 4) (sourceB1578 + difference 4 2) sourceC1578) = raw23808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1578 sourceB1578 sourceC1578 difference raw23808; decide +kernel
    rw [ha]
    exact (canonical23808 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1578 + difference 2 5) (sourceB1578 + difference 5 2) sourceC1578) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1578 + difference 2 5) (sourceB1578 + difference 5 2) sourceC1578) = raw23809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1578 sourceB1578 sourceC1578 difference raw23809; decide +kernel
    rw [ha]
    exact (canonical23809 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1578 + sourceB1578) sourceC1578) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1578 + sourceB1578) sourceC1578) = raw23810 := by
      apply Matrix.ext; unfold doubleCharges sourceA1578 sourceB1578 sourceC1578 raw23810; decide +kernel
    rw [ha]
    exact (canonical23810 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1578 sourceB1578 sourceC1578
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1578, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1579 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1579 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC1579 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceForm1579 : Integer.Sparse Master := [(Sum.inr 1335, 1), (Sum.inr 1337, 1), (Sum.inr 1338, 1), (Sum.inr 1347, 1), (Sum.inr 1406, 1), (Sum.inr 2954, 1), (Sum.inr 4091, -1)]

theorem sourceEq1579 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1579 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1579 + difference 0 2) (sourceB1579 + difference 2 0) sourceC1579) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA1579 + difference 0 2) (sourceB1579 + difference 2 0) sourceC1579) = raw23811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1579 sourceB1579 sourceC1579 difference raw23811; decide +kernel
    rw [ha]
    exact (canonical23811 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1579 + difference 1 2) (sourceB1579 + difference 2 1) sourceC1579) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1335) := by
    have ha : (tripleCharges (sourceA1579 + difference 1 2) (sourceB1579 + difference 2 1) sourceC1579) = raw23812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1579 sourceB1579 sourceC1579 difference raw23812; decide +kernel
    rw [ha]
    exact (canonical23812 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1579 + difference 2 2) (sourceB1579 + difference 2 2) sourceC1579) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA1579 + difference 2 2) (sourceB1579 + difference 2 2) sourceC1579) = raw23813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1579 sourceB1579 sourceC1579 difference raw23813; decide +kernel
    rw [ha]
    exact (canonical23813 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1579 + difference 3 2) (sourceB1579 + difference 2 3) sourceC1579) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1338) := by
    have ha : (tripleCharges (sourceA1579 + difference 3 2) (sourceB1579 + difference 2 3) sourceC1579) = raw23814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1579 sourceB1579 sourceC1579 difference raw23814; decide +kernel
    rw [ha]
    exact (canonical23814 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1579 + difference 4 2) (sourceB1579 + difference 2 4) sourceC1579) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA1579 + difference 4 2) (sourceB1579 + difference 2 4) sourceC1579) = raw23815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1579 sourceB1579 sourceC1579 difference raw23815; decide +kernel
    rw [ha]
    exact (canonical23815 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1579 + difference 5 2) (sourceB1579 + difference 2 5) sourceC1579) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1337) := by
    have ha : (tripleCharges (sourceA1579 + difference 5 2) (sourceB1579 + difference 2 5) sourceC1579) = raw23816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1579 sourceB1579 sourceC1579 difference raw23816; decide +kernel
    rw [ha]
    exact (canonical23816 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1579 + sourceB1579) sourceC1579) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1579 + sourceB1579) sourceC1579) = raw23817 := by
      apply Matrix.ext; unfold doubleCharges sourceA1579 sourceB1579 sourceC1579 raw23817; decide +kernel
    rw [ha]
    exact (canonical23817 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1579 sourceB1579 sourceC1579
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1579, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1580 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceB1580 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC1580 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1580 : Integer.Sparse Master := [(Sum.inr 1714, 1), (Sum.inr 2502, 1), (Sum.inr 3285, 1), (Sum.inr 3287, 1), (Sum.inr 3293, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

theorem sourceEq1580 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1580 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1580 + difference 0 0) (sourceB1580 + difference 0 0) sourceC1580) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1580 + difference 0 0) (sourceB1580 + difference 0 0) sourceC1580) = raw23801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1580 sourceB1580 sourceC1580 difference raw23801; decide +kernel
    rw [ha]
    exact (canonical23801 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1580 + difference 0 1) (sourceB1580 + difference 1 0) sourceC1580) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3285) := by
    have ha : (tripleCharges (sourceA1580 + difference 0 1) (sourceB1580 + difference 1 0) sourceC1580) = raw23818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1580 sourceB1580 sourceC1580 difference raw23818; decide +kernel
    rw [ha]
    exact (canonical23818 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1580 + difference 0 2) (sourceB1580 + difference 2 0) sourceC1580) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1580 + difference 0 2) (sourceB1580 + difference 2 0) sourceC1580) = raw23797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1580 sourceB1580 sourceC1580 difference raw23797; decide +kernel
    rw [ha]
    exact (canonical23797 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1580 + difference 0 3) (sourceB1580 + difference 3 0) sourceC1580) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3287) := by
    have ha : (tripleCharges (sourceA1580 + difference 0 3) (sourceB1580 + difference 3 0) sourceC1580) = raw23819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1580 sourceB1580 sourceC1580 difference raw23819; decide +kernel
    rw [ha]
    exact (canonical23819 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1580 + difference 0 4) (sourceB1580 + difference 4 0) sourceC1580) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1580 + difference 0 4) (sourceB1580 + difference 4 0) sourceC1580) = raw23820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1580 sourceB1580 sourceC1580 difference raw23820; decide +kernel
    rw [ha]
    exact (canonical23820 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1580 + difference 0 5) (sourceB1580 + difference 5 0) sourceC1580) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2502) := by
    have ha : (tripleCharges (sourceA1580 + difference 0 5) (sourceB1580 + difference 5 0) sourceC1580) = raw23821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1580 sourceB1580 sourceC1580 difference raw23821; decide +kernel
    rw [ha]
    exact (canonical23821 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1580 + sourceB1580) sourceC1580) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1580 + sourceB1580) sourceC1580) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1580 sourceB1580 sourceC1580 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1580 sourceB1580 sourceC1580
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1580, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1581 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceB1581 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC1581 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1581 : Integer.Sparse Master := [(Sum.inr 824, 1), (Sum.inr 1607, 1), (Sum.inr 1656, 1), (Sum.inr 1714, 1), (Sum.inr 1737, 1), (Sum.inr 1739, 1), (Sum.inr 4069, -1)]

theorem sourceEq1581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1581 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1581 + difference 3 0) (sourceB1581 + difference 0 3) sourceC1581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 824) := by
    have ha : (tripleCharges (sourceA1581 + difference 3 0) (sourceB1581 + difference 0 3) sourceC1581) = raw23822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1581 sourceB1581 sourceC1581 difference raw23822; decide +kernel
    rw [ha]
    exact (canonical23822 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1581 + difference 3 1) (sourceB1581 + difference 1 3) sourceC1581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1607) := by
    have ha : (tripleCharges (sourceA1581 + difference 3 1) (sourceB1581 + difference 1 3) sourceC1581) = raw23823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1581 sourceB1581 sourceC1581 difference raw23823; decide +kernel
    rw [ha]
    exact (canonical23823 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1581 + difference 3 2) (sourceB1581 + difference 2 3) sourceC1581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1581 + difference 3 2) (sourceB1581 + difference 2 3) sourceC1581) = raw23802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1581 sourceB1581 sourceC1581 difference raw23802; decide +kernel
    rw [ha]
    exact (canonical23802 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1581 + difference 3 3) (sourceB1581 + difference 3 3) sourceC1581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1581 + difference 3 3) (sourceB1581 + difference 3 3) sourceC1581) = raw23801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1581 sourceB1581 sourceC1581 difference raw23801; decide +kernel
    rw [ha]
    exact (canonical23801 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1581 + difference 3 4) (sourceB1581 + difference 4 3) sourceC1581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1581 + difference 3 4) (sourceB1581 + difference 4 3) sourceC1581) = raw23824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1581 sourceB1581 sourceC1581 difference raw23824; decide +kernel
    rw [ha]
    exact (canonical23824 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1581 + difference 3 5) (sourceB1581 + difference 5 3) sourceC1581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1656) := by
    have ha : (tripleCharges (sourceA1581 + difference 3 5) (sourceB1581 + difference 5 3) sourceC1581) = raw23825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1581 sourceB1581 sourceC1581 difference raw23825; decide +kernel
    rw [ha]
    exact (canonical23825 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1581 + sourceB1581) sourceC1581) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1581 + sourceB1581) sourceC1581) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1581 sourceB1581 sourceC1581 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1581 sourceB1581 sourceC1581
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1581, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1582 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceB1582 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC1582 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1582 : Integer.Sparse Master := [(Sum.inr 1713, 1), (Sum.inr 1714, 1), (Sum.inr 1715, 1), (Sum.inr 1724, 1), (Sum.inr 1737, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

theorem sourceEq1582 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1582 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1582 + difference 0 4) (sourceB1582 + difference 4 0) sourceC1582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1582 + difference 0 4) (sourceB1582 + difference 4 0) sourceC1582) = raw23820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1582 sourceB1582 sourceC1582 difference raw23820; decide +kernel
    rw [ha]
    exact (canonical23820 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1582 + difference 1 4) (sourceB1582 + difference 4 1) sourceC1582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1582 + difference 1 4) (sourceB1582 + difference 4 1) sourceC1582) = raw23826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1582 sourceB1582 sourceC1582 difference raw23826; decide +kernel
    rw [ha]
    exact (canonical23826 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1582 + difference 2 4) (sourceB1582 + difference 4 2) sourceC1582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1582 + difference 2 4) (sourceB1582 + difference 4 2) sourceC1582) = raw23827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1582 sourceB1582 sourceC1582 difference raw23827; decide +kernel
    rw [ha]
    exact (canonical23827 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1582 + difference 3 4) (sourceB1582 + difference 4 3) sourceC1582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1582 + difference 3 4) (sourceB1582 + difference 4 3) sourceC1582) = raw23824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1582 sourceB1582 sourceC1582 difference raw23824; decide +kernel
    rw [ha]
    exact (canonical23824 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1582 + difference 4 4) (sourceB1582 + difference 4 4) sourceC1582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1582 + difference 4 4) (sourceB1582 + difference 4 4) sourceC1582) = raw23801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1582 sourceB1582 sourceC1582 difference raw23801; decide +kernel
    rw [ha]
    exact (canonical23801 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1582 + difference 5 4) (sourceB1582 + difference 4 5) sourceC1582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1582 + difference 5 4) (sourceB1582 + difference 4 5) sourceC1582) = raw23828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1582 sourceB1582 sourceC1582 difference raw23828; decide +kernel
    rw [ha]
    exact (canonical23828 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1582 + sourceB1582) sourceC1582) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1582 + sourceB1582) sourceC1582) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1582 sourceB1582 sourceC1582 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1582 sourceB1582 sourceC1582
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1582, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1583 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceB1583 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC1583 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1583 : Integer.Sparse Master := [(Sum.inr 807, 1), (Sum.inr 1598, 1), (Sum.inr 1646, 1), (Sum.inr 1714, 1), (Sum.inr 1724, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

theorem sourceEq1583 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1583 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1583 + difference 5 0) (sourceB1583 + difference 0 5) sourceC1583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 807) := by
    have ha : (tripleCharges (sourceA1583 + difference 5 0) (sourceB1583 + difference 0 5) sourceC1583) = raw23829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1583 sourceB1583 sourceC1583 difference raw23829; decide +kernel
    rw [ha]
    exact (canonical23829 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1583 + difference 5 1) (sourceB1583 + difference 1 5) sourceC1583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1598) := by
    have ha : (tripleCharges (sourceA1583 + difference 5 1) (sourceB1583 + difference 1 5) sourceC1583) = raw23830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1583 sourceB1583 sourceC1583 difference raw23830; decide +kernel
    rw [ha]
    exact (canonical23830 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1583 + difference 5 2) (sourceB1583 + difference 2 5) sourceC1583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1583 + difference 5 2) (sourceB1583 + difference 2 5) sourceC1583) = raw23803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1583 sourceB1583 sourceC1583 difference raw23803; decide +kernel
    rw [ha]
    exact (canonical23803 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1583 + difference 5 3) (sourceB1583 + difference 3 5) sourceC1583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1646) := by
    have ha : (tripleCharges (sourceA1583 + difference 5 3) (sourceB1583 + difference 3 5) sourceC1583) = raw23831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1583 sourceB1583 sourceC1583 difference raw23831; decide +kernel
    rw [ha]
    exact (canonical23831 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1583 + difference 5 4) (sourceB1583 + difference 4 5) sourceC1583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1583 + difference 5 4) (sourceB1583 + difference 4 5) sourceC1583) = raw23828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1583 sourceB1583 sourceC1583 difference raw23828; decide +kernel
    rw [ha]
    exact (canonical23828 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1583 + difference 5 5) (sourceB1583 + difference 5 5) sourceC1583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1583 + difference 5 5) (sourceB1583 + difference 5 5) sourceC1583) = raw23801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1583 sourceB1583 sourceC1583 difference raw23801; decide +kernel
    rw [ha]
    exact (canonical23801 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1583 + sourceB1583) sourceC1583) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1583 + sourceB1583) sourceC1583) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1583 sourceB1583 sourceC1583 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1583 sourceB1583 sourceC1583
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1583, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1584 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1584 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceC1584 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceForm1584 : Integer.Sparse Master := [(Sum.inr 601, 1), (Sum.inr 920, 1), (Sum.inr 1057, 1), (Sum.inr 1079, 1), (Sum.inr 1083, 2), (Sum.inr 4084, -1)]

theorem sourceEq1584 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1584 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1584 + difference 2 0) (sourceB1584 + difference 0 2) sourceC1584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 601) := by
    have ha : (tripleCharges (sourceA1584 + difference 2 0) (sourceB1584 + difference 0 2) sourceC1584) = raw23832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1584 sourceB1584 sourceC1584 difference raw23832; decide +kernel
    rw [ha]
    exact (canonical23832 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1584 + difference 2 1) (sourceB1584 + difference 1 2) sourceC1584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 920) := by
    have ha : (tripleCharges (sourceA1584 + difference 2 1) (sourceB1584 + difference 1 2) sourceC1584) = raw23833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1584 sourceB1584 sourceC1584 difference raw23833; decide +kernel
    rw [ha]
    exact (canonical23833 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1584 + difference 2 2) (sourceB1584 + difference 2 2) sourceC1584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1057) := by
    have ha : (tripleCharges (sourceA1584 + difference 2 2) (sourceB1584 + difference 2 2) sourceC1584) = raw23834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1584 sourceB1584 sourceC1584 difference raw23834; decide +kernel
    rw [ha]
    exact (canonical23834 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1584 + difference 2 3) (sourceB1584 + difference 3 2) sourceC1584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1584 + difference 2 3) (sourceB1584 + difference 3 2) sourceC1584) = raw23835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1584 sourceB1584 sourceC1584 difference raw23835; decide +kernel
    rw [ha]
    exact (canonical23835 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1584 + difference 2 4) (sourceB1584 + difference 4 2) sourceC1584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1584 + difference 2 4) (sourceB1584 + difference 4 2) sourceC1584) = raw23836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1584 sourceB1584 sourceC1584 difference raw23836; decide +kernel
    rw [ha]
    exact (canonical23836 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1584 + difference 2 5) (sourceB1584 + difference 5 2) sourceC1584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1584 + difference 2 5) (sourceB1584 + difference 5 2) sourceC1584) = raw23837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1584 sourceB1584 sourceC1584 difference raw23837; decide +kernel
    rw [ha]
    exact (canonical23837 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1584 + sourceB1584) sourceC1584) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1584 + sourceB1584) sourceC1584) = raw23838 := by
      apply Matrix.ext; unfold doubleCharges sourceA1584 sourceB1584 sourceC1584 raw23838; decide +kernel
    rw [ha]
    exact (canonical23838 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1584 sourceB1584 sourceC1584
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1584, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1585 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1585 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC1585 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceForm1585 : Integer.Sparse Master := [(Sum.inr 1316, 1), (Sum.inr 1320, 1), (Sum.inr 1322, 2), (Sum.inr 1370, 1), (Sum.inr 2884, 1), (Sum.inr 4091, -1)]

theorem sourceEq1585 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1585 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1585 + difference 0 2) (sourceB1585 + difference 2 0) sourceC1585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA1585 + difference 0 2) (sourceB1585 + difference 2 0) sourceC1585) = raw23839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1585 sourceB1585 sourceC1585 difference raw23839; decide +kernel
    rw [ha]
    exact (canonical23839 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1585 + difference 1 2) (sourceB1585 + difference 2 1) sourceC1585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1316) := by
    have ha : (tripleCharges (sourceA1585 + difference 1 2) (sourceB1585 + difference 2 1) sourceC1585) = raw23840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1585 sourceB1585 sourceC1585 difference raw23840; decide +kernel
    rw [ha]
    exact (canonical23840 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1585 + difference 2 2) (sourceB1585 + difference 2 2) sourceC1585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1370) := by
    have ha : (tripleCharges (sourceA1585 + difference 2 2) (sourceB1585 + difference 2 2) sourceC1585) = raw23841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1585 sourceB1585 sourceC1585 difference raw23841; decide +kernel
    rw [ha]
    exact (canonical23841 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1585 + difference 3 2) (sourceB1585 + difference 2 3) sourceC1585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1322) := by
    have ha : (tripleCharges (sourceA1585 + difference 3 2) (sourceB1585 + difference 2 3) sourceC1585) = raw23842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1585 sourceB1585 sourceC1585 difference raw23842; decide +kernel
    rw [ha]
    exact (canonical23842 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1585 + difference 4 2) (sourceB1585 + difference 2 4) sourceC1585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1322) := by
    have ha : (tripleCharges (sourceA1585 + difference 4 2) (sourceB1585 + difference 2 4) sourceC1585) = raw23843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1585 sourceB1585 sourceC1585 difference raw23843; decide +kernel
    rw [ha]
    exact (canonical23843 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1585 + difference 5 2) (sourceB1585 + difference 2 5) sourceC1585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1320) := by
    have ha : (tripleCharges (sourceA1585 + difference 5 2) (sourceB1585 + difference 2 5) sourceC1585) = raw23844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1585 sourceB1585 sourceC1585 difference raw23844; decide +kernel
    rw [ha]
    exact (canonical23844 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1585 + sourceB1585) sourceC1585) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1585 + sourceB1585) sourceC1585) = raw13064 := by
      apply Matrix.ext; unfold doubleCharges sourceA1585 sourceB1585 sourceC1585 raw13064; decide +kernel
    rw [ha]
    exact (canonical13064 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1585 sourceB1585 sourceC1585
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1585, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1586 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB1586 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC1586 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1586 : Integer.Sparse Master := [(Sum.inr 1709, 1), (Sum.inr 3241, 1), (Sum.inr 3245, 1), (Sum.inr 3246, 2), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

theorem sourceEq1586 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1586 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1586 + difference 0 0) (sourceB1586 + difference 0 0) sourceC1586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1586 + difference 0 0) (sourceB1586 + difference 0 0) sourceC1586) = raw23845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1586 sourceB1586 sourceC1586 difference raw23845; decide +kernel
    rw [ha]
    exact (canonical23845 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1586 + difference 0 1) (sourceB1586 + difference 1 0) sourceC1586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3241) := by
    have ha : (tripleCharges (sourceA1586 + difference 0 1) (sourceB1586 + difference 1 0) sourceC1586) = raw23846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1586 sourceB1586 sourceC1586 difference raw23846; decide +kernel
    rw [ha]
    exact (canonical23846 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1586 + difference 0 2) (sourceB1586 + difference 2 0) sourceC1586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1586 + difference 0 2) (sourceB1586 + difference 2 0) sourceC1586) = raw23847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1586 sourceB1586 sourceC1586 difference raw23847; decide +kernel
    rw [ha]
    exact (canonical23847 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1586 + difference 0 3) (sourceB1586 + difference 3 0) sourceC1586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3246) := by
    have ha : (tripleCharges (sourceA1586 + difference 0 3) (sourceB1586 + difference 3 0) sourceC1586) = raw23848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1586 sourceB1586 sourceC1586 difference raw23848; decide +kernel
    rw [ha]
    exact (canonical23848 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1586 + difference 0 4) (sourceB1586 + difference 4 0) sourceC1586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3246) := by
    have ha : (tripleCharges (sourceA1586 + difference 0 4) (sourceB1586 + difference 4 0) sourceC1586) = raw23849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1586 sourceB1586 sourceC1586 difference raw23849; decide +kernel
    rw [ha]
    exact (canonical23849 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1586 + difference 0 5) (sourceB1586 + difference 5 0) sourceC1586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3245) := by
    have ha : (tripleCharges (sourceA1586 + difference 0 5) (sourceB1586 + difference 5 0) sourceC1586) = raw23850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1586 sourceB1586 sourceC1586 difference raw23850; decide +kernel
    rw [ha]
    exact (canonical23850 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1586 + sourceB1586) sourceC1586) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1586 + sourceB1586) sourceC1586) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1586 sourceB1586 sourceC1586 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1586 sourceB1586 sourceC1586
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1586, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1587 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB1587 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC1587 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1587 : Integer.Sparse Master := [(Sum.inr 1705, 1), (Sum.inr 1707, 1), (Sum.inr 1709, 1), (Sum.inr 1724, 2), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

theorem sourceEq1587 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1587 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1587 + difference 0 2) (sourceB1587 + difference 2 0) sourceC1587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1587 + difference 0 2) (sourceB1587 + difference 2 0) sourceC1587) = raw23847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1587 sourceB1587 sourceC1587 difference raw23847; decide +kernel
    rw [ha]
    exact (canonical23847 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1587 + difference 1 2) (sourceB1587 + difference 2 1) sourceC1587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1587 + difference 1 2) (sourceB1587 + difference 2 1) sourceC1587) = raw23851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1587 sourceB1587 sourceC1587 difference raw23851; decide +kernel
    rw [ha]
    exact (canonical23851 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1587 + difference 2 2) (sourceB1587 + difference 2 2) sourceC1587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1587 + difference 2 2) (sourceB1587 + difference 2 2) sourceC1587) = raw23845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1587 sourceB1587 sourceC1587 difference raw23845; decide +kernel
    rw [ha]
    exact (canonical23845 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1587 + difference 3 2) (sourceB1587 + difference 2 3) sourceC1587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1587 + difference 3 2) (sourceB1587 + difference 2 3) sourceC1587) = raw23852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1587 sourceB1587 sourceC1587 difference raw23852; decide +kernel
    rw [ha]
    exact (canonical23852 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1587 + difference 4 2) (sourceB1587 + difference 2 4) sourceC1587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1587 + difference 4 2) (sourceB1587 + difference 2 4) sourceC1587) = raw23828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1587 sourceB1587 sourceC1587 difference raw23828; decide +kernel
    rw [ha]
    exact (canonical23828 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1587 + difference 5 2) (sourceB1587 + difference 2 5) sourceC1587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1587 + difference 5 2) (sourceB1587 + difference 2 5) sourceC1587) = raw23853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1587 sourceB1587 sourceC1587 difference raw23853; decide +kernel
    rw [ha]
    exact (canonical23853 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1587 + sourceB1587) sourceC1587) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1587 + sourceB1587) sourceC1587) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1587 sourceB1587 sourceC1587 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1587 sourceB1587 sourceC1587
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1587, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1588 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB1588 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC1588 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1588 : Integer.Sparse Master := [(Sum.inr 811, 1), (Sum.inr 1601, 1), (Sum.inr 1649, 1), (Sum.inr 1709, 1), (Sum.inr 1715, 1), (Sum.inr 1724, 1), (Sum.inr 4069, -1)]

theorem sourceEq1588 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1588 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1588 + difference 3 0) (sourceB1588 + difference 0 3) sourceC1588) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA1588 + difference 3 0) (sourceB1588 + difference 0 3) sourceC1588) = raw23854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1588 sourceB1588 sourceC1588 difference raw23854; decide +kernel
    rw [ha]
    exact (canonical23854 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1588 + difference 3 1) (sourceB1588 + difference 1 3) sourceC1588) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1601) := by
    have ha : (tripleCharges (sourceA1588 + difference 3 1) (sourceB1588 + difference 1 3) sourceC1588) = raw23855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1588 sourceB1588 sourceC1588 difference raw23855; decide +kernel
    rw [ha]
    exact (canonical23855 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1588 + difference 3 2) (sourceB1588 + difference 2 3) sourceC1588) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1588 + difference 3 2) (sourceB1588 + difference 2 3) sourceC1588) = raw23852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1588 sourceB1588 sourceC1588 difference raw23852; decide +kernel
    rw [ha]
    exact (canonical23852 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1588 + difference 3 3) (sourceB1588 + difference 3 3) sourceC1588) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1588 + difference 3 3) (sourceB1588 + difference 3 3) sourceC1588) = raw23845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1588 sourceB1588 sourceC1588 difference raw23845; decide +kernel
    rw [ha]
    exact (canonical23845 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1588 + difference 3 4) (sourceB1588 + difference 4 3) sourceC1588) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1649) := by
    have ha : (tripleCharges (sourceA1588 + difference 3 4) (sourceB1588 + difference 4 3) sourceC1588) = raw23856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1588 sourceB1588 sourceC1588 difference raw23856; decide +kernel
    rw [ha]
    exact (canonical23856 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1588 + difference 3 5) (sourceB1588 + difference 5 3) sourceC1588) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1588 + difference 3 5) (sourceB1588 + difference 5 3) sourceC1588) = raw23857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1588 sourceB1588 sourceC1588 difference raw23857; decide +kernel
    rw [ha]
    exact (canonical23857 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1588 + sourceB1588) sourceC1588) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1588 + sourceB1588) sourceC1588) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1588 sourceB1588 sourceC1588 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1588 sourceB1588 sourceC1588
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1588, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1589 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB1589 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC1589 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1589 : Integer.Sparse Master := [(Sum.inr 1701, 1), (Sum.inr 1702, 1), (Sum.inr 1709, 1), (Sum.inr 1715, 2), (Sum.inr 3245, 1), (Sum.inr 4069, -1)]

theorem sourceEq1589 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1589 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1589 + difference 0 5) (sourceB1589 + difference 5 0) sourceC1589) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3245) := by
    have ha : (tripleCharges (sourceA1589 + difference 0 5) (sourceB1589 + difference 5 0) sourceC1589) = raw23850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1589 sourceB1589 sourceC1589 difference raw23850; decide +kernel
    rw [ha]
    exact (canonical23850 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1589 + difference 1 5) (sourceB1589 + difference 5 1) sourceC1589) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1701) := by
    have ha : (tripleCharges (sourceA1589 + difference 1 5) (sourceB1589 + difference 5 1) sourceC1589) = raw23858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1589 sourceB1589 sourceC1589 difference raw23858; decide +kernel
    rw [ha]
    exact (canonical23858 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1589 + difference 2 5) (sourceB1589 + difference 5 2) sourceC1589) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1702) := by
    have ha : (tripleCharges (sourceA1589 + difference 2 5) (sourceB1589 + difference 5 2) sourceC1589) = raw23859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1589 sourceB1589 sourceC1589 difference raw23859; decide +kernel
    rw [ha]
    exact (canonical23859 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1589 + difference 3 5) (sourceB1589 + difference 5 3) sourceC1589) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1589 + difference 3 5) (sourceB1589 + difference 5 3) sourceC1589) = raw23857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1589 sourceB1589 sourceC1589 difference raw23857; decide +kernel
    rw [ha]
    exact (canonical23857 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1589 + difference 4 5) (sourceB1589 + difference 5 4) sourceC1589) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1589 + difference 4 5) (sourceB1589 + difference 5 4) sourceC1589) = raw23827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1589 sourceB1589 sourceC1589 difference raw23827; decide +kernel
    rw [ha]
    exact (canonical23827 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1589 + difference 5 5) (sourceB1589 + difference 5 5) sourceC1589) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1589 + difference 5 5) (sourceB1589 + difference 5 5) sourceC1589) = raw23845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1589 sourceB1589 sourceC1589 difference raw23845; decide +kernel
    rw [ha]
    exact (canonical23845 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1589 + sourceB1589) sourceC1589) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1589 + sourceB1589) sourceC1589) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1589 sourceB1589 sourceC1589 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1589 sourceB1589 sourceC1589
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1589, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1590 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1590 : Charge := ![3, 0, -2, 0, -1, 0]
def sourceC1590 : Charge := ![1, 0, 2, -1, 0, -2]
def sourceForm1590 : Integer.Sparse Master := [(Sum.inr 1314, 1), (Sum.inr 1317, 1), (Sum.inr 1318, 1), (Sum.inr 1321, 1), (Sum.inr 1367, 1), (Sum.inr 2881, 1), (Sum.inr 4092, -1)]

theorem sourceEq1590 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1590 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1590 + difference 0 2) (sourceB1590 + difference 2 0) sourceC1590) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA1590 + difference 0 2) (sourceB1590 + difference 2 0) sourceC1590) = raw23860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1590 sourceB1590 sourceC1590 difference raw23860; decide +kernel
    rw [ha]
    exact (canonical23860 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1590 + difference 1 2) (sourceB1590 + difference 2 1) sourceC1590) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1314) := by
    have ha : (tripleCharges (sourceA1590 + difference 1 2) (sourceB1590 + difference 2 1) sourceC1590) = raw23861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1590 sourceB1590 sourceC1590 difference raw23861; decide +kernel
    rw [ha]
    exact (canonical23861 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1590 + difference 2 2) (sourceB1590 + difference 2 2) sourceC1590) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA1590 + difference 2 2) (sourceB1590 + difference 2 2) sourceC1590) = raw23862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1590 sourceB1590 sourceC1590 difference raw23862; decide +kernel
    rw [ha]
    exact (canonical23862 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1590 + difference 3 2) (sourceB1590 + difference 2 3) sourceC1590) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1318) := by
    have ha : (tripleCharges (sourceA1590 + difference 3 2) (sourceB1590 + difference 2 3) sourceC1590) = raw23863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1590 sourceB1590 sourceC1590 difference raw23863; decide +kernel
    rw [ha]
    exact (canonical23863 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1590 + difference 4 2) (sourceB1590 + difference 2 4) sourceC1590) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1321) := by
    have ha : (tripleCharges (sourceA1590 + difference 4 2) (sourceB1590 + difference 2 4) sourceC1590) = raw23864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1590 sourceB1590 sourceC1590 difference raw23864; decide +kernel
    rw [ha]
    exact (canonical23864 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1590 + difference 5 2) (sourceB1590 + difference 2 5) sourceC1590) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1317) := by
    have ha : (tripleCharges (sourceA1590 + difference 5 2) (sourceB1590 + difference 2 5) sourceC1590) = raw23865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1590 sourceB1590 sourceC1590 difference raw23865; decide +kernel
    rw [ha]
    exact (canonical23865 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1590 + sourceB1590) sourceC1590) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1590 + sourceB1590) sourceC1590) = raw23866 := by
      apply Matrix.ext; unfold doubleCharges sourceA1590 sourceB1590 sourceC1590 raw23866; decide +kernel
    rw [ha]
    exact (canonical23866 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1590 sourceB1590 sourceC1590
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1590, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1591 : Charge := ![1, 0, 2, -1, 0, -2]
def sourceB1591 : Charge := ![3, 0, -2, 0, -1, 0]
def sourceC1591 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1591 : Integer.Sparse Master := [(Sum.inr 1715, 1), (Sum.inr 2466, 1), (Sum.inr 3238, 1), (Sum.inr 3240, 1), (Sum.inr 3245, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

theorem sourceEq1591 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1591 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1591 + difference 0 0) (sourceB1591 + difference 0 0) sourceC1591) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1591 + difference 0 0) (sourceB1591 + difference 0 0) sourceC1591) = raw23827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1591 sourceB1591 sourceC1591 difference raw23827; decide +kernel
    rw [ha]
    exact (canonical23827 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1591 + difference 0 1) (sourceB1591 + difference 1 0) sourceC1591) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3238) := by
    have ha : (tripleCharges (sourceA1591 + difference 0 1) (sourceB1591 + difference 1 0) sourceC1591) = raw23867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1591 sourceB1591 sourceC1591 difference raw23867; decide +kernel
    rw [ha]
    exact (canonical23867 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1591 + difference 0 2) (sourceB1591 + difference 2 0) sourceC1591) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1591 + difference 0 2) (sourceB1591 + difference 2 0) sourceC1591) = raw23820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1591 sourceB1591 sourceC1591 difference raw23820; decide +kernel
    rw [ha]
    exact (canonical23820 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1591 + difference 0 3) (sourceB1591 + difference 3 0) sourceC1591) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3240) := by
    have ha : (tripleCharges (sourceA1591 + difference 0 3) (sourceB1591 + difference 3 0) sourceC1591) = raw23868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1591 sourceB1591 sourceC1591 difference raw23868; decide +kernel
    rw [ha]
    exact (canonical23868 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1591 + difference 0 4) (sourceB1591 + difference 4 0) sourceC1591) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3245) := by
    have ha : (tripleCharges (sourceA1591 + difference 0 4) (sourceB1591 + difference 4 0) sourceC1591) = raw23850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1591 sourceB1591 sourceC1591 difference raw23850; decide +kernel
    rw [ha]
    exact (canonical23850 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1591 + difference 0 5) (sourceB1591 + difference 5 0) sourceC1591) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2466) := by
    have ha : (tripleCharges (sourceA1591 + difference 0 5) (sourceB1591 + difference 5 0) sourceC1591) = raw23869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1591 sourceB1591 sourceC1591 difference raw23869; decide +kernel
    rw [ha]
    exact (canonical23869 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1591 + sourceB1591) sourceC1591) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1591 + sourceB1591) sourceC1591) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1591 sourceB1591 sourceC1591 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1591 sourceB1591 sourceC1591
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1591, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1592 : Charge := ![1, 0, 2, -1, 0, -2]
def sourceB1592 : Charge := ![3, 0, -2, 0, -1, 0]
def sourceC1592 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1592 : Integer.Sparse Master := [(Sum.inr 827, 1), (Sum.inr 1609, 1), (Sum.inr 1658, 1), (Sum.inr 1715, 2), (Sum.inr 1737, 1), (Sum.inr 4069, -1)]

theorem sourceEq1592 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1592 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1592 + difference 3 0) (sourceB1592 + difference 0 3) sourceC1592) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 827) := by
    have ha : (tripleCharges (sourceA1592 + difference 3 0) (sourceB1592 + difference 0 3) sourceC1592) = raw23870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1592 sourceB1592 sourceC1592 difference raw23870; decide +kernel
    rw [ha]
    exact (canonical23870 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1592 + difference 3 1) (sourceB1592 + difference 1 3) sourceC1592) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1609) := by
    have ha : (tripleCharges (sourceA1592 + difference 3 1) (sourceB1592 + difference 1 3) sourceC1592) = raw23871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1592 sourceB1592 sourceC1592 difference raw23871; decide +kernel
    rw [ha]
    exact (canonical23871 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1592 + difference 3 2) (sourceB1592 + difference 2 3) sourceC1592) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1592 + difference 3 2) (sourceB1592 + difference 2 3) sourceC1592) = raw23824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1592 sourceB1592 sourceC1592 difference raw23824; decide +kernel
    rw [ha]
    exact (canonical23824 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1592 + difference 3 3) (sourceB1592 + difference 3 3) sourceC1592) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1592 + difference 3 3) (sourceB1592 + difference 3 3) sourceC1592) = raw23827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1592 sourceB1592 sourceC1592 difference raw23827; decide +kernel
    rw [ha]
    exact (canonical23827 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1592 + difference 3 4) (sourceB1592 + difference 4 3) sourceC1592) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1592 + difference 3 4) (sourceB1592 + difference 4 3) sourceC1592) = raw23857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1592 sourceB1592 sourceC1592 difference raw23857; decide +kernel
    rw [ha]
    exact (canonical23857 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1592 + difference 3 5) (sourceB1592 + difference 5 3) sourceC1592) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1658) := by
    have ha : (tripleCharges (sourceA1592 + difference 3 5) (sourceB1592 + difference 5 3) sourceC1592) = raw23872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1592 sourceB1592 sourceC1592 difference raw23872; decide +kernel
    rw [ha]
    exact (canonical23872 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1592 + sourceB1592) sourceC1592) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1592 + sourceB1592) sourceC1592) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1592 sourceB1592 sourceC1592 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1592 sourceB1592 sourceC1592
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1592, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1593 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1593 : Charge := ![3, 0, -3, 0, 0, 0]
def sourceC1593 : Charge := ![1, 0, 3, -1, -1, -2]
def sourceForm1593 : Integer.Sparse Master := [(Sum.inr 1351, 1), (Sum.inr 2237, 1), (Sum.inr 2246, 1), (Sum.inr 2254, 2), (Sum.inr 2840, 1), (Sum.inr 4080, -1)]

theorem sourceEq1593 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1593 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1593 + difference 0 0) (sourceB1593 + difference 0 0) sourceC1593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1351) := by
    have ha : (tripleCharges (sourceA1593 + difference 0 0) (sourceB1593 + difference 0 0) sourceC1593) = raw23873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1593 sourceB1593 sourceC1593 difference raw23873; decide +kernel
    rw [ha]
    exact (canonical23873 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1593 + difference 0 1) (sourceB1593 + difference 1 0) sourceC1593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2237) := by
    have ha : (tripleCharges (sourceA1593 + difference 0 1) (sourceB1593 + difference 1 0) sourceC1593) = raw23874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1593 sourceB1593 sourceC1593 difference raw23874; decide +kernel
    rw [ha]
    exact (canonical23874 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1593 + difference 0 2) (sourceB1593 + difference 2 0) sourceC1593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2840) := by
    have ha : (tripleCharges (sourceA1593 + difference 0 2) (sourceB1593 + difference 2 0) sourceC1593) = raw23875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1593 sourceB1593 sourceC1593 difference raw23875; decide +kernel
    rw [ha]
    exact (canonical23875 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1593 + difference 0 3) (sourceB1593 + difference 3 0) sourceC1593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA1593 + difference 0 3) (sourceB1593 + difference 3 0) sourceC1593) = raw23876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1593 sourceB1593 sourceC1593 difference raw23876; decide +kernel
    rw [ha]
    exact (canonical23876 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1593 + difference 0 4) (sourceB1593 + difference 4 0) sourceC1593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA1593 + difference 0 4) (sourceB1593 + difference 4 0) sourceC1593) = raw23877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1593 sourceB1593 sourceC1593 difference raw23877; decide +kernel
    rw [ha]
    exact (canonical23877 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1593 + difference 0 5) (sourceB1593 + difference 5 0) sourceC1593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA1593 + difference 0 5) (sourceB1593 + difference 5 0) sourceC1593) = raw23878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1593 sourceB1593 sourceC1593 difference raw23878; decide +kernel
    rw [ha]
    exact (canonical23878 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1593 + sourceB1593) sourceC1593) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1593 + sourceB1593) sourceC1593) = raw23879 := by
      apply Matrix.ext; unfold doubleCharges sourceA1593 sourceB1593 sourceC1593 raw23879; decide +kernel
    rw [ha]
    exact (canonical23879 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1593 sourceB1593 sourceC1593
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1593, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1594 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1594 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1594 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceForm1594 : Integer.Sparse Master := [(Sum.inr 578, 1), (Sum.inr 942, 1), (Sum.inr 1020, 1), (Sum.inr 1039, 1), (Sum.inr 1041, 2), (Sum.inr 4083, -1)]

theorem sourceEq1594 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1594 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1594 + difference 1 0) (sourceB1594 + difference 0 1) sourceC1594) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 578) := by
    have ha : (tripleCharges (sourceA1594 + difference 1 0) (sourceB1594 + difference 0 1) sourceC1594) = raw23880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1594 sourceB1594 sourceC1594 difference raw23880; decide +kernel
    rw [ha]
    exact (canonical23880 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1594 + difference 1 1) (sourceB1594 + difference 1 1) sourceC1594) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1020) := by
    have ha : (tripleCharges (sourceA1594 + difference 1 1) (sourceB1594 + difference 1 1) sourceC1594) = raw11301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1594 sourceB1594 sourceC1594 difference raw11301; decide +kernel
    rw [ha]
    exact (canonical11301 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1594 + difference 1 2) (sourceB1594 + difference 2 1) sourceC1594) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 942) := by
    have ha : (tripleCharges (sourceA1594 + difference 1 2) (sourceB1594 + difference 2 1) sourceC1594) = raw23881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1594 sourceB1594 sourceC1594 difference raw23881; decide +kernel
    rw [ha]
    exact (canonical23881 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1594 + difference 1 3) (sourceB1594 + difference 3 1) sourceC1594) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1594 + difference 1 3) (sourceB1594 + difference 3 1) sourceC1594) = raw11299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1594 sourceB1594 sourceC1594 difference raw11299; decide +kernel
    rw [ha]
    exact (canonical11299 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1594 + difference 1 4) (sourceB1594 + difference 4 1) sourceC1594) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1594 + difference 1 4) (sourceB1594 + difference 4 1) sourceC1594) = raw23882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1594 sourceB1594 sourceC1594 difference raw23882; decide +kernel
    rw [ha]
    exact (canonical23882 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1594 + difference 1 5) (sourceB1594 + difference 5 1) sourceC1594) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1039) := by
    have ha : (tripleCharges (sourceA1594 + difference 1 5) (sourceB1594 + difference 5 1) sourceC1594) = raw23883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1594 sourceB1594 sourceC1594 difference raw23883; decide +kernel
    rw [ha]
    exact (canonical23883 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1594 + sourceB1594) sourceC1594) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1594 + sourceB1594) sourceC1594) = raw11298 := by
      apply Matrix.ext; unfold doubleCharges sourceA1594 sourceB1594 sourceC1594 raw11298; decide +kernel
    rw [ha]
    exact (canonical11298 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1594 sourceB1594 sourceC1594
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1594, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1595 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB1595 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC1595 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1595 : Integer.Sparse Master := [(Sum.inr 1705, 1), (Sum.inr 3281, 1), (Sum.inr 3282, 2), (Sum.inr 3299, 2), (Sum.inr 4069, -1)]

theorem sourceEq1595 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1595 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1595 + difference 0 0) (sourceB1595 + difference 0 0) sourceC1595) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1595 + difference 0 0) (sourceB1595 + difference 0 0) sourceC1595) = raw23851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1595 sourceB1595 sourceC1595 difference raw23851; decide +kernel
    rw [ha]
    exact (canonical23851 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1595 + difference 0 1) (sourceB1595 + difference 1 0) sourceC1595) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1595 + difference 0 1) (sourceB1595 + difference 1 0) sourceC1595) = raw23847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1595 sourceB1595 sourceC1595 difference raw23847; decide +kernel
    rw [ha]
    exact (canonical23847 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1595 + difference 0 2) (sourceB1595 + difference 2 0) sourceC1595) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1595 + difference 0 2) (sourceB1595 + difference 2 0) sourceC1595) = raw23884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1595 sourceB1595 sourceC1595 difference raw23884; decide +kernel
    rw [ha]
    exact (canonical23884 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1595 + difference 0 3) (sourceB1595 + difference 3 0) sourceC1595) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3282) := by
    have ha : (tripleCharges (sourceA1595 + difference 0 3) (sourceB1595 + difference 3 0) sourceC1595) = raw23885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1595 sourceB1595 sourceC1595 difference raw23885; decide +kernel
    rw [ha]
    exact (canonical23885 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1595 + difference 0 4) (sourceB1595 + difference 4 0) sourceC1595) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3282) := by
    have ha : (tripleCharges (sourceA1595 + difference 0 4) (sourceB1595 + difference 4 0) sourceC1595) = raw23886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1595 sourceB1595 sourceC1595 difference raw23886; decide +kernel
    rw [ha]
    exact (canonical23886 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1595 + difference 0 5) (sourceB1595 + difference 5 0) sourceC1595) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3281) := by
    have ha : (tripleCharges (sourceA1595 + difference 0 5) (sourceB1595 + difference 5 0) sourceC1595) = raw23887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1595 sourceB1595 sourceC1595 difference raw23887; decide +kernel
    rw [ha]
    exact (canonical23887 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1595 + sourceB1595) sourceC1595) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1595 + sourceB1595) sourceC1595) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1595 sourceB1595 sourceC1595 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1595 sourceB1595 sourceC1595
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1595, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1596 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB1596 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC1596 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1596 : Integer.Sparse Master := [(Sum.inr 782, 1), (Sum.inr 784, 2), (Sum.inr 803, 2), (Sum.inr 1705, 1), (Sum.inr 4069, -1)]

theorem sourceEq1596 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1596 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1596 + difference 0 0) (sourceB1596 + difference 0 0) sourceC1596) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1596 + difference 0 0) (sourceB1596 + difference 0 0) sourceC1596) = raw23851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1596 sourceB1596 sourceC1596 difference raw23851; decide +kernel
    rw [ha]
    exact (canonical23851 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1596 + difference 1 0) (sourceB1596 + difference 0 1) sourceC1596) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 784) := by
    have ha : (tripleCharges (sourceA1596 + difference 1 0) (sourceB1596 + difference 0 1) sourceC1596) = raw23888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1596 sourceB1596 sourceC1596 difference raw23888; decide +kernel
    rw [ha]
    exact (canonical23888 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1596 + difference 2 0) (sourceB1596 + difference 0 2) sourceC1596) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 784) := by
    have ha : (tripleCharges (sourceA1596 + difference 2 0) (sourceB1596 + difference 0 2) sourceC1596) = raw23889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1596 sourceB1596 sourceC1596 difference raw23889; decide +kernel
    rw [ha]
    exact (canonical23889 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1596 + difference 3 0) (sourceB1596 + difference 0 3) sourceC1596) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 803) := by
    have ha : (tripleCharges (sourceA1596 + difference 3 0) (sourceB1596 + difference 0 3) sourceC1596) = raw23890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1596 sourceB1596 sourceC1596 difference raw23890; decide +kernel
    rw [ha]
    exact (canonical23890 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1596 + difference 4 0) (sourceB1596 + difference 0 4) sourceC1596) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 803) := by
    have ha : (tripleCharges (sourceA1596 + difference 4 0) (sourceB1596 + difference 0 4) sourceC1596) = raw23891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1596 sourceB1596 sourceC1596 difference raw23891; decide +kernel
    rw [ha]
    exact (canonical23891 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1596 + difference 5 0) (sourceB1596 + difference 0 5) sourceC1596) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 782) := by
    have ha : (tripleCharges (sourceA1596 + difference 5 0) (sourceB1596 + difference 0 5) sourceC1596) = raw23892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1596 sourceB1596 sourceC1596 difference raw23892; decide +kernel
    rw [ha]
    exact (canonical23892 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1596 + sourceB1596) sourceC1596) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1596 + sourceB1596) sourceC1596) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1596 sourceB1596 sourceC1596 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1596 sourceB1596 sourceC1596
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1596, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1597 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB1597 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC1597 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1597 : Integer.Sparse Master := [(Sum.inr 803, 1), (Sum.inr 1642, 1), (Sum.inr 1705, 1), (Sum.inr 1713, 1), (Sum.inr 1724, 2), (Sum.inr 4069, -1)]

theorem sourceEq1597 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1597 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1597 + difference 3 0) (sourceB1597 + difference 0 3) sourceC1597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 803) := by
    have ha : (tripleCharges (sourceA1597 + difference 3 0) (sourceB1597 + difference 0 3) sourceC1597) = raw23890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1597 sourceB1597 sourceC1597 difference raw23890; decide +kernel
    rw [ha]
    exact (canonical23890 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1597 + difference 3 1) (sourceB1597 + difference 1 3) sourceC1597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1597 + difference 3 1) (sourceB1597 + difference 1 3) sourceC1597) = raw23852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1597 sourceB1597 sourceC1597 difference raw23852; decide +kernel
    rw [ha]
    exact (canonical23852 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1597 + difference 3 2) (sourceB1597 + difference 2 3) sourceC1597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1597 + difference 3 2) (sourceB1597 + difference 2 3) sourceC1597) = raw23893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1597 sourceB1597 sourceC1597 difference raw23893; decide +kernel
    rw [ha]
    exact (canonical23893 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1597 + difference 3 3) (sourceB1597 + difference 3 3) sourceC1597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1597 + difference 3 3) (sourceB1597 + difference 3 3) sourceC1597) = raw23851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1597 sourceB1597 sourceC1597 difference raw23851; decide +kernel
    rw [ha]
    exact (canonical23851 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1597 + difference 3 4) (sourceB1597 + difference 4 3) sourceC1597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1642) := by
    have ha : (tripleCharges (sourceA1597 + difference 3 4) (sourceB1597 + difference 4 3) sourceC1597) = raw23894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1597 sourceB1597 sourceC1597 difference raw23894; decide +kernel
    rw [ha]
    exact (canonical23894 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1597 + difference 3 5) (sourceB1597 + difference 5 3) sourceC1597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1597 + difference 3 5) (sourceB1597 + difference 5 3) sourceC1597) = raw23895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1597 sourceB1597 sourceC1597 difference raw23895; decide +kernel
    rw [ha]
    exact (canonical23895 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1597 + sourceB1597) sourceC1597) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1597 + sourceB1597) sourceC1597) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1597 sourceB1597 sourceC1597 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1597 sourceB1597 sourceC1597
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1597, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1598 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB1598 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC1598 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1598 : Integer.Sparse Master := [(Sum.inr 782, 1), (Sum.inr 1635, 2), (Sum.inr 1705, 1), (Sum.inr 1707, 2), (Sum.inr 4069, -1)]

theorem sourceEq1598 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1598 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1598 + difference 5 0) (sourceB1598 + difference 0 5) sourceC1598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 782) := by
    have ha : (tripleCharges (sourceA1598 + difference 5 0) (sourceB1598 + difference 0 5) sourceC1598) = raw23892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1598 sourceB1598 sourceC1598 difference raw23892; decide +kernel
    rw [ha]
    exact (canonical23892 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1598 + difference 5 1) (sourceB1598 + difference 1 5) sourceC1598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1598 + difference 5 1) (sourceB1598 + difference 1 5) sourceC1598) = raw23853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1598 sourceB1598 sourceC1598 difference raw23853; decide +kernel
    rw [ha]
    exact (canonical23853 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1598 + difference 5 2) (sourceB1598 + difference 2 5) sourceC1598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1598 + difference 5 2) (sourceB1598 + difference 2 5) sourceC1598) = raw23896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1598 sourceB1598 sourceC1598 difference raw23896; decide +kernel
    rw [ha]
    exact (canonical23896 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1598 + difference 5 3) (sourceB1598 + difference 3 5) sourceC1598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1635) := by
    have ha : (tripleCharges (sourceA1598 + difference 5 3) (sourceB1598 + difference 3 5) sourceC1598) = raw23897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1598 sourceB1598 sourceC1598 difference raw23897; decide +kernel
    rw [ha]
    exact (canonical23897 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1598 + difference 5 4) (sourceB1598 + difference 4 5) sourceC1598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1635) := by
    have ha : (tripleCharges (sourceA1598 + difference 5 4) (sourceB1598 + difference 4 5) sourceC1598) = raw23898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1598 sourceB1598 sourceC1598 difference raw23898; decide +kernel
    rw [ha]
    exact (canonical23898 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1598 + difference 5 5) (sourceB1598 + difference 5 5) sourceC1598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1598 + difference 5 5) (sourceB1598 + difference 5 5) sourceC1598) = raw23851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1598 sourceB1598 sourceC1598 difference raw23851; decide +kernel
    rw [ha]
    exact (canonical23851 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1598 + sourceB1598) sourceC1598) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1598 + sourceB1598) sourceC1598) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1598 sourceB1598 sourceC1598 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1598 sourceB1598 sourceC1598
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1598, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1599 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB1599 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC1599 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1599 : Integer.Sparse Master := [(Sum.inr 1701, 2), (Sum.inr 1705, 1), (Sum.inr 1713, 2), (Sum.inr 3281, 1), (Sum.inr 4069, -1)]

theorem sourceEq1599 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1599 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1599 + difference 0 5) (sourceB1599 + difference 5 0) sourceC1599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3281) := by
    have ha : (tripleCharges (sourceA1599 + difference 0 5) (sourceB1599 + difference 5 0) sourceC1599) = raw23887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1599 sourceB1599 sourceC1599 difference raw23887; decide +kernel
    rw [ha]
    exact (canonical23887 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1599 + difference 1 5) (sourceB1599 + difference 5 1) sourceC1599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1701) := by
    have ha : (tripleCharges (sourceA1599 + difference 1 5) (sourceB1599 + difference 5 1) sourceC1599) = raw23899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1599 sourceB1599 sourceC1599 difference raw23899; decide +kernel
    rw [ha]
    exact (canonical23899 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1599 + difference 2 5) (sourceB1599 + difference 5 2) sourceC1599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1701) := by
    have ha : (tripleCharges (sourceA1599 + difference 2 5) (sourceB1599 + difference 5 2) sourceC1599) = raw23858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1599 sourceB1599 sourceC1599 difference raw23858; decide +kernel
    rw [ha]
    exact (canonical23858 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1599 + difference 3 5) (sourceB1599 + difference 5 3) sourceC1599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1599 + difference 3 5) (sourceB1599 + difference 5 3) sourceC1599) = raw23895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1599 sourceB1599 sourceC1599 difference raw23895; decide +kernel
    rw [ha]
    exact (canonical23895 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1599 + difference 4 5) (sourceB1599 + difference 5 4) sourceC1599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1599 + difference 4 5) (sourceB1599 + difference 5 4) sourceC1599) = raw23826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1599 sourceB1599 sourceC1599 difference raw23826; decide +kernel
    rw [ha]
    exact (canonical23826 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1599 + difference 5 5) (sourceB1599 + difference 5 5) sourceC1599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1599 + difference 5 5) (sourceB1599 + difference 5 5) sourceC1599) = raw23851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1599 sourceB1599 sourceC1599 difference raw23851; decide +kernel
    rw [ha]
    exact (canonical23851 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1599 + sourceB1599) sourceC1599) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1599 + sourceB1599) sourceC1599) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1599 sourceB1599 sourceC1599 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1599 sourceB1599 sourceC1599
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1599, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
