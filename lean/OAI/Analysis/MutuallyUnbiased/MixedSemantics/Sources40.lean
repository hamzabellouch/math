import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical117
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical154
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical163
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical164

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1280 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1280 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1280 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1280 : Integer.Sparse Master := [(Sum.inr 4454, 3), (Sum.inr 4464, 3), (Sum.inr 4488, 3), (Sum.inr 4493, 1), (Sum.inr 4501, 1), (Sum.inr 4507, 1), (Sum.inr 4508, 1), (Sum.inr 4509, 1), (Sum.inr 4588, 6), (Sum.inr 4605, 3), (Sum.inr 4609, 3), (Sum.inr 4610, 3), (Sum.inr 4625, 1)]

theorem sourceEq1280 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1280 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1280 + difference 0 1) (sourceB1280 + difference 1 0) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA1280 + difference 0 1) (sourceB1280 + difference 1 0) sourceC1280) = raw20568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20568; decide +kernel
    rw [ha]
    exact (canonical20568 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1280 + difference 0 2) (sourceB1280 + difference 2 0) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA1280 + difference 0 2) (sourceB1280 + difference 2 0) sourceC1280) = raw20569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20569; decide +kernel
    rw [ha]
    exact (canonical20569 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1280 + difference 0 3) (sourceB1280 + difference 3 0) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA1280 + difference 0 3) (sourceB1280 + difference 3 0) sourceC1280) = raw20570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20570; decide +kernel
    rw [ha]
    exact (canonical20570 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1280 + difference 0 4) (sourceB1280 + difference 4 0) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4508) := by
    have ha : (tripleCharges (sourceA1280 + difference 0 4) (sourceB1280 + difference 4 0) sourceC1280) = raw20571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20571; decide +kernel
    rw [ha]
    exact (canonical20571 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1280 + difference 0 5) (sourceB1280 + difference 5 0) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA1280 + difference 0 5) (sourceB1280 + difference 5 0) sourceC1280) = raw20417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20417; decide +kernel
    rw [ha]
    exact (canonical20417 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1280 + difference 1 0) (sourceB1280 + difference 0 1) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4454) := by
    have ha : (tripleCharges (sourceA1280 + difference 1 0) (sourceB1280 + difference 0 1) sourceC1280) = raw20572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20572; decide +kernel
    rw [ha]
    exact (canonical20572 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1280 + difference 1 2) (sourceB1280 + difference 2 1) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4588) := by
    have ha : (tripleCharges (sourceA1280 + difference 1 2) (sourceB1280 + difference 2 1) sourceC1280) = raw20573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20573; decide +kernel
    rw [ha]
    exact (canonical20573 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1280 + difference 1 3) (sourceB1280 + difference 3 1) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4588) := by
    have ha : (tripleCharges (sourceA1280 + difference 1 3) (sourceB1280 + difference 3 1) sourceC1280) = raw20574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20574; decide +kernel
    rw [ha]
    exact (canonical20574 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1280 + difference 1 4) (sourceB1280 + difference 4 1) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4610) := by
    have ha : (tripleCharges (sourceA1280 + difference 1 4) (sourceB1280 + difference 4 1) sourceC1280) = raw20575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20575; decide +kernel
    rw [ha]
    exact (canonical20575 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1280 + difference 1 5) (sourceB1280 + difference 5 1) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1280 + difference 1 5) (sourceB1280 + difference 5 1) sourceC1280) = raw20422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20422; decide +kernel
    rw [ha]
    exact (canonical20422 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1280 + difference 2 0) (sourceB1280 + difference 0 2) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4454) := by
    have ha : (tripleCharges (sourceA1280 + difference 2 0) (sourceB1280 + difference 0 2) sourceC1280) = raw20576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20576; decide +kernel
    rw [ha]
    exact (canonical20576 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1280 + difference 2 1) (sourceB1280 + difference 1 2) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4588) := by
    have ha : (tripleCharges (sourceA1280 + difference 2 1) (sourceB1280 + difference 1 2) sourceC1280) = raw20577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20577; decide +kernel
    rw [ha]
    exact (canonical20577 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1280 + difference 2 3) (sourceB1280 + difference 3 2) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4588) := by
    have ha : (tripleCharges (sourceA1280 + difference 2 3) (sourceB1280 + difference 3 2) sourceC1280) = raw20578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20578; decide +kernel
    rw [ha]
    exact (canonical20578 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1280 + difference 2 4) (sourceB1280 + difference 4 2) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4610) := by
    have ha : (tripleCharges (sourceA1280 + difference 2 4) (sourceB1280 + difference 4 2) sourceC1280) = raw20579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20579; decide +kernel
    rw [ha]
    exact (canonical20579 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1280 + difference 2 5) (sourceB1280 + difference 5 2) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1280 + difference 2 5) (sourceB1280 + difference 5 2) sourceC1280) = raw20427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20427; decide +kernel
    rw [ha]
    exact (canonical20427 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1280 + difference 3 0) (sourceB1280 + difference 0 3) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4454) := by
    have ha : (tripleCharges (sourceA1280 + difference 3 0) (sourceB1280 + difference 0 3) sourceC1280) = raw20580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20580; decide +kernel
    rw [ha]
    exact (canonical20580 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1280 + difference 3 1) (sourceB1280 + difference 1 3) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4588) := by
    have ha : (tripleCharges (sourceA1280 + difference 3 1) (sourceB1280 + difference 1 3) sourceC1280) = raw20581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20581; decide +kernel
    rw [ha]
    exact (canonical20581 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1280 + difference 3 2) (sourceB1280 + difference 2 3) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4588) := by
    have ha : (tripleCharges (sourceA1280 + difference 3 2) (sourceB1280 + difference 2 3) sourceC1280) = raw20582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20582; decide +kernel
    rw [ha]
    exact (canonical20582 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1280 + difference 3 4) (sourceB1280 + difference 4 3) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4610) := by
    have ha : (tripleCharges (sourceA1280 + difference 3 4) (sourceB1280 + difference 4 3) sourceC1280) = raw20583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20583; decide +kernel
    rw [ha]
    exact (canonical20583 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1280 + difference 3 5) (sourceB1280 + difference 5 3) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1280 + difference 3 5) (sourceB1280 + difference 5 3) sourceC1280) = raw20432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20432; decide +kernel
    rw [ha]
    exact (canonical20432 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1280 + difference 4 0) (sourceB1280 + difference 0 4) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1280 + difference 4 0) (sourceB1280 + difference 0 4) sourceC1280) = raw20439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20439; decide +kernel
    rw [ha]
    exact (canonical20439 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1280 + difference 4 1) (sourceB1280 + difference 1 4) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1280 + difference 4 1) (sourceB1280 + difference 1 4) sourceC1280) = raw20440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20440; decide +kernel
    rw [ha]
    exact (canonical20440 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1280 + difference 4 2) (sourceB1280 + difference 2 4) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1280 + difference 4 2) (sourceB1280 + difference 2 4) sourceC1280) = raw20441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20441; decide +kernel
    rw [ha]
    exact (canonical20441 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1280 + difference 4 3) (sourceB1280 + difference 3 4) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1280 + difference 4 3) (sourceB1280 + difference 3 4) sourceC1280) = raw20442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20442; decide +kernel
    rw [ha]
    exact (canonical20442 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1280 + difference 4 5) (sourceB1280 + difference 5 4) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1280 + difference 4 5) (sourceB1280 + difference 5 4) sourceC1280) = raw20584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20584; decide +kernel
    rw [ha]
    exact (canonical20584 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1280 + difference 5 0) (sourceB1280 + difference 0 5) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4493) := by
    have ha : (tripleCharges (sourceA1280 + difference 5 0) (sourceB1280 + difference 0 5) sourceC1280) = raw20585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20585; decide +kernel
    rw [ha]
    exact (canonical20585 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1280 + difference 5 1) (sourceB1280 + difference 1 5) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4488) := by
    have ha : (tripleCharges (sourceA1280 + difference 5 1) (sourceB1280 + difference 1 5) sourceC1280) = raw20586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20586; decide +kernel
    rw [ha]
    exact (canonical20586 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1280 + difference 5 2) (sourceB1280 + difference 2 5) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4488) := by
    have ha : (tripleCharges (sourceA1280 + difference 5 2) (sourceB1280 + difference 2 5) sourceC1280) = raw20587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20587; decide +kernel
    rw [ha]
    exact (canonical20587 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1280 + difference 5 3) (sourceB1280 + difference 3 5) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4488) := by
    have ha : (tripleCharges (sourceA1280 + difference 5 3) (sourceB1280 + difference 3 5) sourceC1280) = raw20588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20588; decide +kernel
    rw [ha]
    exact (canonical20588 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1280 + difference 5 4) (sourceB1280 + difference 4 5) sourceC1280) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4509) := by
    have ha : (tripleCharges (sourceA1280 + difference 5 4) (sourceB1280 + difference 4 5) sourceC1280) = raw20589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1280 sourceB1280 sourceC1280 difference raw20589; decide +kernel
    rw [ha]
    exact (canonical20589 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1280 sourceB1280 sourceC1280
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1280, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1281 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1281 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1281 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1281 : Integer.Sparse Master := [(Sum.inr 1037, 3), (Sum.inr 1077, 1), (Sum.inr 1085, 1), (Sum.inr 1211, 6), (Sum.inr 1231, 3), (Sum.inr 1239, 3), (Sum.inr 1258, 3), (Sum.inr 1264, 3), (Sum.inr 1289, 1), (Sum.inr 1304, 1), (Sum.inr 1408, 3), (Sum.inr 1438, 1), (Sum.inr 1445, 1)]

theorem sourceEq1281 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1281 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1281 + difference 0 1) (sourceB1281 + difference 1 0) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA1281 + difference 0 1) (sourceB1281 + difference 1 0) sourceC1281) = raw20590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20590; decide +kernel
    rw [ha]
    exact (canonical20590 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1281 + difference 0 2) (sourceB1281 + difference 2 0) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA1281 + difference 0 2) (sourceB1281 + difference 2 0) sourceC1281) = raw20591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20591; decide +kernel
    rw [ha]
    exact (canonical20591 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1281 + difference 0 3) (sourceB1281 + difference 3 0) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA1281 + difference 0 3) (sourceB1281 + difference 3 0) sourceC1281) = raw20592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20592; decide +kernel
    rw [ha]
    exact (canonical20592 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1281 + difference 0 4) (sourceB1281 + difference 4 0) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1438) := by
    have ha : (tripleCharges (sourceA1281 + difference 0 4) (sourceB1281 + difference 4 0) sourceC1281) = raw20593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20593; decide +kernel
    rw [ha]
    exact (canonical20593 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1281 + difference 0 5) (sourceB1281 + difference 5 0) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1445) := by
    have ha : (tripleCharges (sourceA1281 + difference 0 5) (sourceB1281 + difference 5 0) sourceC1281) = raw20594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20594; decide +kernel
    rw [ha]
    exact (canonical20594 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1281 + difference 1 0) (sourceB1281 + difference 0 1) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1037) := by
    have ha : (tripleCharges (sourceA1281 + difference 1 0) (sourceB1281 + difference 0 1) sourceC1281) = raw20595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20595; decide +kernel
    rw [ha]
    exact (canonical20595 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1281 + difference 1 2) (sourceB1281 + difference 2 1) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1211) := by
    have ha : (tripleCharges (sourceA1281 + difference 1 2) (sourceB1281 + difference 2 1) sourceC1281) = raw20596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20596; decide +kernel
    rw [ha]
    exact (canonical20596 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1281 + difference 1 3) (sourceB1281 + difference 3 1) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1211) := by
    have ha : (tripleCharges (sourceA1281 + difference 1 3) (sourceB1281 + difference 3 1) sourceC1281) = raw20597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20597; decide +kernel
    rw [ha]
    exact (canonical20597 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1281 + difference 1 4) (sourceB1281 + difference 4 1) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1258) := by
    have ha : (tripleCharges (sourceA1281 + difference 1 4) (sourceB1281 + difference 4 1) sourceC1281) = raw20598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20598; decide +kernel
    rw [ha]
    exact (canonical20598 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1281 + difference 1 5) (sourceB1281 + difference 5 1) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1264) := by
    have ha : (tripleCharges (sourceA1281 + difference 1 5) (sourceB1281 + difference 5 1) sourceC1281) = raw20599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20599; decide +kernel
    rw [ha]
    exact (canonical20599 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1281 + difference 2 0) (sourceB1281 + difference 0 2) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1037) := by
    have ha : (tripleCharges (sourceA1281 + difference 2 0) (sourceB1281 + difference 0 2) sourceC1281) = raw20600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20600; decide +kernel
    rw [ha]
    exact (canonical20600 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1281 + difference 2 1) (sourceB1281 + difference 1 2) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1211) := by
    have ha : (tripleCharges (sourceA1281 + difference 2 1) (sourceB1281 + difference 1 2) sourceC1281) = raw20601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20601; decide +kernel
    rw [ha]
    exact (canonical20601 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1281 + difference 2 3) (sourceB1281 + difference 3 2) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1211) := by
    have ha : (tripleCharges (sourceA1281 + difference 2 3) (sourceB1281 + difference 3 2) sourceC1281) = raw20602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20602; decide +kernel
    rw [ha]
    exact (canonical20602 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1281 + difference 2 4) (sourceB1281 + difference 4 2) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1258) := by
    have ha : (tripleCharges (sourceA1281 + difference 2 4) (sourceB1281 + difference 4 2) sourceC1281) = raw20603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20603; decide +kernel
    rw [ha]
    exact (canonical20603 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1281 + difference 2 5) (sourceB1281 + difference 5 2) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1264) := by
    have ha : (tripleCharges (sourceA1281 + difference 2 5) (sourceB1281 + difference 5 2) sourceC1281) = raw20604 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20604; decide +kernel
    rw [ha]
    exact (canonical20604 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1281 + difference 3 0) (sourceB1281 + difference 0 3) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1037) := by
    have ha : (tripleCharges (sourceA1281 + difference 3 0) (sourceB1281 + difference 0 3) sourceC1281) = raw20605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20605; decide +kernel
    rw [ha]
    exact (canonical20605 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1281 + difference 3 1) (sourceB1281 + difference 1 3) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1211) := by
    have ha : (tripleCharges (sourceA1281 + difference 3 1) (sourceB1281 + difference 1 3) sourceC1281) = raw20606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20606; decide +kernel
    rw [ha]
    exact (canonical20606 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1281 + difference 3 2) (sourceB1281 + difference 2 3) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1211) := by
    have ha : (tripleCharges (sourceA1281 + difference 3 2) (sourceB1281 + difference 2 3) sourceC1281) = raw20607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20607; decide +kernel
    rw [ha]
    exact (canonical20607 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1281 + difference 3 4) (sourceB1281 + difference 4 3) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1258) := by
    have ha : (tripleCharges (sourceA1281 + difference 3 4) (sourceB1281 + difference 4 3) sourceC1281) = raw20608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20608; decide +kernel
    rw [ha]
    exact (canonical20608 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1281 + difference 3 5) (sourceB1281 + difference 5 3) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1264) := by
    have ha : (tripleCharges (sourceA1281 + difference 3 5) (sourceB1281 + difference 5 3) sourceC1281) = raw20609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20609; decide +kernel
    rw [ha]
    exact (canonical20609 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1281 + difference 4 0) (sourceB1281 + difference 0 4) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1085) := by
    have ha : (tripleCharges (sourceA1281 + difference 4 0) (sourceB1281 + difference 0 4) sourceC1281) = raw20610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20610; decide +kernel
    rw [ha]
    exact (canonical20610 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1281 + difference 4 1) (sourceB1281 + difference 1 4) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1281 + difference 4 1) (sourceB1281 + difference 1 4) sourceC1281) = raw20611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20611; decide +kernel
    rw [ha]
    exact (canonical20611 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1281 + difference 4 2) (sourceB1281 + difference 2 4) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1281 + difference 4 2) (sourceB1281 + difference 2 4) sourceC1281) = raw20612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20612; decide +kernel
    rw [ha]
    exact (canonical20612 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1281 + difference 4 3) (sourceB1281 + difference 3 4) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1281 + difference 4 3) (sourceB1281 + difference 3 4) sourceC1281) = raw20613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20613; decide +kernel
    rw [ha]
    exact (canonical20613 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1281 + difference 4 5) (sourceB1281 + difference 5 4) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1304) := by
    have ha : (tripleCharges (sourceA1281 + difference 4 5) (sourceB1281 + difference 5 4) sourceC1281) = raw20614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20614; decide +kernel
    rw [ha]
    exact (canonical20614 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1281 + difference 5 0) (sourceB1281 + difference 0 5) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1077) := by
    have ha : (tripleCharges (sourceA1281 + difference 5 0) (sourceB1281 + difference 0 5) sourceC1281) = raw20615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20615; decide +kernel
    rw [ha]
    exact (canonical20615 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1281 + difference 5 1) (sourceB1281 + difference 1 5) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1231) := by
    have ha : (tripleCharges (sourceA1281 + difference 5 1) (sourceB1281 + difference 1 5) sourceC1281) = raw20616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20616; decide +kernel
    rw [ha]
    exact (canonical20616 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1281 + difference 5 2) (sourceB1281 + difference 2 5) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1231) := by
    have ha : (tripleCharges (sourceA1281 + difference 5 2) (sourceB1281 + difference 2 5) sourceC1281) = raw20617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20617; decide +kernel
    rw [ha]
    exact (canonical20617 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1281 + difference 5 3) (sourceB1281 + difference 3 5) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1231) := by
    have ha : (tripleCharges (sourceA1281 + difference 5 3) (sourceB1281 + difference 3 5) sourceC1281) = raw20618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20618; decide +kernel
    rw [ha]
    exact (canonical20618 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1281 + difference 5 4) (sourceB1281 + difference 4 5) sourceC1281) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1289) := by
    have ha : (tripleCharges (sourceA1281 + difference 5 4) (sourceB1281 + difference 4 5) sourceC1281) = raw20619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1281 sourceB1281 sourceC1281 difference raw20619; decide +kernel
    rw [ha]
    exact (canonical20619 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1281 sourceB1281 sourceC1281
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1281, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1282 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1282 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1282 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1282 : Integer.Sparse Master := [(Sum.inr 1047, 3), (Sum.inr 1091, 1), (Sum.inr 1092, 1), (Sum.inr 1218, 6), (Sum.inr 1243, 3), (Sum.inr 1244, 3), (Sum.inr 1271, 3), (Sum.inr 1272, 3), (Sum.inr 1307, 1), (Sum.inr 1309, 1), (Sum.inr 1417, 3), (Sum.inr 1452, 1), (Sum.inr 1453, 1)]

theorem sourceEq1282 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1282 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1282 + difference 0 1) (sourceB1282 + difference 1 0) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA1282 + difference 0 1) (sourceB1282 + difference 1 0) sourceC1282) = raw20620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20620; decide +kernel
    rw [ha]
    exact (canonical20620 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1282 + difference 0 2) (sourceB1282 + difference 2 0) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA1282 + difference 0 2) (sourceB1282 + difference 2 0) sourceC1282) = raw20621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20621; decide +kernel
    rw [ha]
    exact (canonical20621 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1282 + difference 0 3) (sourceB1282 + difference 3 0) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA1282 + difference 0 3) (sourceB1282 + difference 3 0) sourceC1282) = raw20622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20622; decide +kernel
    rw [ha]
    exact (canonical20622 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1282 + difference 0 4) (sourceB1282 + difference 4 0) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1092) := by
    have ha : (tripleCharges (sourceA1282 + difference 0 4) (sourceB1282 + difference 4 0) sourceC1282) = raw20623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20623; decide +kernel
    rw [ha]
    exact (canonical20623 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1282 + difference 0 5) (sourceB1282 + difference 5 0) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA1282 + difference 0 5) (sourceB1282 + difference 5 0) sourceC1282) = raw20447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20447; decide +kernel
    rw [ha]
    exact (canonical20447 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1282 + difference 1 0) (sourceB1282 + difference 0 1) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1417) := by
    have ha : (tripleCharges (sourceA1282 + difference 1 0) (sourceB1282 + difference 0 1) sourceC1282) = raw20624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20624; decide +kernel
    rw [ha]
    exact (canonical20624 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1282 + difference 1 2) (sourceB1282 + difference 2 1) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA1282 + difference 1 2) (sourceB1282 + difference 2 1) sourceC1282) = raw20625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20625; decide +kernel
    rw [ha]
    exact (canonical20625 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1282 + difference 1 3) (sourceB1282 + difference 3 1) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA1282 + difference 1 3) (sourceB1282 + difference 3 1) sourceC1282) = raw20626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20626; decide +kernel
    rw [ha]
    exact (canonical20626 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1282 + difference 1 4) (sourceB1282 + difference 4 1) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1244) := by
    have ha : (tripleCharges (sourceA1282 + difference 1 4) (sourceB1282 + difference 4 1) sourceC1282) = raw20627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20627; decide +kernel
    rw [ha]
    exact (canonical20627 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1282 + difference 1 5) (sourceB1282 + difference 5 1) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1282 + difference 1 5) (sourceB1282 + difference 5 1) sourceC1282) = raw20452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20452; decide +kernel
    rw [ha]
    exact (canonical20452 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1282 + difference 2 0) (sourceB1282 + difference 0 2) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1417) := by
    have ha : (tripleCharges (sourceA1282 + difference 2 0) (sourceB1282 + difference 0 2) sourceC1282) = raw20628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20628; decide +kernel
    rw [ha]
    exact (canonical20628 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1282 + difference 2 1) (sourceB1282 + difference 1 2) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA1282 + difference 2 1) (sourceB1282 + difference 1 2) sourceC1282) = raw20629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20629; decide +kernel
    rw [ha]
    exact (canonical20629 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1282 + difference 2 3) (sourceB1282 + difference 3 2) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA1282 + difference 2 3) (sourceB1282 + difference 3 2) sourceC1282) = raw20630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20630; decide +kernel
    rw [ha]
    exact (canonical20630 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1282 + difference 2 4) (sourceB1282 + difference 4 2) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1244) := by
    have ha : (tripleCharges (sourceA1282 + difference 2 4) (sourceB1282 + difference 4 2) sourceC1282) = raw20631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20631; decide +kernel
    rw [ha]
    exact (canonical20631 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1282 + difference 2 5) (sourceB1282 + difference 5 2) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1282 + difference 2 5) (sourceB1282 + difference 5 2) sourceC1282) = raw20457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20457; decide +kernel
    rw [ha]
    exact (canonical20457 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1282 + difference 3 0) (sourceB1282 + difference 0 3) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1417) := by
    have ha : (tripleCharges (sourceA1282 + difference 3 0) (sourceB1282 + difference 0 3) sourceC1282) = raw20632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20632; decide +kernel
    rw [ha]
    exact (canonical20632 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1282 + difference 3 1) (sourceB1282 + difference 1 3) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA1282 + difference 3 1) (sourceB1282 + difference 1 3) sourceC1282) = raw20633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20633; decide +kernel
    rw [ha]
    exact (canonical20633 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1282 + difference 3 2) (sourceB1282 + difference 2 3) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA1282 + difference 3 2) (sourceB1282 + difference 2 3) sourceC1282) = raw20634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20634; decide +kernel
    rw [ha]
    exact (canonical20634 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1282 + difference 3 4) (sourceB1282 + difference 4 3) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1244) := by
    have ha : (tripleCharges (sourceA1282 + difference 3 4) (sourceB1282 + difference 4 3) sourceC1282) = raw20635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20635; decide +kernel
    rw [ha]
    exact (canonical20635 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1282 + difference 3 5) (sourceB1282 + difference 5 3) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1282 + difference 3 5) (sourceB1282 + difference 5 3) sourceC1282) = raw20462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20462; decide +kernel
    rw [ha]
    exact (canonical20462 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1282 + difference 4 0) (sourceB1282 + difference 0 4) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1452) := by
    have ha : (tripleCharges (sourceA1282 + difference 4 0) (sourceB1282 + difference 0 4) sourceC1282) = raw20469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20469; decide +kernel
    rw [ha]
    exact (canonical20469 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1282 + difference 4 1) (sourceB1282 + difference 1 4) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1282 + difference 4 1) (sourceB1282 + difference 1 4) sourceC1282) = raw20470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20470; decide +kernel
    rw [ha]
    exact (canonical20470 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1282 + difference 4 2) (sourceB1282 + difference 2 4) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1282 + difference 4 2) (sourceB1282 + difference 2 4) sourceC1282) = raw20471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20471; decide +kernel
    rw [ha]
    exact (canonical20471 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1282 + difference 4 3) (sourceB1282 + difference 3 4) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1282 + difference 4 3) (sourceB1282 + difference 3 4) sourceC1282) = raw20472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20472; decide +kernel
    rw [ha]
    exact (canonical20472 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1282 + difference 4 5) (sourceB1282 + difference 5 4) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1282 + difference 4 5) (sourceB1282 + difference 5 4) sourceC1282) = raw20636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20636; decide +kernel
    rw [ha]
    exact (canonical20636 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1282 + difference 5 0) (sourceB1282 + difference 0 5) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1453) := by
    have ha : (tripleCharges (sourceA1282 + difference 5 0) (sourceB1282 + difference 0 5) sourceC1282) = raw20637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20637; decide +kernel
    rw [ha]
    exact (canonical20637 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1282 + difference 5 1) (sourceB1282 + difference 1 5) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1272) := by
    have ha : (tripleCharges (sourceA1282 + difference 5 1) (sourceB1282 + difference 1 5) sourceC1282) = raw20638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20638; decide +kernel
    rw [ha]
    exact (canonical20638 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1282 + difference 5 2) (sourceB1282 + difference 2 5) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1272) := by
    have ha : (tripleCharges (sourceA1282 + difference 5 2) (sourceB1282 + difference 2 5) sourceC1282) = raw20639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20639; decide +kernel
    rw [ha]
    exact (canonical20639 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1282 + difference 5 3) (sourceB1282 + difference 3 5) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1272) := by
    have ha : (tripleCharges (sourceA1282 + difference 5 3) (sourceB1282 + difference 3 5) sourceC1282) = raw20640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20640; decide +kernel
    rw [ha]
    exact (canonical20640 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1282 + difference 5 4) (sourceB1282 + difference 4 5) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1309) := by
    have ha : (tripleCharges (sourceA1282 + difference 5 4) (sourceB1282 + difference 4 5) sourceC1282) = raw20641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20641; decide +kernel
    rw [ha]
    exact (canonical20641 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1282 sourceB1282 sourceC1282
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1282, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1283 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1283 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1283 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1283 : Integer.Sparse Master := [(Sum.inr 1077, 1), (Sum.inr 1647, 3), (Sum.inr 1730, 1), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

theorem sourceEq1283 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1283 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1283 + difference 0 0) (sourceB1283 + difference 0 0) sourceC1283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA1283 + difference 0 0) (sourceB1283 + difference 0 0) sourceC1283) = raw20642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1283 sourceB1283 sourceC1283 difference raw20642; decide +kernel
    rw [ha]
    exact (canonical20642 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1283 + difference 1 0) (sourceB1283 + difference 0 1) sourceC1283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1647) := by
    have ha : (tripleCharges (sourceA1283 + difference 1 0) (sourceB1283 + difference 0 1) sourceC1283) = raw20643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1283 sourceB1283 sourceC1283 difference raw20643; decide +kernel
    rw [ha]
    exact (canonical20643 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1283 + difference 2 0) (sourceB1283 + difference 0 2) sourceC1283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1647) := by
    have ha : (tripleCharges (sourceA1283 + difference 2 0) (sourceB1283 + difference 0 2) sourceC1283) = raw20644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1283 sourceB1283 sourceC1283 difference raw20644; decide +kernel
    rw [ha]
    exact (canonical20644 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1283 + difference 3 0) (sourceB1283 + difference 0 3) sourceC1283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1647) := by
    have ha : (tripleCharges (sourceA1283 + difference 3 0) (sourceB1283 + difference 0 3) sourceC1283) = raw20645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1283 sourceB1283 sourceC1283 difference raw20645; decide +kernel
    rw [ha]
    exact (canonical20645 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1283 + difference 4 0) (sourceB1283 + difference 0 4) sourceC1283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1283 + difference 4 0) (sourceB1283 + difference 0 4) sourceC1283) = raw20480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1283 sourceB1283 sourceC1283 difference raw20480; decide +kernel
    rw [ha]
    exact (canonical20480 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1283 + difference 5 0) (sourceB1283 + difference 0 5) sourceC1283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1077) := by
    have ha : (tripleCharges (sourceA1283 + difference 5 0) (sourceB1283 + difference 0 5) sourceC1283) = raw20646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1283 sourceB1283 sourceC1283 difference raw20646; decide +kernel
    rw [ha]
    exact (canonical20646 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1283 + sourceB1283) sourceC1283) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1283 + sourceB1283) sourceC1283) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1283 sourceB1283 sourceC1283 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1283 sourceB1283 sourceC1283
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1283, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1284 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1284 : Charge := ![2, 0, 0, 0, -3, 1]
def sourceC1284 : Charge := ![2, 0, 0, 0, 2, -4]
def sourceForm1284 : Integer.Sparse Master := [(Sum.inr 1289, 1), (Sum.inr 1657, 3), (Sum.inr 1741, 1), (Sum.inr 2780, 1), (Sum.inr 4071, -1)]

theorem sourceEq1284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1284 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1284 + difference 0 0) (sourceB1284 + difference 0 0) sourceC1284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1289) := by
    have ha : (tripleCharges (sourceA1284 + difference 0 0) (sourceB1284 + difference 0 0) sourceC1284) = raw19844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1284 sourceB1284 sourceC1284 difference raw19844; decide +kernel
    rw [ha]
    exact (canonical19844 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1284 + difference 0 1) (sourceB1284 + difference 1 0) sourceC1284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1657) := by
    have ha : (tripleCharges (sourceA1284 + difference 0 1) (sourceB1284 + difference 1 0) sourceC1284) = raw20647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1284 sourceB1284 sourceC1284 difference raw20647; decide +kernel
    rw [ha]
    exact (canonical20647 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1284 + difference 0 2) (sourceB1284 + difference 2 0) sourceC1284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1657) := by
    have ha : (tripleCharges (sourceA1284 + difference 0 2) (sourceB1284 + difference 2 0) sourceC1284) = raw20648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1284 sourceB1284 sourceC1284 difference raw20648; decide +kernel
    rw [ha]
    exact (canonical20648 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1284 + difference 0 3) (sourceB1284 + difference 3 0) sourceC1284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1657) := by
    have ha : (tripleCharges (sourceA1284 + difference 0 3) (sourceB1284 + difference 3 0) sourceC1284) = raw20649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1284 sourceB1284 sourceC1284 difference raw20649; decide +kernel
    rw [ha]
    exact (canonical20649 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1284 + difference 0 4) (sourceB1284 + difference 4 0) sourceC1284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1284 + difference 0 4) (sourceB1284 + difference 4 0) sourceC1284) = raw19835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1284 sourceB1284 sourceC1284 difference raw19835; decide +kernel
    rw [ha]
    exact (canonical19835 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1284 + difference 0 5) (sourceB1284 + difference 5 0) sourceC1284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2780) := by
    have ha : (tripleCharges (sourceA1284 + difference 0 5) (sourceB1284 + difference 5 0) sourceC1284) = raw20650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1284 sourceB1284 sourceC1284 difference raw20650; decide +kernel
    rw [ha]
    exact (canonical20650 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1284 + sourceB1284) sourceC1284) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1284 + sourceB1284) sourceC1284) = raw19836 := by
      apply Matrix.ext; unfold doubleCharges sourceA1284 sourceB1284 sourceC1284 raw19836; decide +kernel
    rw [ha]
    exact (canonical19836 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1284 sourceB1284 sourceC1284
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1284, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1285 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1285 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1285 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceForm1285 : Integer.Sparse Master := [(Sum.inr 4153, 2), (Sum.inr 4156, 1), (Sum.inr 4161, 1), (Sum.inr 4178, 1), (Sum.inr 4528, 2), (Sum.inr 4531, 2), (Sum.inr 4535, 2), (Sum.inr 4546, 2), (Sum.inr 4547, 2), (Sum.inr 4555, 1), (Sum.inr 4558, 1), (Sum.inr 4591, 2), (Sum.inr 4594, 1), (Sum.inr 4602, 2), (Sum.inr 4609, 1), (Sum.inr 4612, 1), (Sum.inr 4619, 1), (Sum.inr 5075, 2), (Sum.inr 5107, 1), (Sum.inr 5261, 1), (Sum.inr 5274, 1)]

theorem sourceEq1285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1285 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1285 + difference 0 1) (sourceB1285 + difference 1 0) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1285 + difference 0 1) (sourceB1285 + difference 1 0) sourceC1285) = raw10565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10565; decide +kernel
    rw [ha]
    exact (canonical10565 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1285 + difference 0 2) (sourceB1285 + difference 2 0) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1285 + difference 0 2) (sourceB1285 + difference 2 0) sourceC1285) = raw10566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10566; decide +kernel
    rw [ha]
    exact (canonical10566 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1285 + difference 0 3) (sourceB1285 + difference 3 0) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA1285 + difference 0 3) (sourceB1285 + difference 3 0) sourceC1285) = raw10567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10567; decide +kernel
    rw [ha]
    exact (canonical10567 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1285 + difference 0 4) (sourceB1285 + difference 4 0) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA1285 + difference 0 4) (sourceB1285 + difference 4 0) sourceC1285) = raw10568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10568; decide +kernel
    rw [ha]
    exact (canonical10568 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1285 + difference 0 5) (sourceB1285 + difference 5 0) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA1285 + difference 0 5) (sourceB1285 + difference 5 0) sourceC1285) = raw18318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw18318; decide +kernel
    rw [ha]
    exact (canonical18318 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1285 + difference 1 0) (sourceB1285 + difference 0 1) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4153) := by
    have ha : (tripleCharges (sourceA1285 + difference 1 0) (sourceB1285 + difference 0 1) sourceC1285) = raw20651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20651; decide +kernel
    rw [ha]
    exact (canonical20651 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1285 + difference 1 2) (sourceB1285 + difference 2 1) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4528) := by
    have ha : (tripleCharges (sourceA1285 + difference 1 2) (sourceB1285 + difference 2 1) sourceC1285) = raw20652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20652; decide +kernel
    rw [ha]
    exact (canonical20652 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1285 + difference 1 3) (sourceB1285 + difference 3 1) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1285 + difference 1 3) (sourceB1285 + difference 3 1) sourceC1285) = raw20653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20653; decide +kernel
    rw [ha]
    exact (canonical20653 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1285 + difference 1 4) (sourceB1285 + difference 4 1) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1285 + difference 1 4) (sourceB1285 + difference 4 1) sourceC1285) = raw20654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20654; decide +kernel
    rw [ha]
    exact (canonical20654 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1285 + difference 1 5) (sourceB1285 + difference 5 1) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1285 + difference 1 5) (sourceB1285 + difference 5 1) sourceC1285) = raw10544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10544; decide +kernel
    rw [ha]
    exact (canonical10544 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1285 + difference 2 0) (sourceB1285 + difference 0 2) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4153) := by
    have ha : (tripleCharges (sourceA1285 + difference 2 0) (sourceB1285 + difference 0 2) sourceC1285) = raw20655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20655; decide +kernel
    rw [ha]
    exact (canonical20655 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1285 + difference 2 1) (sourceB1285 + difference 1 2) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4528) := by
    have ha : (tripleCharges (sourceA1285 + difference 2 1) (sourceB1285 + difference 1 2) sourceC1285) = raw20656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20656; decide +kernel
    rw [ha]
    exact (canonical20656 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1285 + difference 2 3) (sourceB1285 + difference 3 2) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1285 + difference 2 3) (sourceB1285 + difference 3 2) sourceC1285) = raw20657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20657; decide +kernel
    rw [ha]
    exact (canonical20657 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1285 + difference 2 4) (sourceB1285 + difference 4 2) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1285 + difference 2 4) (sourceB1285 + difference 4 2) sourceC1285) = raw20658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20658; decide +kernel
    rw [ha]
    exact (canonical20658 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1285 + difference 2 5) (sourceB1285 + difference 5 2) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1285 + difference 2 5) (sourceB1285 + difference 5 2) sourceC1285) = raw10549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10549; decide +kernel
    rw [ha]
    exact (canonical10549 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1285 + difference 3 0) (sourceB1285 + difference 0 3) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4178) := by
    have ha : (tripleCharges (sourceA1285 + difference 3 0) (sourceB1285 + difference 0 3) sourceC1285) = raw20659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20659; decide +kernel
    rw [ha]
    exact (canonical20659 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1285 + difference 3 1) (sourceB1285 + difference 1 3) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4547) := by
    have ha : (tripleCharges (sourceA1285 + difference 3 1) (sourceB1285 + difference 1 3) sourceC1285) = raw20660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20660; decide +kernel
    rw [ha]
    exact (canonical20660 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1285 + difference 3 2) (sourceB1285 + difference 2 3) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4547) := by
    have ha : (tripleCharges (sourceA1285 + difference 3 2) (sourceB1285 + difference 2 3) sourceC1285) = raw20661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20661; decide +kernel
    rw [ha]
    exact (canonical20661 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1285 + difference 3 4) (sourceB1285 + difference 4 3) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1285 + difference 3 4) (sourceB1285 + difference 4 3) sourceC1285) = raw20662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20662; decide +kernel
    rw [ha]
    exact (canonical20662 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1285 + difference 3 5) (sourceB1285 + difference 5 3) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1285 + difference 3 5) (sourceB1285 + difference 5 3) sourceC1285) = raw10554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10554; decide +kernel
    rw [ha]
    exact (canonical10554 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1285 + difference 4 0) (sourceB1285 + difference 0 4) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4161) := by
    have ha : (tripleCharges (sourceA1285 + difference 4 0) (sourceB1285 + difference 0 4) sourceC1285) = raw20663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20663; decide +kernel
    rw [ha]
    exact (canonical20663 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1285 + difference 4 1) (sourceB1285 + difference 1 4) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA1285 + difference 4 1) (sourceB1285 + difference 1 4) sourceC1285) = raw20664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20664; decide +kernel
    rw [ha]
    exact (canonical20664 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1285 + difference 4 2) (sourceB1285 + difference 2 4) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA1285 + difference 4 2) (sourceB1285 + difference 2 4) sourceC1285) = raw20665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20665; decide +kernel
    rw [ha]
    exact (canonical20665 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1285 + difference 4 3) (sourceB1285 + difference 3 4) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1285 + difference 4 3) (sourceB1285 + difference 3 4) sourceC1285) = raw20666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20666; decide +kernel
    rw [ha]
    exact (canonical20666 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1285 + difference 4 5) (sourceB1285 + difference 5 4) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1285 + difference 4 5) (sourceB1285 + difference 5 4) sourceC1285) = raw10559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10559; decide +kernel
    rw [ha]
    exact (canonical10559 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1285 + difference 5 0) (sourceB1285 + difference 0 5) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4156) := by
    have ha : (tripleCharges (sourceA1285 + difference 5 0) (sourceB1285 + difference 0 5) sourceC1285) = raw20667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20667; decide +kernel
    rw [ha]
    exact (canonical20667 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1285 + difference 5 1) (sourceB1285 + difference 1 5) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4531) := by
    have ha : (tripleCharges (sourceA1285 + difference 5 1) (sourceB1285 + difference 1 5) sourceC1285) = raw20668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20668; decide +kernel
    rw [ha]
    exact (canonical20668 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1285 + difference 5 2) (sourceB1285 + difference 2 5) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4531) := by
    have ha : (tripleCharges (sourceA1285 + difference 5 2) (sourceB1285 + difference 2 5) sourceC1285) = raw20669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20669; decide +kernel
    rw [ha]
    exact (canonical20669 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1285 + difference 5 3) (sourceB1285 + difference 3 5) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1285 + difference 5 3) (sourceB1285 + difference 3 5) sourceC1285) = raw20670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20670; decide +kernel
    rw [ha]
    exact (canonical20670 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1285 + difference 5 4) (sourceB1285 + difference 4 5) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1285 + difference 5 4) (sourceB1285 + difference 4 5) sourceC1285) = raw20671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20671; decide +kernel
    rw [ha]
    exact (canonical20671 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1285 sourceB1285 sourceC1285
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1285, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1286 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1286 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1286 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceForm1286 : Integer.Sparse Master := [(Sum.inr 581, 2), (Sum.inr 584, 1), (Sum.inr 589, 1), (Sum.inr 606, 1), (Sum.inr 1112, 2), (Sum.inr 1115, 2), (Sum.inr 1120, 2), (Sum.inr 1132, 2), (Sum.inr 1165, 2), (Sum.inr 1168, 1), (Sum.inr 1176, 1), (Sum.inr 1217, 2), (Sum.inr 1221, 1), (Sum.inr 1243, 1), (Sum.inr 1267, 2), (Sum.inr 1274, 1), (Sum.inr 1302, 1), (Sum.inr 2939, 2), (Sum.inr 3002, 1), (Sum.inr 3090, 1), (Sum.inr 3112, 1)]

theorem sourceEq1286 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1286 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1286 + difference 0 1) (sourceB1286 + difference 1 0) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2939) := by
    have ha : (tripleCharges (sourceA1286 + difference 0 1) (sourceB1286 + difference 1 0) sourceC1286) = raw20672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20672; decide +kernel
    rw [ha]
    exact (canonical20672 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1286 + difference 0 2) (sourceB1286 + difference 2 0) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2939) := by
    have ha : (tripleCharges (sourceA1286 + difference 0 2) (sourceB1286 + difference 2 0) sourceC1286) = raw20673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20673; decide +kernel
    rw [ha]
    exact (canonical20673 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1286 + difference 0 3) (sourceB1286 + difference 3 0) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3002) := by
    have ha : (tripleCharges (sourceA1286 + difference 0 3) (sourceB1286 + difference 3 0) sourceC1286) = raw20674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20674; decide +kernel
    rw [ha]
    exact (canonical20674 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1286 + difference 0 4) (sourceB1286 + difference 4 0) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA1286 + difference 0 4) (sourceB1286 + difference 4 0) sourceC1286) = raw20675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20675; decide +kernel
    rw [ha]
    exact (canonical20675 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1286 + difference 0 5) (sourceB1286 + difference 5 0) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA1286 + difference 0 5) (sourceB1286 + difference 5 0) sourceC1286) = raw20676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20676; decide +kernel
    rw [ha]
    exact (canonical20676 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1286 + difference 1 0) (sourceB1286 + difference 0 1) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 581) := by
    have ha : (tripleCharges (sourceA1286 + difference 1 0) (sourceB1286 + difference 0 1) sourceC1286) = raw20677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20677; decide +kernel
    rw [ha]
    exact (canonical20677 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1286 + difference 1 2) (sourceB1286 + difference 2 1) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1112) := by
    have ha : (tripleCharges (sourceA1286 + difference 1 2) (sourceB1286 + difference 2 1) sourceC1286) = raw20678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20678; decide +kernel
    rw [ha]
    exact (canonical20678 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1286 + difference 1 3) (sourceB1286 + difference 3 1) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1165) := by
    have ha : (tripleCharges (sourceA1286 + difference 1 3) (sourceB1286 + difference 3 1) sourceC1286) = raw20679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20679; decide +kernel
    rw [ha]
    exact (canonical20679 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1286 + difference 1 4) (sourceB1286 + difference 4 1) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1286 + difference 1 4) (sourceB1286 + difference 4 1) sourceC1286) = raw20680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20680; decide +kernel
    rw [ha]
    exact (canonical20680 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1286 + difference 1 5) (sourceB1286 + difference 5 1) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1267) := by
    have ha : (tripleCharges (sourceA1286 + difference 1 5) (sourceB1286 + difference 5 1) sourceC1286) = raw20681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20681; decide +kernel
    rw [ha]
    exact (canonical20681 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1286 + difference 2 0) (sourceB1286 + difference 0 2) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 581) := by
    have ha : (tripleCharges (sourceA1286 + difference 2 0) (sourceB1286 + difference 0 2) sourceC1286) = raw20682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20682; decide +kernel
    rw [ha]
    exact (canonical20682 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1286 + difference 2 1) (sourceB1286 + difference 1 2) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1112) := by
    have ha : (tripleCharges (sourceA1286 + difference 2 1) (sourceB1286 + difference 1 2) sourceC1286) = raw20683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20683; decide +kernel
    rw [ha]
    exact (canonical20683 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1286 + difference 2 3) (sourceB1286 + difference 3 2) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1165) := by
    have ha : (tripleCharges (sourceA1286 + difference 2 3) (sourceB1286 + difference 3 2) sourceC1286) = raw20684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20684; decide +kernel
    rw [ha]
    exact (canonical20684 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1286 + difference 2 4) (sourceB1286 + difference 4 2) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1286 + difference 2 4) (sourceB1286 + difference 4 2) sourceC1286) = raw20685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20685; decide +kernel
    rw [ha]
    exact (canonical20685 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1286 + difference 2 5) (sourceB1286 + difference 5 2) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1267) := by
    have ha : (tripleCharges (sourceA1286 + difference 2 5) (sourceB1286 + difference 5 2) sourceC1286) = raw20686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20686; decide +kernel
    rw [ha]
    exact (canonical20686 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1286 + difference 3 0) (sourceB1286 + difference 0 3) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 606) := by
    have ha : (tripleCharges (sourceA1286 + difference 3 0) (sourceB1286 + difference 0 3) sourceC1286) = raw20687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20687; decide +kernel
    rw [ha]
    exact (canonical20687 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1286 + difference 3 1) (sourceB1286 + difference 1 3) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1132) := by
    have ha : (tripleCharges (sourceA1286 + difference 3 1) (sourceB1286 + difference 1 3) sourceC1286) = raw20688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20688; decide +kernel
    rw [ha]
    exact (canonical20688 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1286 + difference 3 2) (sourceB1286 + difference 2 3) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1132) := by
    have ha : (tripleCharges (sourceA1286 + difference 3 2) (sourceB1286 + difference 2 3) sourceC1286) = raw20689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20689; decide +kernel
    rw [ha]
    exact (canonical20689 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1286 + difference 3 4) (sourceB1286 + difference 4 3) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1286 + difference 3 4) (sourceB1286 + difference 4 3) sourceC1286) = raw20690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20690; decide +kernel
    rw [ha]
    exact (canonical20690 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1286 + difference 3 5) (sourceB1286 + difference 5 3) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1302) := by
    have ha : (tripleCharges (sourceA1286 + difference 3 5) (sourceB1286 + difference 5 3) sourceC1286) = raw20691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20691; decide +kernel
    rw [ha]
    exact (canonical20691 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1286 + difference 4 0) (sourceB1286 + difference 0 4) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 589) := by
    have ha : (tripleCharges (sourceA1286 + difference 4 0) (sourceB1286 + difference 0 4) sourceC1286) = raw20692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20692; decide +kernel
    rw [ha]
    exact (canonical20692 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1286 + difference 4 1) (sourceB1286 + difference 1 4) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1120) := by
    have ha : (tripleCharges (sourceA1286 + difference 4 1) (sourceB1286 + difference 1 4) sourceC1286) = raw20693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20693; decide +kernel
    rw [ha]
    exact (canonical20693 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1286 + difference 4 2) (sourceB1286 + difference 2 4) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1120) := by
    have ha : (tripleCharges (sourceA1286 + difference 4 2) (sourceB1286 + difference 2 4) sourceC1286) = raw20694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20694; decide +kernel
    rw [ha]
    exact (canonical20694 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1286 + difference 4 3) (sourceB1286 + difference 3 4) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1176) := by
    have ha : (tripleCharges (sourceA1286 + difference 4 3) (sourceB1286 + difference 3 4) sourceC1286) = raw20695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20695; decide +kernel
    rw [ha]
    exact (canonical20695 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1286 + difference 4 5) (sourceB1286 + difference 5 4) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1286 + difference 4 5) (sourceB1286 + difference 5 4) sourceC1286) = raw20696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20696; decide +kernel
    rw [ha]
    exact (canonical20696 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1286 + difference 5 0) (sourceB1286 + difference 0 5) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 584) := by
    have ha : (tripleCharges (sourceA1286 + difference 5 0) (sourceB1286 + difference 0 5) sourceC1286) = raw20697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20697; decide +kernel
    rw [ha]
    exact (canonical20697 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1286 + difference 5 1) (sourceB1286 + difference 1 5) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1115) := by
    have ha : (tripleCharges (sourceA1286 + difference 5 1) (sourceB1286 + difference 1 5) sourceC1286) = raw20698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20698; decide +kernel
    rw [ha]
    exact (canonical20698 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1286 + difference 5 2) (sourceB1286 + difference 2 5) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1115) := by
    have ha : (tripleCharges (sourceA1286 + difference 5 2) (sourceB1286 + difference 2 5) sourceC1286) = raw20699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20699; decide +kernel
    rw [ha]
    exact (canonical20699 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1286 + difference 5 3) (sourceB1286 + difference 3 5) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1168) := by
    have ha : (tripleCharges (sourceA1286 + difference 5 3) (sourceB1286 + difference 3 5) sourceC1286) = raw20700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20700; decide +kernel
    rw [ha]
    exact (canonical20700 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1286 + difference 5 4) (sourceB1286 + difference 4 5) sourceC1286) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1286 + difference 5 4) (sourceB1286 + difference 4 5) sourceC1286) = raw20701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1286 sourceB1286 sourceC1286 difference raw20701; decide +kernel
    rw [ha]
    exact (canonical20701 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1286 sourceB1286 sourceC1286
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1286, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1287 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1287 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1287 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceForm1287 : Integer.Sparse Master := [(Sum.inr 1514, 2), (Sum.inr 1516, 1), (Sum.inr 1520, 1), (Sum.inr 1533, 1), (Sum.inr 3260, 2), (Sum.inr 3262, 2), (Sum.inr 3264, 2), (Sum.inr 3266, 2), (Sum.inr 3272, 2), (Sum.inr 3275, 1), (Sum.inr 3276, 1), (Sum.inr 3291, 2), (Sum.inr 3293, 2), (Sum.inr 3298, 1), (Sum.inr 3301, 1), (Sum.inr 3302, 1), (Sum.inr 3305, 1), (Sum.inr 3468, 2), (Sum.inr 3484, 1), (Sum.inr 3545, 1), (Sum.inr 3547, 1)]

theorem sourceEq1287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1287 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1287 + difference 0 1) (sourceB1287 + difference 1 0) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1287 + difference 0 1) (sourceB1287 + difference 1 0) sourceC1287) = raw20702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20702; decide +kernel
    rw [ha]
    exact (canonical20702 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1287 + difference 0 2) (sourceB1287 + difference 2 0) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1287 + difference 0 2) (sourceB1287 + difference 2 0) sourceC1287) = raw20703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20703; decide +kernel
    rw [ha]
    exact (canonical20703 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1287 + difference 0 3) (sourceB1287 + difference 3 0) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3484) := by
    have ha : (tripleCharges (sourceA1287 + difference 0 3) (sourceB1287 + difference 3 0) sourceC1287) = raw20704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20704; decide +kernel
    rw [ha]
    exact (canonical20704 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1287 + difference 0 4) (sourceB1287 + difference 4 0) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA1287 + difference 0 4) (sourceB1287 + difference 4 0) sourceC1287) = raw20705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20705; decide +kernel
    rw [ha]
    exact (canonical20705 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1287 + difference 0 5) (sourceB1287 + difference 5 0) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA1287 + difference 0 5) (sourceB1287 + difference 5 0) sourceC1287) = raw20706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20706; decide +kernel
    rw [ha]
    exact (canonical20706 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1287 + difference 1 0) (sourceB1287 + difference 0 1) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA1287 + difference 1 0) (sourceB1287 + difference 0 1) sourceC1287) = raw20707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20707; decide +kernel
    rw [ha]
    exact (canonical20707 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1287 + difference 1 2) (sourceB1287 + difference 2 1) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3260) := by
    have ha : (tripleCharges (sourceA1287 + difference 1 2) (sourceB1287 + difference 2 1) sourceC1287) = raw20708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20708; decide +kernel
    rw [ha]
    exact (canonical20708 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1287 + difference 1 3) (sourceB1287 + difference 3 1) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3264) := by
    have ha : (tripleCharges (sourceA1287 + difference 1 3) (sourceB1287 + difference 3 1) sourceC1287) = raw20709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20709; decide +kernel
    rw [ha]
    exact (canonical20709 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1287 + difference 1 4) (sourceB1287 + difference 4 1) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1287 + difference 1 4) (sourceB1287 + difference 4 1) sourceC1287) = raw20710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20710; decide +kernel
    rw [ha]
    exact (canonical20710 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1287 + difference 1 5) (sourceB1287 + difference 5 1) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1287 + difference 1 5) (sourceB1287 + difference 5 1) sourceC1287) = raw20711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20711; decide +kernel
    rw [ha]
    exact (canonical20711 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1287 + difference 2 0) (sourceB1287 + difference 0 2) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA1287 + difference 2 0) (sourceB1287 + difference 0 2) sourceC1287) = raw20712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20712; decide +kernel
    rw [ha]
    exact (canonical20712 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1287 + difference 2 1) (sourceB1287 + difference 1 2) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3260) := by
    have ha : (tripleCharges (sourceA1287 + difference 2 1) (sourceB1287 + difference 1 2) sourceC1287) = raw20713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20713; decide +kernel
    rw [ha]
    exact (canonical20713 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1287 + difference 2 3) (sourceB1287 + difference 3 2) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3264) := by
    have ha : (tripleCharges (sourceA1287 + difference 2 3) (sourceB1287 + difference 3 2) sourceC1287) = raw20714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20714; decide +kernel
    rw [ha]
    exact (canonical20714 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1287 + difference 2 4) (sourceB1287 + difference 4 2) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1287 + difference 2 4) (sourceB1287 + difference 4 2) sourceC1287) = raw20715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20715; decide +kernel
    rw [ha]
    exact (canonical20715 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1287 + difference 2 5) (sourceB1287 + difference 5 2) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1287 + difference 2 5) (sourceB1287 + difference 5 2) sourceC1287) = raw20716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20716; decide +kernel
    rw [ha]
    exact (canonical20716 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1287 + difference 3 0) (sourceB1287 + difference 0 3) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1520) := by
    have ha : (tripleCharges (sourceA1287 + difference 3 0) (sourceB1287 + difference 0 3) sourceC1287) = raw20717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20717; decide +kernel
    rw [ha]
    exact (canonical20717 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1287 + difference 3 1) (sourceB1287 + difference 1 3) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA1287 + difference 3 1) (sourceB1287 + difference 1 3) sourceC1287) = raw20718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20718; decide +kernel
    rw [ha]
    exact (canonical20718 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1287 + difference 3 2) (sourceB1287 + difference 2 3) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA1287 + difference 3 2) (sourceB1287 + difference 2 3) sourceC1287) = raw20719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20719; decide +kernel
    rw [ha]
    exact (canonical20719 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1287 + difference 3 4) (sourceB1287 + difference 4 3) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1287 + difference 3 4) (sourceB1287 + difference 4 3) sourceC1287) = raw20720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20720; decide +kernel
    rw [ha]
    exact (canonical20720 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1287 + difference 3 5) (sourceB1287 + difference 5 3) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1287 + difference 3 5) (sourceB1287 + difference 5 3) sourceC1287) = raw20721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20721; decide +kernel
    rw [ha]
    exact (canonical20721 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1287 + difference 4 0) (sourceB1287 + difference 0 4) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA1287 + difference 4 0) (sourceB1287 + difference 0 4) sourceC1287) = raw20722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20722; decide +kernel
    rw [ha]
    exact (canonical20722 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1287 + difference 4 1) (sourceB1287 + difference 1 4) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA1287 + difference 4 1) (sourceB1287 + difference 1 4) sourceC1287) = raw20723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20723; decide +kernel
    rw [ha]
    exact (canonical20723 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1287 + difference 4 2) (sourceB1287 + difference 2 4) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA1287 + difference 4 2) (sourceB1287 + difference 2 4) sourceC1287) = raw20724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20724; decide +kernel
    rw [ha]
    exact (canonical20724 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1287 + difference 4 3) (sourceB1287 + difference 3 4) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA1287 + difference 4 3) (sourceB1287 + difference 3 4) sourceC1287) = raw20725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20725; decide +kernel
    rw [ha]
    exact (canonical20725 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1287 + difference 4 5) (sourceB1287 + difference 5 4) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1287 + difference 4 5) (sourceB1287 + difference 5 4) sourceC1287) = raw20726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20726; decide +kernel
    rw [ha]
    exact (canonical20726 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1287 + difference 5 0) (sourceB1287 + difference 0 5) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA1287 + difference 5 0) (sourceB1287 + difference 0 5) sourceC1287) = raw20727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20727; decide +kernel
    rw [ha]
    exact (canonical20727 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1287 + difference 5 1) (sourceB1287 + difference 1 5) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3262) := by
    have ha : (tripleCharges (sourceA1287 + difference 5 1) (sourceB1287 + difference 1 5) sourceC1287) = raw20728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20728; decide +kernel
    rw [ha]
    exact (canonical20728 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1287 + difference 5 2) (sourceB1287 + difference 2 5) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3262) := by
    have ha : (tripleCharges (sourceA1287 + difference 5 2) (sourceB1287 + difference 2 5) sourceC1287) = raw20729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20729; decide +kernel
    rw [ha]
    exact (canonical20729 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1287 + difference 5 3) (sourceB1287 + difference 3 5) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3275) := by
    have ha : (tripleCharges (sourceA1287 + difference 5 3) (sourceB1287 + difference 3 5) sourceC1287) = raw20730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20730; decide +kernel
    rw [ha]
    exact (canonical20730 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1287 + difference 5 4) (sourceB1287 + difference 4 5) sourceC1287) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3298) := by
    have ha : (tripleCharges (sourceA1287 + difference 5 4) (sourceB1287 + difference 4 5) sourceC1287) = raw20731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1287 sourceB1287 sourceC1287 difference raw20731; decide +kernel
    rw [ha]
    exact (canonical20731 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1287 sourceB1287 sourceC1287
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1287, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1288 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1288 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1288 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceForm1288 : Integer.Sparse Master := [(Sum.inr 626, 2), (Sum.inr 633, 1), (Sum.inr 635, 1), (Sum.inr 641, 1), (Sum.inr 1242, 1), (Sum.inr 4092, -1)]

theorem sourceEq1288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1288 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1288 + difference 0 0) (sourceB1288 + difference 0 0) sourceC1288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1288 + difference 0 0) (sourceB1288 + difference 0 0) sourceC1288) = raw20732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1288 sourceB1288 sourceC1288 difference raw20732; decide +kernel
    rw [ha]
    exact (canonical20732 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1288 + difference 1 0) (sourceB1288 + difference 0 1) sourceC1288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 626) := by
    have ha : (tripleCharges (sourceA1288 + difference 1 0) (sourceB1288 + difference 0 1) sourceC1288) = raw20733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1288 sourceB1288 sourceC1288 difference raw20733; decide +kernel
    rw [ha]
    exact (canonical20733 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1288 + difference 2 0) (sourceB1288 + difference 0 2) sourceC1288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 626) := by
    have ha : (tripleCharges (sourceA1288 + difference 2 0) (sourceB1288 + difference 0 2) sourceC1288) = raw20734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1288 sourceB1288 sourceC1288 difference raw20734; decide +kernel
    rw [ha]
    exact (canonical20734 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1288 + difference 3 0) (sourceB1288 + difference 0 3) sourceC1288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 641) := by
    have ha : (tripleCharges (sourceA1288 + difference 3 0) (sourceB1288 + difference 0 3) sourceC1288) = raw20735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1288 sourceB1288 sourceC1288 difference raw20735; decide +kernel
    rw [ha]
    exact (canonical20735 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1288 + difference 4 0) (sourceB1288 + difference 0 4) sourceC1288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 635) := by
    have ha : (tripleCharges (sourceA1288 + difference 4 0) (sourceB1288 + difference 0 4) sourceC1288) = raw20736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1288 sourceB1288 sourceC1288 difference raw20736; decide +kernel
    rw [ha]
    exact (canonical20736 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1288 + difference 5 0) (sourceB1288 + difference 0 5) sourceC1288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 633) := by
    have ha : (tripleCharges (sourceA1288 + difference 5 0) (sourceB1288 + difference 0 5) sourceC1288) = raw20737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1288 sourceB1288 sourceC1288 difference raw20737; decide +kernel
    rw [ha]
    exact (canonical20737 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1288 + sourceB1288) sourceC1288) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1288 + sourceB1288) sourceC1288) = raw20738 := by
      apply Matrix.ext; unfold doubleCharges sourceA1288 sourceB1288 sourceC1288 raw20738; decide +kernel
    rw [ha]
    exact (canonical20738 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1288 sourceB1288 sourceC1288
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1288, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1289 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1289 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1289 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceForm1289 : Integer.Sparse Master := [(Sum.inr 1115, 1), (Sum.inr 1148, 1), (Sum.inr 1154, 1), (Sum.inr 1159, 1), (Sum.inr 1242, 1), (Sum.inr 2482, 1), (Sum.inr 4092, -1)]

theorem sourceEq1289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1289 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1289 + difference 0 1) (sourceB1289 + difference 1 0) sourceC1289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1289 + difference 0 1) (sourceB1289 + difference 1 0) sourceC1289) = raw20739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1289 sourceB1289 sourceC1289 difference raw20739; decide +kernel
    rw [ha]
    exact (canonical20739 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1289 + difference 1 1) (sourceB1289 + difference 1 1) sourceC1289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1289 + difference 1 1) (sourceB1289 + difference 1 1) sourceC1289) = raw20732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1289 sourceB1289 sourceC1289 difference raw20732; decide +kernel
    rw [ha]
    exact (canonical20732 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1289 + difference 2 1) (sourceB1289 + difference 1 2) sourceC1289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1148) := by
    have ha : (tripleCharges (sourceA1289 + difference 2 1) (sourceB1289 + difference 1 2) sourceC1289) = raw20740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1289 sourceB1289 sourceC1289 difference raw20740; decide +kernel
    rw [ha]
    exact (canonical20740 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1289 + difference 3 1) (sourceB1289 + difference 1 3) sourceC1289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1159) := by
    have ha : (tripleCharges (sourceA1289 + difference 3 1) (sourceB1289 + difference 1 3) sourceC1289) = raw20741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1289 sourceB1289 sourceC1289 difference raw20741; decide +kernel
    rw [ha]
    exact (canonical20741 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1289 + difference 4 1) (sourceB1289 + difference 1 4) sourceC1289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1154) := by
    have ha : (tripleCharges (sourceA1289 + difference 4 1) (sourceB1289 + difference 1 4) sourceC1289) = raw20742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1289 sourceB1289 sourceC1289 difference raw20742; decide +kernel
    rw [ha]
    exact (canonical20742 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1289 + difference 5 1) (sourceB1289 + difference 1 5) sourceC1289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1115) := by
    have ha : (tripleCharges (sourceA1289 + difference 5 1) (sourceB1289 + difference 1 5) sourceC1289) = raw20743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1289 sourceB1289 sourceC1289 difference raw20743; decide +kernel
    rw [ha]
    exact (canonical20743 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1289 + sourceB1289) sourceC1289) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1289 + sourceB1289) sourceC1289) = raw20738 := by
      apply Matrix.ext; unfold doubleCharges sourceA1289 sourceB1289 sourceC1289 raw20738; decide +kernel
    rw [ha]
    exact (canonical20738 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1289 sourceB1289 sourceC1289
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1289, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1290 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1290 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1290 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceForm1290 : Integer.Sparse Master := [(Sum.inr 1131, 2), (Sum.inr 1140, 1), (Sum.inr 1144, 1), (Sum.inr 1242, 1), (Sum.inr 2517, 1), (Sum.inr 4092, -1)]

theorem sourceEq1290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1290 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1290 + difference 0 3) (sourceB1290 + difference 3 0) sourceC1290) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2517) := by
    have ha : (tripleCharges (sourceA1290 + difference 0 3) (sourceB1290 + difference 3 0) sourceC1290) = raw20744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1290 sourceB1290 sourceC1290 difference raw20744; decide +kernel
    rw [ha]
    exact (canonical20744 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1290 + difference 1 3) (sourceB1290 + difference 3 1) sourceC1290) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1290 + difference 1 3) (sourceB1290 + difference 3 1) sourceC1290) = raw20745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1290 sourceB1290 sourceC1290 difference raw20745; decide +kernel
    rw [ha]
    exact (canonical20745 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1290 + difference 2 3) (sourceB1290 + difference 3 2) sourceC1290) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1290 + difference 2 3) (sourceB1290 + difference 3 2) sourceC1290) = raw20746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1290 sourceB1290 sourceC1290 difference raw20746; decide +kernel
    rw [ha]
    exact (canonical20746 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1290 + difference 3 3) (sourceB1290 + difference 3 3) sourceC1290) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1290 + difference 3 3) (sourceB1290 + difference 3 3) sourceC1290) = raw20732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1290 sourceB1290 sourceC1290 difference raw20732; decide +kernel
    rw [ha]
    exact (canonical20732 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1290 + difference 4 3) (sourceB1290 + difference 3 4) sourceC1290) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1144) := by
    have ha : (tripleCharges (sourceA1290 + difference 4 3) (sourceB1290 + difference 3 4) sourceC1290) = raw20747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1290 sourceB1290 sourceC1290 difference raw20747; decide +kernel
    rw [ha]
    exact (canonical20747 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1290 + difference 5 3) (sourceB1290 + difference 3 5) sourceC1290) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1290 + difference 5 3) (sourceB1290 + difference 3 5) sourceC1290) = raw20748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1290 sourceB1290 sourceC1290 difference raw20748; decide +kernel
    rw [ha]
    exact (canonical20748 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1290 + sourceB1290) sourceC1290) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1290 + sourceB1290) sourceC1290) = raw20738 := by
      apply Matrix.ext; unfold doubleCharges sourceA1290 sourceB1290 sourceC1290 raw20738; decide +kernel
    rw [ha]
    exact (canonical20738 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1290 sourceB1290 sourceC1290
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1290, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1291 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1291 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC1291 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceForm1291 : Integer.Sparse Master := [(Sum.inr 4144, 2), (Sum.inr 4146, 1), (Sum.inr 4148, 1), (Sum.inr 4177, 1), (Sum.inr 4293, 2), (Sum.inr 4315, 1), (Sum.inr 4468, 1), (Sum.inr 4517, 2), (Sum.inr 4520, 1), (Sum.inr 4523, 2), (Sum.inr 4526, 2), (Sum.inr 4546, 2), (Sum.inr 4606, 2), (Sum.inr 4608, 2), (Sum.inr 4612, 1), (Sum.inr 4624, 1), (Sum.inr 4625, 1), (Sum.inr 5078, 2), (Sum.inr 5109, 1), (Sum.inr 5293, 1), (Sum.inr 5296, 1)]

theorem sourceEq1291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1291 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1291 + difference 0 1) (sourceB1291 + difference 1 0) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1291 + difference 0 1) (sourceB1291 + difference 1 0) sourceC1291) = raw7832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7832; decide +kernel
    rw [ha]
    exact (canonical7832 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1291 + difference 0 2) (sourceB1291 + difference 2 0) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1291 + difference 0 2) (sourceB1291 + difference 2 0) sourceC1291) = raw7833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7833; decide +kernel
    rw [ha]
    exact (canonical7833 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1291 + difference 0 3) (sourceB1291 + difference 3 0) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1291 + difference 0 3) (sourceB1291 + difference 3 0) sourceC1291) = raw7834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7834; decide +kernel
    rw [ha]
    exact (canonical7834 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1291 + difference 0 4) (sourceB1291 + difference 4 0) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA1291 + difference 0 4) (sourceB1291 + difference 4 0) sourceC1291) = raw7835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7835; decide +kernel
    rw [ha]
    exact (canonical7835 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1291 + difference 0 5) (sourceB1291 + difference 5 0) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1291 + difference 0 5) (sourceB1291 + difference 5 0) sourceC1291) = raw15022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw15022; decide +kernel
    rw [ha]
    exact (canonical15022 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1291 + difference 1 0) (sourceB1291 + difference 0 1) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4144) := by
    have ha : (tripleCharges (sourceA1291 + difference 1 0) (sourceB1291 + difference 0 1) sourceC1291) = raw20749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20749; decide +kernel
    rw [ha]
    exact (canonical20749 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1291 + difference 1 2) (sourceB1291 + difference 2 1) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4523) := by
    have ha : (tripleCharges (sourceA1291 + difference 1 2) (sourceB1291 + difference 2 1) sourceC1291) = raw20750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20750; decide +kernel
    rw [ha]
    exact (canonical20750 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1291 + difference 1 3) (sourceB1291 + difference 3 1) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4517) := by
    have ha : (tripleCharges (sourceA1291 + difference 1 3) (sourceB1291 + difference 3 1) sourceC1291) = raw20751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20751; decide +kernel
    rw [ha]
    exact (canonical20751 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1291 + difference 1 4) (sourceB1291 + difference 4 1) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1291 + difference 1 4) (sourceB1291 + difference 4 1) sourceC1291) = raw20752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20752; decide +kernel
    rw [ha]
    exact (canonical20752 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1291 + difference 1 5) (sourceB1291 + difference 5 1) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1291 + difference 1 5) (sourceB1291 + difference 5 1) sourceC1291) = raw7811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7811; decide +kernel
    rw [ha]
    exact (canonical7811 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1291 + difference 2 0) (sourceB1291 + difference 0 2) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4144) := by
    have ha : (tripleCharges (sourceA1291 + difference 2 0) (sourceB1291 + difference 0 2) sourceC1291) = raw20753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20753; decide +kernel
    rw [ha]
    exact (canonical20753 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1291 + difference 2 1) (sourceB1291 + difference 1 2) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4523) := by
    have ha : (tripleCharges (sourceA1291 + difference 2 1) (sourceB1291 + difference 1 2) sourceC1291) = raw20754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20754; decide +kernel
    rw [ha]
    exact (canonical20754 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1291 + difference 2 3) (sourceB1291 + difference 3 2) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4517) := by
    have ha : (tripleCharges (sourceA1291 + difference 2 3) (sourceB1291 + difference 3 2) sourceC1291) = raw20755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20755; decide +kernel
    rw [ha]
    exact (canonical20755 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1291 + difference 2 4) (sourceB1291 + difference 4 2) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1291 + difference 2 4) (sourceB1291 + difference 4 2) sourceC1291) = raw20756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20756; decide +kernel
    rw [ha]
    exact (canonical20756 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1291 + difference 2 5) (sourceB1291 + difference 5 2) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1291 + difference 2 5) (sourceB1291 + difference 5 2) sourceC1291) = raw7816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7816; decide +kernel
    rw [ha]
    exact (canonical7816 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1291 + difference 3 0) (sourceB1291 + difference 0 3) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1291 + difference 3 0) (sourceB1291 + difference 0 3) sourceC1291) = raw20757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20757; decide +kernel
    rw [ha]
    exact (canonical20757 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1291 + difference 3 1) (sourceB1291 + difference 1 3) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1291 + difference 3 1) (sourceB1291 + difference 1 3) sourceC1291) = raw20758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20758; decide +kernel
    rw [ha]
    exact (canonical20758 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1291 + difference 3 2) (sourceB1291 + difference 2 3) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1291 + difference 3 2) (sourceB1291 + difference 2 3) sourceC1291) = raw20759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20759; decide +kernel
    rw [ha]
    exact (canonical20759 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1291 + difference 3 4) (sourceB1291 + difference 4 3) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1291 + difference 3 4) (sourceB1291 + difference 4 3) sourceC1291) = raw20760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20760; decide +kernel
    rw [ha]
    exact (canonical20760 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1291 + difference 3 5) (sourceB1291 + difference 5 3) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1291 + difference 3 5) (sourceB1291 + difference 5 3) sourceC1291) = raw7821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7821; decide +kernel
    rw [ha]
    exact (canonical7821 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1291 + difference 4 0) (sourceB1291 + difference 0 4) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4148) := by
    have ha : (tripleCharges (sourceA1291 + difference 4 0) (sourceB1291 + difference 0 4) sourceC1291) = raw20761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20761; decide +kernel
    rw [ha]
    exact (canonical20761 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1291 + difference 4 1) (sourceB1291 + difference 1 4) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4526) := by
    have ha : (tripleCharges (sourceA1291 + difference 4 1) (sourceB1291 + difference 1 4) sourceC1291) = raw20762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20762; decide +kernel
    rw [ha]
    exact (canonical20762 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1291 + difference 4 2) (sourceB1291 + difference 2 4) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4526) := by
    have ha : (tripleCharges (sourceA1291 + difference 4 2) (sourceB1291 + difference 2 4) sourceC1291) = raw20763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20763; decide +kernel
    rw [ha]
    exact (canonical20763 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1291 + difference 4 3) (sourceB1291 + difference 3 4) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4520) := by
    have ha : (tripleCharges (sourceA1291 + difference 4 3) (sourceB1291 + difference 3 4) sourceC1291) = raw20764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20764; decide +kernel
    rw [ha]
    exact (canonical20764 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1291 + difference 4 5) (sourceB1291 + difference 5 4) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1291 + difference 4 5) (sourceB1291 + difference 5 4) sourceC1291) = raw7826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7826; decide +kernel
    rw [ha]
    exact (canonical7826 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1291 + difference 5 0) (sourceB1291 + difference 0 5) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4146) := by
    have ha : (tripleCharges (sourceA1291 + difference 5 0) (sourceB1291 + difference 0 5) sourceC1291) = raw20765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20765; decide +kernel
    rw [ha]
    exact (canonical20765 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1291 + difference 5 1) (sourceB1291 + difference 1 5) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4293) := by
    have ha : (tripleCharges (sourceA1291 + difference 5 1) (sourceB1291 + difference 1 5) sourceC1291) = raw20766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20766; decide +kernel
    rw [ha]
    exact (canonical20766 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1291 + difference 5 2) (sourceB1291 + difference 2 5) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4293) := by
    have ha : (tripleCharges (sourceA1291 + difference 5 2) (sourceB1291 + difference 2 5) sourceC1291) = raw20767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20767; decide +kernel
    rw [ha]
    exact (canonical20767 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1291 + difference 5 3) (sourceB1291 + difference 3 5) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4315) := by
    have ha : (tripleCharges (sourceA1291 + difference 5 3) (sourceB1291 + difference 3 5) sourceC1291) = raw20768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20768; decide +kernel
    rw [ha]
    exact (canonical20768 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1291 + difference 5 4) (sourceB1291 + difference 4 5) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1291 + difference 5 4) (sourceB1291 + difference 4 5) sourceC1291) = raw20769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20769; decide +kernel
    rw [ha]
    exact (canonical20769 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1291 sourceB1291 sourceC1291
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1291, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1292 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1292 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC1292 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceForm1292 : Integer.Sparse Master := [(Sum.inr 572, 2), (Sum.inr 574, 1), (Sum.inr 576, 1), (Sum.inr 605, 1), (Sum.inr 871, 2), (Sum.inr 893, 1), (Sum.inr 1051, 1), (Sum.inr 1101, 2), (Sum.inr 1104, 1), (Sum.inr 1107, 2), (Sum.inr 1110, 2), (Sum.inr 1131, 2), (Sum.inr 1240, 2), (Sum.inr 1242, 2), (Sum.inr 1246, 1), (Sum.inr 1301, 1), (Sum.inr 1304, 1), (Sum.inr 2485, 2), (Sum.inr 2519, 1), (Sum.inr 2770, 1), (Sum.inr 3102, 1)]

theorem sourceEq1292 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1292 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1292 + difference 0 1) (sourceB1292 + difference 1 0) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1292 + difference 0 1) (sourceB1292 + difference 1 0) sourceC1292) = raw7862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw7862; decide +kernel
    rw [ha]
    exact (canonical7862 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1292 + difference 0 2) (sourceB1292 + difference 2 0) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1292 + difference 0 2) (sourceB1292 + difference 2 0) sourceC1292) = raw7863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw7863; decide +kernel
    rw [ha]
    exact (canonical7863 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1292 + difference 0 3) (sourceB1292 + difference 3 0) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1292 + difference 0 3) (sourceB1292 + difference 3 0) sourceC1292) = raw7864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw7864; decide +kernel
    rw [ha]
    exact (canonical7864 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1292 + difference 0 4) (sourceB1292 + difference 4 0) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA1292 + difference 0 4) (sourceB1292 + difference 4 0) sourceC1292) = raw7865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw7865; decide +kernel
    rw [ha]
    exact (canonical7865 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1292 + difference 0 5) (sourceB1292 + difference 5 0) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA1292 + difference 0 5) (sourceB1292 + difference 5 0) sourceC1292) = raw15044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw15044; decide +kernel
    rw [ha]
    exact (canonical15044 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1292 + difference 1 0) (sourceB1292 + difference 0 1) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 572) := by
    have ha : (tripleCharges (sourceA1292 + difference 1 0) (sourceB1292 + difference 0 1) sourceC1292) = raw20770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20770; decide +kernel
    rw [ha]
    exact (canonical20770 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1292 + difference 1 2) (sourceB1292 + difference 2 1) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1107) := by
    have ha : (tripleCharges (sourceA1292 + difference 1 2) (sourceB1292 + difference 2 1) sourceC1292) = raw20771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20771; decide +kernel
    rw [ha]
    exact (canonical20771 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1292 + difference 1 3) (sourceB1292 + difference 3 1) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1101) := by
    have ha : (tripleCharges (sourceA1292 + difference 1 3) (sourceB1292 + difference 3 1) sourceC1292) = raw20772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20772; decide +kernel
    rw [ha]
    exact (canonical20772 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1292 + difference 1 4) (sourceB1292 + difference 4 1) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1292 + difference 1 4) (sourceB1292 + difference 4 1) sourceC1292) = raw20773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20773; decide +kernel
    rw [ha]
    exact (canonical20773 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1292 + difference 1 5) (sourceB1292 + difference 5 1) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1292 + difference 1 5) (sourceB1292 + difference 5 1) sourceC1292) = raw7841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw7841; decide +kernel
    rw [ha]
    exact (canonical7841 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1292 + difference 2 0) (sourceB1292 + difference 0 2) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 572) := by
    have ha : (tripleCharges (sourceA1292 + difference 2 0) (sourceB1292 + difference 0 2) sourceC1292) = raw20774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20774; decide +kernel
    rw [ha]
    exact (canonical20774 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1292 + difference 2 1) (sourceB1292 + difference 1 2) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1107) := by
    have ha : (tripleCharges (sourceA1292 + difference 2 1) (sourceB1292 + difference 1 2) sourceC1292) = raw20775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20775; decide +kernel
    rw [ha]
    exact (canonical20775 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1292 + difference 2 3) (sourceB1292 + difference 3 2) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1101) := by
    have ha : (tripleCharges (sourceA1292 + difference 2 3) (sourceB1292 + difference 3 2) sourceC1292) = raw20776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20776; decide +kernel
    rw [ha]
    exact (canonical20776 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1292 + difference 2 4) (sourceB1292 + difference 4 2) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1292 + difference 2 4) (sourceB1292 + difference 4 2) sourceC1292) = raw20777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20777; decide +kernel
    rw [ha]
    exact (canonical20777 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1292 + difference 2 5) (sourceB1292 + difference 5 2) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1292 + difference 2 5) (sourceB1292 + difference 5 2) sourceC1292) = raw7846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw7846; decide +kernel
    rw [ha]
    exact (canonical7846 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1292 + difference 3 0) (sourceB1292 + difference 0 3) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 605) := by
    have ha : (tripleCharges (sourceA1292 + difference 3 0) (sourceB1292 + difference 0 3) sourceC1292) = raw20778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20778; decide +kernel
    rw [ha]
    exact (canonical20778 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1292 + difference 3 1) (sourceB1292 + difference 1 3) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1292 + difference 3 1) (sourceB1292 + difference 1 3) sourceC1292) = raw20779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20779; decide +kernel
    rw [ha]
    exact (canonical20779 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1292 + difference 3 2) (sourceB1292 + difference 2 3) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1292 + difference 3 2) (sourceB1292 + difference 2 3) sourceC1292) = raw20780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20780; decide +kernel
    rw [ha]
    exact (canonical20780 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1292 + difference 3 4) (sourceB1292 + difference 4 3) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1304) := by
    have ha : (tripleCharges (sourceA1292 + difference 3 4) (sourceB1292 + difference 4 3) sourceC1292) = raw20781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20781; decide +kernel
    rw [ha]
    exact (canonical20781 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1292 + difference 3 5) (sourceB1292 + difference 5 3) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1292 + difference 3 5) (sourceB1292 + difference 5 3) sourceC1292) = raw7851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw7851; decide +kernel
    rw [ha]
    exact (canonical7851 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1292 + difference 4 0) (sourceB1292 + difference 0 4) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 576) := by
    have ha : (tripleCharges (sourceA1292 + difference 4 0) (sourceB1292 + difference 0 4) sourceC1292) = raw20782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20782; decide +kernel
    rw [ha]
    exact (canonical20782 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1292 + difference 4 1) (sourceB1292 + difference 1 4) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1110) := by
    have ha : (tripleCharges (sourceA1292 + difference 4 1) (sourceB1292 + difference 1 4) sourceC1292) = raw20783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20783; decide +kernel
    rw [ha]
    exact (canonical20783 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1292 + difference 4 2) (sourceB1292 + difference 2 4) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1110) := by
    have ha : (tripleCharges (sourceA1292 + difference 4 2) (sourceB1292 + difference 2 4) sourceC1292) = raw20784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20784; decide +kernel
    rw [ha]
    exact (canonical20784 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1292 + difference 4 3) (sourceB1292 + difference 3 4) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1104) := by
    have ha : (tripleCharges (sourceA1292 + difference 4 3) (sourceB1292 + difference 3 4) sourceC1292) = raw20785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20785; decide +kernel
    rw [ha]
    exact (canonical20785 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1292 + difference 4 5) (sourceB1292 + difference 5 4) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1292 + difference 4 5) (sourceB1292 + difference 5 4) sourceC1292) = raw7856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw7856; decide +kernel
    rw [ha]
    exact (canonical7856 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1292 + difference 5 0) (sourceB1292 + difference 0 5) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 574) := by
    have ha : (tripleCharges (sourceA1292 + difference 5 0) (sourceB1292 + difference 0 5) sourceC1292) = raw20786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20786; decide +kernel
    rw [ha]
    exact (canonical20786 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1292 + difference 5 1) (sourceB1292 + difference 1 5) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 871) := by
    have ha : (tripleCharges (sourceA1292 + difference 5 1) (sourceB1292 + difference 1 5) sourceC1292) = raw20787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20787; decide +kernel
    rw [ha]
    exact (canonical20787 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1292 + difference 5 2) (sourceB1292 + difference 2 5) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 871) := by
    have ha : (tripleCharges (sourceA1292 + difference 5 2) (sourceB1292 + difference 2 5) sourceC1292) = raw20788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20788; decide +kernel
    rw [ha]
    exact (canonical20788 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1292 + difference 5 3) (sourceB1292 + difference 3 5) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 893) := by
    have ha : (tripleCharges (sourceA1292 + difference 5 3) (sourceB1292 + difference 3 5) sourceC1292) = raw20789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20789; decide +kernel
    rw [ha]
    exact (canonical20789 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1292 + difference 5 4) (sourceB1292 + difference 4 5) sourceC1292) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1292 + difference 5 4) (sourceB1292 + difference 4 5) sourceC1292) = raw20790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1292 sourceB1292 sourceC1292 difference raw20790; decide +kernel
    rw [ha]
    exact (canonical20790 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1292 sourceB1292 sourceC1292
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1292, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1293 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceB1293 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC1293 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1293 : Integer.Sparse Master := [(Sum.inr 4401, 2), (Sum.inr 4426, 1), (Sum.inr 4428, 1), (Sum.inr 4440, 2), (Sum.inr 4460, 1), (Sum.inr 4463, 1), (Sum.inr 4476, 1), (Sum.inr 4505, 1), (Sum.inr 4564, 2), (Sum.inr 4572, 1), (Sum.inr 4573, 1), (Sum.inr 4577, 2), (Sum.inr 4583, 2), (Sum.inr 4584, 2), (Sum.inr 4591, 4), (Sum.inr 4605, 1), (Sum.inr 4608, 2), (Sum.inr 4609, 1), (Sum.inr 4625, 2)]

theorem sourceEq1293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1293 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1293 + difference 0 1) (sourceB1293 + difference 1 0) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA1293 + difference 0 1) (sourceB1293 + difference 1 0) sourceC1293) = raw20791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20791; decide +kernel
    rw [ha]
    exact (canonical20791 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1293 + difference 0 2) (sourceB1293 + difference 2 0) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA1293 + difference 0 2) (sourceB1293 + difference 2 0) sourceC1293) = raw20792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20792; decide +kernel
    rw [ha]
    exact (canonical20792 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1293 + difference 0 3) (sourceB1293 + difference 3 0) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA1293 + difference 0 3) (sourceB1293 + difference 3 0) sourceC1293) = raw20793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20793; decide +kernel
    rw [ha]
    exact (canonical20793 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1293 + difference 0 4) (sourceB1293 + difference 4 0) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1293 + difference 0 4) (sourceB1293 + difference 4 0) sourceC1293) = raw20416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20416; decide +kernel
    rw [ha]
    exact (canonical20416 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1293 + difference 0 5) (sourceB1293 + difference 5 0) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1293 + difference 0 5) (sourceB1293 + difference 5 0) sourceC1293) = raw20794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20794; decide +kernel
    rw [ha]
    exact (canonical20794 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1293 + difference 1 0) (sourceB1293 + difference 0 1) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1293 + difference 1 0) (sourceB1293 + difference 0 1) sourceC1293) = raw20795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20795; decide +kernel
    rw [ha]
    exact (canonical20795 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1293 + difference 1 2) (sourceB1293 + difference 2 1) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4577) := by
    have ha : (tripleCharges (sourceA1293 + difference 1 2) (sourceB1293 + difference 2 1) sourceC1293) = raw20796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20796; decide +kernel
    rw [ha]
    exact (canonical20796 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1293 + difference 1 3) (sourceB1293 + difference 3 1) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4564) := by
    have ha : (tripleCharges (sourceA1293 + difference 1 3) (sourceB1293 + difference 3 1) sourceC1293) = raw20797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20797; decide +kernel
    rw [ha]
    exact (canonical20797 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1293 + difference 1 4) (sourceB1293 + difference 4 1) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1293 + difference 1 4) (sourceB1293 + difference 4 1) sourceC1293) = raw20421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20421; decide +kernel
    rw [ha]
    exact (canonical20421 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1293 + difference 1 5) (sourceB1293 + difference 5 1) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1293 + difference 1 5) (sourceB1293 + difference 5 1) sourceC1293) = raw20798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20798; decide +kernel
    rw [ha]
    exact (canonical20798 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1293 + difference 2 0) (sourceB1293 + difference 0 2) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1293 + difference 2 0) (sourceB1293 + difference 0 2) sourceC1293) = raw20799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20799; decide +kernel
    rw [ha]
    exact (canonical20799 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1293 + difference 2 1) (sourceB1293 + difference 1 2) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4577) := by
    have ha : (tripleCharges (sourceA1293 + difference 2 1) (sourceB1293 + difference 1 2) sourceC1293) = raw20800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20800; decide +kernel
    rw [ha]
    exact (canonical20800 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1293 + difference 2 3) (sourceB1293 + difference 3 2) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4564) := by
    have ha : (tripleCharges (sourceA1293 + difference 2 3) (sourceB1293 + difference 3 2) sourceC1293) = raw20801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20801; decide +kernel
    rw [ha]
    exact (canonical20801 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1293 + difference 2 4) (sourceB1293 + difference 4 2) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1293 + difference 2 4) (sourceB1293 + difference 4 2) sourceC1293) = raw20426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20426; decide +kernel
    rw [ha]
    exact (canonical20426 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1293 + difference 2 5) (sourceB1293 + difference 5 2) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1293 + difference 2 5) (sourceB1293 + difference 5 2) sourceC1293) = raw20802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20802; decide +kernel
    rw [ha]
    exact (canonical20802 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1293 + difference 3 0) (sourceB1293 + difference 0 3) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1293 + difference 3 0) (sourceB1293 + difference 0 3) sourceC1293) = raw20434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20434; decide +kernel
    rw [ha]
    exact (canonical20434 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1293 + difference 3 1) (sourceB1293 + difference 1 3) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1293 + difference 3 1) (sourceB1293 + difference 1 3) sourceC1293) = raw20435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20435; decide +kernel
    rw [ha]
    exact (canonical20435 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1293 + difference 3 2) (sourceB1293 + difference 2 3) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1293 + difference 3 2) (sourceB1293 + difference 2 3) sourceC1293) = raw20436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20436; decide +kernel
    rw [ha]
    exact (canonical20436 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1293 + difference 3 4) (sourceB1293 + difference 4 3) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1293 + difference 3 4) (sourceB1293 + difference 4 3) sourceC1293) = raw20584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20584; decide +kernel
    rw [ha]
    exact (canonical20584 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1293 + difference 3 5) (sourceB1293 + difference 5 3) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1293 + difference 3 5) (sourceB1293 + difference 5 3) sourceC1293) = raw20438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20438; decide +kernel
    rw [ha]
    exact (canonical20438 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1293 + difference 4 0) (sourceB1293 + difference 0 4) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1293 + difference 4 0) (sourceB1293 + difference 0 4) sourceC1293) = raw20803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20803; decide +kernel
    rw [ha]
    exact (canonical20803 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1293 + difference 4 1) (sourceB1293 + difference 1 4) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4584) := by
    have ha : (tripleCharges (sourceA1293 + difference 4 1) (sourceB1293 + difference 1 4) sourceC1293) = raw20804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20804; decide +kernel
    rw [ha]
    exact (canonical20804 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1293 + difference 4 2) (sourceB1293 + difference 2 4) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4584) := by
    have ha : (tripleCharges (sourceA1293 + difference 4 2) (sourceB1293 + difference 2 4) sourceC1293) = raw20805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20805; decide +kernel
    rw [ha]
    exact (canonical20805 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1293 + difference 4 3) (sourceB1293 + difference 3 4) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4573) := by
    have ha : (tripleCharges (sourceA1293 + difference 4 3) (sourceB1293 + difference 3 4) sourceC1293) = raw20806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20806; decide +kernel
    rw [ha]
    exact (canonical20806 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1293 + difference 4 5) (sourceB1293 + difference 5 4) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1293 + difference 4 5) (sourceB1293 + difference 5 4) sourceC1293) = raw20807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20807; decide +kernel
    rw [ha]
    exact (canonical20807 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1293 + difference 5 0) (sourceB1293 + difference 0 5) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4426) := by
    have ha : (tripleCharges (sourceA1293 + difference 5 0) (sourceB1293 + difference 0 5) sourceC1293) = raw20808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20808; decide +kernel
    rw [ha]
    exact (canonical20808 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1293 + difference 5 1) (sourceB1293 + difference 1 5) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA1293 + difference 5 1) (sourceB1293 + difference 1 5) sourceC1293) = raw20809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20809; decide +kernel
    rw [ha]
    exact (canonical20809 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1293 + difference 5 2) (sourceB1293 + difference 2 5) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA1293 + difference 5 2) (sourceB1293 + difference 2 5) sourceC1293) = raw20810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20810; decide +kernel
    rw [ha]
    exact (canonical20810 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1293 + difference 5 3) (sourceB1293 + difference 3 5) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA1293 + difference 5 3) (sourceB1293 + difference 3 5) sourceC1293) = raw20811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20811; decide +kernel
    rw [ha]
    exact (canonical20811 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1293 + difference 5 4) (sourceB1293 + difference 4 5) sourceC1293) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1293 + difference 5 4) (sourceB1293 + difference 4 5) sourceC1293) = raw20442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1293 sourceB1293 sourceC1293 difference raw20442; decide +kernel
    rw [ha]
    exact (canonical20442 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1293 sourceB1293 sourceC1293
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1293, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1294 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceB1294 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC1294 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1294 : Integer.Sparse Master := [(Sum.inr 982, 2), (Sum.inr 1007, 1), (Sum.inr 1009, 1), (Sum.inr 1089, 1), (Sum.inr 1181, 2), (Sum.inr 1190, 1), (Sum.inr 1191, 1), (Sum.inr 1195, 2), (Sum.inr 1202, 2), (Sum.inr 1203, 2), (Sum.inr 1215, 2), (Sum.inr 1217, 2), (Sum.inr 1239, 1), (Sum.inr 1242, 2), (Sum.inr 1243, 1), (Sum.inr 1304, 1), (Sum.inr 1307, 1), (Sum.inr 1372, 1), (Sum.inr 1388, 2), (Sum.inr 1413, 1), (Sum.inr 1416, 1)]

theorem sourceEq1294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1294 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1294 + difference 0 1) (sourceB1294 + difference 1 0) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA1294 + difference 0 1) (sourceB1294 + difference 1 0) sourceC1294) = raw20812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20812; decide +kernel
    rw [ha]
    exact (canonical20812 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1294 + difference 0 2) (sourceB1294 + difference 2 0) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA1294 + difference 0 2) (sourceB1294 + difference 2 0) sourceC1294) = raw20813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20813; decide +kernel
    rw [ha]
    exact (canonical20813 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1294 + difference 0 3) (sourceB1294 + difference 3 0) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA1294 + difference 0 3) (sourceB1294 + difference 3 0) sourceC1294) = raw20814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20814; decide +kernel
    rw [ha]
    exact (canonical20814 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1294 + difference 0 4) (sourceB1294 + difference 4 0) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1413) := by
    have ha : (tripleCharges (sourceA1294 + difference 0 4) (sourceB1294 + difference 4 0) sourceC1294) = raw20815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20815; decide +kernel
    rw [ha]
    exact (canonical20815 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1294 + difference 0 5) (sourceB1294 + difference 5 0) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1294 + difference 0 5) (sourceB1294 + difference 5 0) sourceC1294) = raw20816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20816; decide +kernel
    rw [ha]
    exact (canonical20816 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1294 + difference 1 0) (sourceB1294 + difference 0 1) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1294 + difference 1 0) (sourceB1294 + difference 0 1) sourceC1294) = raw20817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20817; decide +kernel
    rw [ha]
    exact (canonical20817 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1294 + difference 1 2) (sourceB1294 + difference 2 1) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1195) := by
    have ha : (tripleCharges (sourceA1294 + difference 1 2) (sourceB1294 + difference 2 1) sourceC1294) = raw20818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20818; decide +kernel
    rw [ha]
    exact (canonical20818 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1294 + difference 1 3) (sourceB1294 + difference 3 1) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1181) := by
    have ha : (tripleCharges (sourceA1294 + difference 1 3) (sourceB1294 + difference 3 1) sourceC1294) = raw20819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20819; decide +kernel
    rw [ha]
    exact (canonical20819 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1294 + difference 1 4) (sourceB1294 + difference 4 1) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA1294 + difference 1 4) (sourceB1294 + difference 4 1) sourceC1294) = raw20820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20820; decide +kernel
    rw [ha]
    exact (canonical20820 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1294 + difference 1 5) (sourceB1294 + difference 5 1) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1294 + difference 1 5) (sourceB1294 + difference 5 1) sourceC1294) = raw20821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20821; decide +kernel
    rw [ha]
    exact (canonical20821 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1294 + difference 2 0) (sourceB1294 + difference 0 2) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1294 + difference 2 0) (sourceB1294 + difference 0 2) sourceC1294) = raw20822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20822; decide +kernel
    rw [ha]
    exact (canonical20822 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1294 + difference 2 1) (sourceB1294 + difference 1 2) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1195) := by
    have ha : (tripleCharges (sourceA1294 + difference 2 1) (sourceB1294 + difference 1 2) sourceC1294) = raw20823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20823; decide +kernel
    rw [ha]
    exact (canonical20823 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1294 + difference 2 3) (sourceB1294 + difference 3 2) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1181) := by
    have ha : (tripleCharges (sourceA1294 + difference 2 3) (sourceB1294 + difference 3 2) sourceC1294) = raw20824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20824; decide +kernel
    rw [ha]
    exact (canonical20824 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1294 + difference 2 4) (sourceB1294 + difference 4 2) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA1294 + difference 2 4) (sourceB1294 + difference 4 2) sourceC1294) = raw20825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20825; decide +kernel
    rw [ha]
    exact (canonical20825 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1294 + difference 2 5) (sourceB1294 + difference 5 2) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1294 + difference 2 5) (sourceB1294 + difference 5 2) sourceC1294) = raw20826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20826; decide +kernel
    rw [ha]
    exact (canonical20826 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1294 + difference 3 0) (sourceB1294 + difference 0 3) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1089) := by
    have ha : (tripleCharges (sourceA1294 + difference 3 0) (sourceB1294 + difference 0 3) sourceC1294) = raw20827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20827; decide +kernel
    rw [ha]
    exact (canonical20827 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1294 + difference 3 1) (sourceB1294 + difference 1 3) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1294 + difference 3 1) (sourceB1294 + difference 1 3) sourceC1294) = raw20828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20828; decide +kernel
    rw [ha]
    exact (canonical20828 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1294 + difference 3 2) (sourceB1294 + difference 2 3) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1294 + difference 3 2) (sourceB1294 + difference 2 3) sourceC1294) = raw20829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20829; decide +kernel
    rw [ha]
    exact (canonical20829 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1294 + difference 3 4) (sourceB1294 + difference 4 3) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1304) := by
    have ha : (tripleCharges (sourceA1294 + difference 3 4) (sourceB1294 + difference 4 3) sourceC1294) = raw20614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20614; decide +kernel
    rw [ha]
    exact (canonical20614 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1294 + difference 3 5) (sourceB1294 + difference 5 3) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1294 + difference 3 5) (sourceB1294 + difference 5 3) sourceC1294) = raw20830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20830; decide +kernel
    rw [ha]
    exact (canonical20830 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1294 + difference 4 0) (sourceB1294 + difference 0 4) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA1294 + difference 4 0) (sourceB1294 + difference 0 4) sourceC1294) = raw20831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20831; decide +kernel
    rw [ha]
    exact (canonical20831 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1294 + difference 4 1) (sourceB1294 + difference 1 4) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1203) := by
    have ha : (tripleCharges (sourceA1294 + difference 4 1) (sourceB1294 + difference 1 4) sourceC1294) = raw20832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20832; decide +kernel
    rw [ha]
    exact (canonical20832 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1294 + difference 4 2) (sourceB1294 + difference 2 4) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1203) := by
    have ha : (tripleCharges (sourceA1294 + difference 4 2) (sourceB1294 + difference 2 4) sourceC1294) = raw20833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20833; decide +kernel
    rw [ha]
    exact (canonical20833 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1294 + difference 4 3) (sourceB1294 + difference 3 4) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1191) := by
    have ha : (tripleCharges (sourceA1294 + difference 4 3) (sourceB1294 + difference 3 4) sourceC1294) = raw20834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20834; decide +kernel
    rw [ha]
    exact (canonical20834 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1294 + difference 4 5) (sourceB1294 + difference 5 4) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1294 + difference 4 5) (sourceB1294 + difference 5 4) sourceC1294) = raw20835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20835; decide +kernel
    rw [ha]
    exact (canonical20835 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1294 + difference 5 0) (sourceB1294 + difference 0 5) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1007) := by
    have ha : (tripleCharges (sourceA1294 + difference 5 0) (sourceB1294 + difference 0 5) sourceC1294) = raw20836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20836; decide +kernel
    rw [ha]
    exact (canonical20836 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1294 + difference 5 1) (sourceB1294 + difference 1 5) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA1294 + difference 5 1) (sourceB1294 + difference 1 5) sourceC1294) = raw20837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20837; decide +kernel
    rw [ha]
    exact (canonical20837 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1294 + difference 5 2) (sourceB1294 + difference 2 5) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA1294 + difference 5 2) (sourceB1294 + difference 2 5) sourceC1294) = raw20838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20838; decide +kernel
    rw [ha]
    exact (canonical20838 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1294 + difference 5 3) (sourceB1294 + difference 3 5) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA1294 + difference 5 3) (sourceB1294 + difference 3 5) sourceC1294) = raw20839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20839; decide +kernel
    rw [ha]
    exact (canonical20839 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1294 + difference 5 4) (sourceB1294 + difference 4 5) sourceC1294) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1294 + difference 5 4) (sourceB1294 + difference 4 5) sourceC1294) = raw20613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1294 sourceB1294 sourceC1294 difference raw20613; decide +kernel
    rw [ha]
    exact (canonical20613 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1294 sourceB1294 sourceC1294
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1294, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1295 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceB1295 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC1295 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1295 : Integer.Sparse Master := [(Sum.inr 1617, 2), (Sum.inr 1625, 1), (Sum.inr 1630, 1), (Sum.inr 1754, 1), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

theorem sourceEq1295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1295 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1295 + difference 0 0) (sourceB1295 + difference 0 0) sourceC1295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1295 + difference 0 0) (sourceB1295 + difference 0 0) sourceC1295) = raw20482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1295 sourceB1295 sourceC1295 difference raw20482; decide +kernel
    rw [ha]
    exact (canonical20482 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1295 + difference 1 0) (sourceB1295 + difference 0 1) sourceC1295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1617) := by
    have ha : (tripleCharges (sourceA1295 + difference 1 0) (sourceB1295 + difference 0 1) sourceC1295) = raw20840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1295 sourceB1295 sourceC1295 difference raw20840; decide +kernel
    rw [ha]
    exact (canonical20840 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1295 + difference 2 0) (sourceB1295 + difference 0 2) sourceC1295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1617) := by
    have ha : (tripleCharges (sourceA1295 + difference 2 0) (sourceB1295 + difference 0 2) sourceC1295) = raw20841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1295 sourceB1295 sourceC1295 difference raw20841; decide +kernel
    rw [ha]
    exact (canonical20841 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1295 + difference 3 0) (sourceB1295 + difference 0 3) sourceC1295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA1295 + difference 3 0) (sourceB1295 + difference 0 3) sourceC1295) = raw20479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1295 sourceB1295 sourceC1295 difference raw20479; decide +kernel
    rw [ha]
    exact (canonical20479 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1295 + difference 4 0) (sourceB1295 + difference 0 4) sourceC1295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1630) := by
    have ha : (tripleCharges (sourceA1295 + difference 4 0) (sourceB1295 + difference 0 4) sourceC1295) = raw20842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1295 sourceB1295 sourceC1295 difference raw20842; decide +kernel
    rw [ha]
    exact (canonical20842 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1295 + difference 5 0) (sourceB1295 + difference 0 5) sourceC1295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1625) := by
    have ha : (tripleCharges (sourceA1295 + difference 5 0) (sourceB1295 + difference 0 5) sourceC1295) = raw20843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1295 sourceB1295 sourceC1295 difference raw20843; decide +kernel
    rw [ha]
    exact (canonical20843 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1295 + sourceB1295) sourceC1295) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1295 + sourceB1295) sourceC1295) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1295 sourceB1295 sourceC1295 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1295 sourceB1295 sourceC1295
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1295, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1296 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1296 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1296 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm1296 : Integer.Sparse Master := [(Sum.inr 4157, 2), (Sum.inr 4159, 1), (Sum.inr 4162, 1), (Sum.inr 4184, 1), (Sum.inr 4330, 2), (Sum.inr 4356, 1), (Sum.inr 4468, 1), (Sum.inr 4532, 2), (Sum.inr 4536, 2), (Sum.inr 4543, 2), (Sum.inr 4552, 2), (Sum.inr 4557, 1), (Sum.inr 4600, 2), (Sum.inr 4605, 2), (Sum.inr 4611, 1), (Sum.inr 4617, 1), (Sum.inr 4621, 1), (Sum.inr 4804, 2), (Sum.inr 4841, 1), (Sum.inr 4897, 1), (Sum.inr 5272, 1)]

theorem sourceEq1296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1296 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1296 + difference 0 1) (sourceB1296 + difference 1 0) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA1296 + difference 0 1) (sourceB1296 + difference 1 0) sourceC1296) = raw10608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10608; decide +kernel
    rw [ha]
    exact (canonical10608 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1296 + difference 0 2) (sourceB1296 + difference 2 0) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA1296 + difference 0 2) (sourceB1296 + difference 2 0) sourceC1296) = raw10609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10609; decide +kernel
    rw [ha]
    exact (canonical10609 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1296 + difference 0 3) (sourceB1296 + difference 3 0) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1296 + difference 0 3) (sourceB1296 + difference 3 0) sourceC1296) = raw10610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10610; decide +kernel
    rw [ha]
    exact (canonical10610 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1296 + difference 0 4) (sourceB1296 + difference 4 0) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1296 + difference 0 4) (sourceB1296 + difference 4 0) sourceC1296) = raw10611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10611; decide +kernel
    rw [ha]
    exact (canonical10611 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1296 + difference 0 5) (sourceB1296 + difference 5 0) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA1296 + difference 0 5) (sourceB1296 + difference 5 0) sourceC1296) = raw20844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20844; decide +kernel
    rw [ha]
    exact (canonical20844 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1296 + difference 1 0) (sourceB1296 + difference 0 1) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4157) := by
    have ha : (tripleCharges (sourceA1296 + difference 1 0) (sourceB1296 + difference 0 1) sourceC1296) = raw20845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20845; decide +kernel
    rw [ha]
    exact (canonical20845 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1296 + difference 1 2) (sourceB1296 + difference 2 1) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4532) := by
    have ha : (tripleCharges (sourceA1296 + difference 1 2) (sourceB1296 + difference 2 1) sourceC1296) = raw20846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20846; decide +kernel
    rw [ha]
    exact (canonical20846 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1296 + difference 1 3) (sourceB1296 + difference 3 1) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA1296 + difference 1 3) (sourceB1296 + difference 3 1) sourceC1296) = raw20847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20847; decide +kernel
    rw [ha]
    exact (canonical20847 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1296 + difference 1 4) (sourceB1296 + difference 4 1) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1296 + difference 1 4) (sourceB1296 + difference 4 1) sourceC1296) = raw20848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20848; decide +kernel
    rw [ha]
    exact (canonical20848 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1296 + difference 1 5) (sourceB1296 + difference 5 1) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1296 + difference 1 5) (sourceB1296 + difference 5 1) sourceC1296) = raw10587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10587; decide +kernel
    rw [ha]
    exact (canonical10587 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1296 + difference 2 0) (sourceB1296 + difference 0 2) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4157) := by
    have ha : (tripleCharges (sourceA1296 + difference 2 0) (sourceB1296 + difference 0 2) sourceC1296) = raw20849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20849; decide +kernel
    rw [ha]
    exact (canonical20849 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1296 + difference 2 1) (sourceB1296 + difference 1 2) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4532) := by
    have ha : (tripleCharges (sourceA1296 + difference 2 1) (sourceB1296 + difference 1 2) sourceC1296) = raw20850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20850; decide +kernel
    rw [ha]
    exact (canonical20850 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1296 + difference 2 3) (sourceB1296 + difference 3 2) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA1296 + difference 2 3) (sourceB1296 + difference 3 2) sourceC1296) = raw20851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20851; decide +kernel
    rw [ha]
    exact (canonical20851 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1296 + difference 2 4) (sourceB1296 + difference 4 2) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1296 + difference 2 4) (sourceB1296 + difference 4 2) sourceC1296) = raw20852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20852; decide +kernel
    rw [ha]
    exact (canonical20852 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1296 + difference 2 5) (sourceB1296 + difference 5 2) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1296 + difference 2 5) (sourceB1296 + difference 5 2) sourceC1296) = raw10592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10592; decide +kernel
    rw [ha]
    exact (canonical10592 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1296 + difference 3 0) (sourceB1296 + difference 0 3) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4184) := by
    have ha : (tripleCharges (sourceA1296 + difference 3 0) (sourceB1296 + difference 0 3) sourceC1296) = raw20853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20853; decide +kernel
    rw [ha]
    exact (canonical20853 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1296 + difference 3 1) (sourceB1296 + difference 1 3) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1296 + difference 3 1) (sourceB1296 + difference 1 3) sourceC1296) = raw20854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20854; decide +kernel
    rw [ha]
    exact (canonical20854 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1296 + difference 3 2) (sourceB1296 + difference 2 3) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1296 + difference 3 2) (sourceB1296 + difference 2 3) sourceC1296) = raw20855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20855; decide +kernel
    rw [ha]
    exact (canonical20855 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1296 + difference 3 4) (sourceB1296 + difference 4 3) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA1296 + difference 3 4) (sourceB1296 + difference 4 3) sourceC1296) = raw20856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20856; decide +kernel
    rw [ha]
    exact (canonical20856 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1296 + difference 3 5) (sourceB1296 + difference 5 3) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1296 + difference 3 5) (sourceB1296 + difference 5 3) sourceC1296) = raw10597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10597; decide +kernel
    rw [ha]
    exact (canonical10597 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1296 + difference 4 0) (sourceB1296 + difference 0 4) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4162) := by
    have ha : (tripleCharges (sourceA1296 + difference 4 0) (sourceB1296 + difference 0 4) sourceC1296) = raw20857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20857; decide +kernel
    rw [ha]
    exact (canonical20857 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1296 + difference 4 1) (sourceB1296 + difference 1 4) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4536) := by
    have ha : (tripleCharges (sourceA1296 + difference 4 1) (sourceB1296 + difference 1 4) sourceC1296) = raw20858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20858; decide +kernel
    rw [ha]
    exact (canonical20858 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1296 + difference 4 2) (sourceB1296 + difference 2 4) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4536) := by
    have ha : (tripleCharges (sourceA1296 + difference 4 2) (sourceB1296 + difference 2 4) sourceC1296) = raw20859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20859; decide +kernel
    rw [ha]
    exact (canonical20859 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1296 + difference 4 3) (sourceB1296 + difference 3 4) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4557) := by
    have ha : (tripleCharges (sourceA1296 + difference 4 3) (sourceB1296 + difference 3 4) sourceC1296) = raw20860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20860; decide +kernel
    rw [ha]
    exact (canonical20860 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1296 + difference 4 5) (sourceB1296 + difference 5 4) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1296 + difference 4 5) (sourceB1296 + difference 5 4) sourceC1296) = raw10602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10602; decide +kernel
    rw [ha]
    exact (canonical10602 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1296 + difference 5 0) (sourceB1296 + difference 0 5) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4159) := by
    have ha : (tripleCharges (sourceA1296 + difference 5 0) (sourceB1296 + difference 0 5) sourceC1296) = raw20861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20861; decide +kernel
    rw [ha]
    exact (canonical20861 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1296 + difference 5 1) (sourceB1296 + difference 1 5) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1296 + difference 5 1) (sourceB1296 + difference 1 5) sourceC1296) = raw20862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20862; decide +kernel
    rw [ha]
    exact (canonical20862 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1296 + difference 5 2) (sourceB1296 + difference 2 5) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1296 + difference 5 2) (sourceB1296 + difference 2 5) sourceC1296) = raw20863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20863; decide +kernel
    rw [ha]
    exact (canonical20863 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1296 + difference 5 3) (sourceB1296 + difference 3 5) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1296 + difference 5 3) (sourceB1296 + difference 3 5) sourceC1296) = raw20864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20864; decide +kernel
    rw [ha]
    exact (canonical20864 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1296 + difference 5 4) (sourceB1296 + difference 4 5) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1296 + difference 5 4) (sourceB1296 + difference 4 5) sourceC1296) = raw20865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20865; decide +kernel
    rw [ha]
    exact (canonical20865 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1296 sourceB1296 sourceC1296
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1296, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1297 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1297 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1297 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm1297 : Integer.Sparse Master := [(Sum.inr 585, 2), (Sum.inr 587, 1), (Sum.inr 590, 1), (Sum.inr 612, 1), (Sum.inr 1116, 2), (Sum.inr 1118, 2), (Sum.inr 1121, 2), (Sum.inr 1137, 2), (Sum.inr 1170, 2), (Sum.inr 1173, 1), (Sum.inr 1177, 1), (Sum.inr 1270, 2), (Sum.inr 1271, 2), (Sum.inr 1273, 1), (Sum.inr 1275, 1), (Sum.inr 1306, 1), (Sum.inr 1308, 1), (Sum.inr 2941, 2), (Sum.inr 3004, 1), (Sum.inr 3113, 1), (Sum.inr 3114, 1)]

theorem sourceEq1297 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1297 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1297 + difference 0 1) (sourceB1297 + difference 1 0) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA1297 + difference 0 1) (sourceB1297 + difference 1 0) sourceC1297) = raw10638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10638; decide +kernel
    rw [ha]
    exact (canonical10638 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1297 + difference 0 2) (sourceB1297 + difference 2 0) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA1297 + difference 0 2) (sourceB1297 + difference 2 0) sourceC1297) = raw10639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10639; decide +kernel
    rw [ha]
    exact (canonical10639 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1297 + difference 0 3) (sourceB1297 + difference 3 0) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3004) := by
    have ha : (tripleCharges (sourceA1297 + difference 0 3) (sourceB1297 + difference 3 0) sourceC1297) = raw10640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10640; decide +kernel
    rw [ha]
    exact (canonical10640 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1297 + difference 0 4) (sourceB1297 + difference 4 0) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA1297 + difference 0 4) (sourceB1297 + difference 4 0) sourceC1297) = raw10641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10641; decide +kernel
    rw [ha]
    exact (canonical10641 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1297 + difference 0 5) (sourceB1297 + difference 5 0) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3113) := by
    have ha : (tripleCharges (sourceA1297 + difference 0 5) (sourceB1297 + difference 5 0) sourceC1297) = raw20866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20866; decide +kernel
    rw [ha]
    exact (canonical20866 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1297 + difference 1 0) (sourceB1297 + difference 0 1) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 585) := by
    have ha : (tripleCharges (sourceA1297 + difference 1 0) (sourceB1297 + difference 0 1) sourceC1297) = raw20867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20867; decide +kernel
    rw [ha]
    exact (canonical20867 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1297 + difference 1 2) (sourceB1297 + difference 2 1) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1116) := by
    have ha : (tripleCharges (sourceA1297 + difference 1 2) (sourceB1297 + difference 2 1) sourceC1297) = raw20868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20868; decide +kernel
    rw [ha]
    exact (canonical20868 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1297 + difference 1 3) (sourceB1297 + difference 3 1) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1170) := by
    have ha : (tripleCharges (sourceA1297 + difference 1 3) (sourceB1297 + difference 3 1) sourceC1297) = raw20869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20869; decide +kernel
    rw [ha]
    exact (canonical20869 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1297 + difference 1 4) (sourceB1297 + difference 4 1) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1297 + difference 1 4) (sourceB1297 + difference 4 1) sourceC1297) = raw20870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20870; decide +kernel
    rw [ha]
    exact (canonical20870 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1297 + difference 1 5) (sourceB1297 + difference 5 1) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA1297 + difference 1 5) (sourceB1297 + difference 5 1) sourceC1297) = raw10617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10617; decide +kernel
    rw [ha]
    exact (canonical10617 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1297 + difference 2 0) (sourceB1297 + difference 0 2) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 585) := by
    have ha : (tripleCharges (sourceA1297 + difference 2 0) (sourceB1297 + difference 0 2) sourceC1297) = raw20871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20871; decide +kernel
    rw [ha]
    exact (canonical20871 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1297 + difference 2 1) (sourceB1297 + difference 1 2) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1116) := by
    have ha : (tripleCharges (sourceA1297 + difference 2 1) (sourceB1297 + difference 1 2) sourceC1297) = raw20872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20872; decide +kernel
    rw [ha]
    exact (canonical20872 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1297 + difference 2 3) (sourceB1297 + difference 3 2) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1170) := by
    have ha : (tripleCharges (sourceA1297 + difference 2 3) (sourceB1297 + difference 3 2) sourceC1297) = raw20873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20873; decide +kernel
    rw [ha]
    exact (canonical20873 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1297 + difference 2 4) (sourceB1297 + difference 4 2) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1297 + difference 2 4) (sourceB1297 + difference 4 2) sourceC1297) = raw20874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20874; decide +kernel
    rw [ha]
    exact (canonical20874 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1297 + difference 2 5) (sourceB1297 + difference 5 2) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA1297 + difference 2 5) (sourceB1297 + difference 5 2) sourceC1297) = raw10622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10622; decide +kernel
    rw [ha]
    exact (canonical10622 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1297 + difference 3 0) (sourceB1297 + difference 0 3) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 612) := by
    have ha : (tripleCharges (sourceA1297 + difference 3 0) (sourceB1297 + difference 0 3) sourceC1297) = raw20875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20875; decide +kernel
    rw [ha]
    exact (canonical20875 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1297 + difference 3 1) (sourceB1297 + difference 1 3) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA1297 + difference 3 1) (sourceB1297 + difference 1 3) sourceC1297) = raw20876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20876; decide +kernel
    rw [ha]
    exact (canonical20876 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1297 + difference 3 2) (sourceB1297 + difference 2 3) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA1297 + difference 3 2) (sourceB1297 + difference 2 3) sourceC1297) = raw20877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20877; decide +kernel
    rw [ha]
    exact (canonical20877 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1297 + difference 3 4) (sourceB1297 + difference 4 3) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1308) := by
    have ha : (tripleCharges (sourceA1297 + difference 3 4) (sourceB1297 + difference 4 3) sourceC1297) = raw20878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20878; decide +kernel
    rw [ha]
    exact (canonical20878 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1297 + difference 3 5) (sourceB1297 + difference 5 3) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA1297 + difference 3 5) (sourceB1297 + difference 5 3) sourceC1297) = raw10627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10627; decide +kernel
    rw [ha]
    exact (canonical10627 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1297 + difference 4 0) (sourceB1297 + difference 0 4) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 590) := by
    have ha : (tripleCharges (sourceA1297 + difference 4 0) (sourceB1297 + difference 0 4) sourceC1297) = raw20879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20879; decide +kernel
    rw [ha]
    exact (canonical20879 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1297 + difference 4 1) (sourceB1297 + difference 1 4) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1121) := by
    have ha : (tripleCharges (sourceA1297 + difference 4 1) (sourceB1297 + difference 1 4) sourceC1297) = raw20880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20880; decide +kernel
    rw [ha]
    exact (canonical20880 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1297 + difference 4 2) (sourceB1297 + difference 2 4) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1121) := by
    have ha : (tripleCharges (sourceA1297 + difference 4 2) (sourceB1297 + difference 2 4) sourceC1297) = raw20881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20881; decide +kernel
    rw [ha]
    exact (canonical20881 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1297 + difference 4 3) (sourceB1297 + difference 3 4) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1177) := by
    have ha : (tripleCharges (sourceA1297 + difference 4 3) (sourceB1297 + difference 3 4) sourceC1297) = raw20882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20882; decide +kernel
    rw [ha]
    exact (canonical20882 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1297 + difference 4 5) (sourceB1297 + difference 5 4) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA1297 + difference 4 5) (sourceB1297 + difference 5 4) sourceC1297) = raw10632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10632; decide +kernel
    rw [ha]
    exact (canonical10632 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1297 + difference 5 0) (sourceB1297 + difference 0 5) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 587) := by
    have ha : (tripleCharges (sourceA1297 + difference 5 0) (sourceB1297 + difference 0 5) sourceC1297) = raw20883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20883; decide +kernel
    rw [ha]
    exact (canonical20883 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1297 + difference 5 1) (sourceB1297 + difference 1 5) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1297 + difference 5 1) (sourceB1297 + difference 1 5) sourceC1297) = raw20884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20884; decide +kernel
    rw [ha]
    exact (canonical20884 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1297 + difference 5 2) (sourceB1297 + difference 2 5) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1297 + difference 5 2) (sourceB1297 + difference 2 5) sourceC1297) = raw20885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20885; decide +kernel
    rw [ha]
    exact (canonical20885 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1297 + difference 5 3) (sourceB1297 + difference 3 5) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1173) := by
    have ha : (tripleCharges (sourceA1297 + difference 5 3) (sourceB1297 + difference 3 5) sourceC1297) = raw20886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20886; decide +kernel
    rw [ha]
    exact (canonical20886 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1297 + difference 5 4) (sourceB1297 + difference 4 5) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1297 + difference 5 4) (sourceB1297 + difference 4 5) sourceC1297) = raw20887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20887; decide +kernel
    rw [ha]
    exact (canonical20887 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1297 sourceB1297 sourceC1297
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1297, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1298 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1298 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1298 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm1298 : Integer.Sparse Master := [(Sum.inr 1528, 2), (Sum.inr 1529, 1), (Sum.inr 1530, 1), (Sum.inr 1532, 1), (Sum.inr 1672, 2), (Sum.inr 1692, 1), (Sum.inr 1752, 1), (Sum.inr 2149, 2), (Sum.inr 2167, 1), (Sum.inr 2172, 2), (Sum.inr 2184, 2), (Sum.inr 2200, 2), (Sum.inr 2203, 2), (Sum.inr 2226, 2), (Sum.inr 2228, 1), (Sum.inr 2289, 1), (Sum.inr 2292, 1), (Sum.inr 2683, 1), (Sum.inr 2702, 2), (Sum.inr 2737, 1), (Sum.inr 2740, 1)]

theorem sourceEq1298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1298 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1298 + difference 0 1) (sourceB1298 + difference 1 0) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1298 + difference 0 1) (sourceB1298 + difference 1 0) sourceC1298) = raw10668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10668; decide +kernel
    rw [ha]
    exact (canonical10668 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1298 + difference 0 2) (sourceB1298 + difference 2 0) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1298 + difference 0 2) (sourceB1298 + difference 2 0) sourceC1298) = raw10669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10669; decide +kernel
    rw [ha]
    exact (canonical10669 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1298 + difference 0 3) (sourceB1298 + difference 3 0) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA1298 + difference 0 3) (sourceB1298 + difference 3 0) sourceC1298) = raw10670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10670; decide +kernel
    rw [ha]
    exact (canonical10670 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1298 + difference 0 4) (sourceB1298 + difference 4 0) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA1298 + difference 0 4) (sourceB1298 + difference 4 0) sourceC1298) = raw10671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10671; decide +kernel
    rw [ha]
    exact (canonical10671 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1298 + difference 0 5) (sourceB1298 + difference 5 0) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA1298 + difference 0 5) (sourceB1298 + difference 5 0) sourceC1298) = raw20888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20888; decide +kernel
    rw [ha]
    exact (canonical20888 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1298 + difference 1 0) (sourceB1298 + difference 0 1) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1528) := by
    have ha : (tripleCharges (sourceA1298 + difference 1 0) (sourceB1298 + difference 0 1) sourceC1298) = raw20889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20889; decide +kernel
    rw [ha]
    exact (canonical20889 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1298 + difference 1 2) (sourceB1298 + difference 2 1) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2172) := by
    have ha : (tripleCharges (sourceA1298 + difference 1 2) (sourceB1298 + difference 2 1) sourceC1298) = raw20890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20890; decide +kernel
    rw [ha]
    exact (canonical20890 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1298 + difference 1 3) (sourceB1298 + difference 3 1) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2184) := by
    have ha : (tripleCharges (sourceA1298 + difference 1 3) (sourceB1298 + difference 3 1) sourceC1298) = raw20891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20891; decide +kernel
    rw [ha]
    exact (canonical20891 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1298 + difference 1 4) (sourceB1298 + difference 4 1) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1298 + difference 1 4) (sourceB1298 + difference 4 1) sourceC1298) = raw20892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20892; decide +kernel
    rw [ha]
    exact (canonical20892 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1298 + difference 1 5) (sourceB1298 + difference 5 1) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1298 + difference 1 5) (sourceB1298 + difference 5 1) sourceC1298) = raw10647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10647; decide +kernel
    rw [ha]
    exact (canonical10647 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1298 + difference 2 0) (sourceB1298 + difference 0 2) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1528) := by
    have ha : (tripleCharges (sourceA1298 + difference 2 0) (sourceB1298 + difference 0 2) sourceC1298) = raw20893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20893; decide +kernel
    rw [ha]
    exact (canonical20893 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1298 + difference 2 1) (sourceB1298 + difference 1 2) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2172) := by
    have ha : (tripleCharges (sourceA1298 + difference 2 1) (sourceB1298 + difference 1 2) sourceC1298) = raw20894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20894; decide +kernel
    rw [ha]
    exact (canonical20894 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1298 + difference 2 3) (sourceB1298 + difference 3 2) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2184) := by
    have ha : (tripleCharges (sourceA1298 + difference 2 3) (sourceB1298 + difference 3 2) sourceC1298) = raw20895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20895; decide +kernel
    rw [ha]
    exact (canonical20895 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1298 + difference 2 4) (sourceB1298 + difference 4 2) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1298 + difference 2 4) (sourceB1298 + difference 4 2) sourceC1298) = raw20896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20896; decide +kernel
    rw [ha]
    exact (canonical20896 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1298 + difference 2 5) (sourceB1298 + difference 5 2) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1298 + difference 2 5) (sourceB1298 + difference 5 2) sourceC1298) = raw10652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10652; decide +kernel
    rw [ha]
    exact (canonical10652 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1298 + difference 3 0) (sourceB1298 + difference 0 3) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1530) := by
    have ha : (tripleCharges (sourceA1298 + difference 3 0) (sourceB1298 + difference 0 3) sourceC1298) = raw20897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20897; decide +kernel
    rw [ha]
    exact (canonical20897 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1298 + difference 3 1) (sourceB1298 + difference 1 3) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1298 + difference 3 1) (sourceB1298 + difference 1 3) sourceC1298) = raw20898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20898; decide +kernel
    rw [ha]
    exact (canonical20898 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1298 + difference 3 2) (sourceB1298 + difference 2 3) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1298 + difference 3 2) (sourceB1298 + difference 2 3) sourceC1298) = raw20899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20899; decide +kernel
    rw [ha]
    exact (canonical20899 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1298 + difference 3 4) (sourceB1298 + difference 4 3) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA1298 + difference 3 4) (sourceB1298 + difference 4 3) sourceC1298) = raw20900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20900; decide +kernel
    rw [ha]
    exact (canonical20900 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1298 + difference 3 5) (sourceB1298 + difference 5 3) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1298 + difference 3 5) (sourceB1298 + difference 5 3) sourceC1298) = raw10657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10657; decide +kernel
    rw [ha]
    exact (canonical10657 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1298 + difference 4 0) (sourceB1298 + difference 0 4) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1529) := by
    have ha : (tripleCharges (sourceA1298 + difference 4 0) (sourceB1298 + difference 0 4) sourceC1298) = raw20901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20901; decide +kernel
    rw [ha]
    exact (canonical20901 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1298 + difference 4 1) (sourceB1298 + difference 1 4) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2149) := by
    have ha : (tripleCharges (sourceA1298 + difference 4 1) (sourceB1298 + difference 1 4) sourceC1298) = raw20902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20902; decide +kernel
    rw [ha]
    exact (canonical20902 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1298 + difference 4 2) (sourceB1298 + difference 2 4) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2149) := by
    have ha : (tripleCharges (sourceA1298 + difference 4 2) (sourceB1298 + difference 2 4) sourceC1298) = raw20903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20903; decide +kernel
    rw [ha]
    exact (canonical20903 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1298 + difference 4 3) (sourceB1298 + difference 3 4) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2167) := by
    have ha : (tripleCharges (sourceA1298 + difference 4 3) (sourceB1298 + difference 3 4) sourceC1298) = raw20904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20904; decide +kernel
    rw [ha]
    exact (canonical20904 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1298 + difference 4 5) (sourceB1298 + difference 5 4) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1298 + difference 4 5) (sourceB1298 + difference 5 4) sourceC1298) = raw10662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10662; decide +kernel
    rw [ha]
    exact (canonical10662 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1298 + difference 5 0) (sourceB1298 + difference 0 5) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA1298 + difference 5 0) (sourceB1298 + difference 0 5) sourceC1298) = raw20905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20905; decide +kernel
    rw [ha]
    exact (canonical20905 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1298 + difference 5 1) (sourceB1298 + difference 1 5) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1298 + difference 5 1) (sourceB1298 + difference 1 5) sourceC1298) = raw20906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20906; decide +kernel
    rw [ha]
    exact (canonical20906 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1298 + difference 5 2) (sourceB1298 + difference 2 5) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1298 + difference 5 2) (sourceB1298 + difference 2 5) sourceC1298) = raw20907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20907; decide +kernel
    rw [ha]
    exact (canonical20907 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1298 + difference 5 3) (sourceB1298 + difference 3 5) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA1298 + difference 5 3) (sourceB1298 + difference 3 5) sourceC1298) = raw20908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20908; decide +kernel
    rw [ha]
    exact (canonical20908 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1298 + difference 5 4) (sourceB1298 + difference 4 5) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1298 + difference 5 4) (sourceB1298 + difference 4 5) sourceC1298) = raw20909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20909; decide +kernel
    rw [ha]
    exact (canonical20909 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1298 sourceB1298 sourceC1298
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1298, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1299 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1299 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1299 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm1299 : Integer.Sparse Master := [(Sum.inr 624, 2), (Sum.inr 628, 1), (Sum.inr 634, 1), (Sum.inr 639, 1), (Sum.inr 1239, 1), (Sum.inr 4084, -1)]

theorem sourceEq1299 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1299 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1299 + difference 0 0) (sourceB1299 + difference 0 0) sourceC1299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1299 + difference 0 0) (sourceB1299 + difference 0 0) sourceC1299) = raw20910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1299 sourceB1299 sourceC1299 difference raw20910; decide +kernel
    rw [ha]
    exact (canonical20910 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1299 + difference 1 0) (sourceB1299 + difference 0 1) sourceC1299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 624) := by
    have ha : (tripleCharges (sourceA1299 + difference 1 0) (sourceB1299 + difference 0 1) sourceC1299) = raw20911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1299 sourceB1299 sourceC1299 difference raw20911; decide +kernel
    rw [ha]
    exact (canonical20911 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1299 + difference 2 0) (sourceB1299 + difference 0 2) sourceC1299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 624) := by
    have ha : (tripleCharges (sourceA1299 + difference 2 0) (sourceB1299 + difference 0 2) sourceC1299) = raw20912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1299 sourceB1299 sourceC1299 difference raw20912; decide +kernel
    rw [ha]
    exact (canonical20912 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1299 + difference 3 0) (sourceB1299 + difference 0 3) sourceC1299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 639) := by
    have ha : (tripleCharges (sourceA1299 + difference 3 0) (sourceB1299 + difference 0 3) sourceC1299) = raw20913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1299 sourceB1299 sourceC1299 difference raw20913; decide +kernel
    rw [ha]
    exact (canonical20913 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1299 + difference 4 0) (sourceB1299 + difference 0 4) sourceC1299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 634) := by
    have ha : (tripleCharges (sourceA1299 + difference 4 0) (sourceB1299 + difference 0 4) sourceC1299) = raw20914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1299 sourceB1299 sourceC1299 difference raw20914; decide +kernel
    rw [ha]
    exact (canonical20914 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1299 + difference 5 0) (sourceB1299 + difference 0 5) sourceC1299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 628) := by
    have ha : (tripleCharges (sourceA1299 + difference 5 0) (sourceB1299 + difference 0 5) sourceC1299) = raw20915 := by
      apply Matrix.ext; unfold tripleCharges sourceA1299 sourceB1299 sourceC1299 difference raw20915; decide +kernel
    rw [ha]
    exact (canonical20915 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1299 + sourceB1299) sourceC1299) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1299 + sourceB1299) sourceC1299) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA1299 sourceB1299 sourceC1299 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1299 sourceB1299 sourceC1299
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1299, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1300 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1300 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1300 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm1300 : Integer.Sparse Master := [(Sum.inr 624, 1), (Sum.inr 1128, 1), (Sum.inr 1147, 1), (Sum.inr 1234, 1), (Sum.inr 1239, 2), (Sum.inr 4084, -1)]

theorem sourceEq1300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1300 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1300 + difference 1 0) (sourceB1300 + difference 0 1) sourceC1300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 624) := by
    have ha : (tripleCharges (sourceA1300 + difference 1 0) (sourceB1300 + difference 0 1) sourceC1300) = raw20911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1300 sourceB1300 sourceC1300 difference raw20911; decide +kernel
    rw [ha]
    exact (canonical20911 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1300 + difference 1 1) (sourceB1300 + difference 1 1) sourceC1300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1300 + difference 1 1) (sourceB1300 + difference 1 1) sourceC1300) = raw20910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1300 sourceB1300 sourceC1300 difference raw20910; decide +kernel
    rw [ha]
    exact (canonical20910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1300 + difference 1 2) (sourceB1300 + difference 2 1) sourceC1300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1147) := by
    have ha : (tripleCharges (sourceA1300 + difference 1 2) (sourceB1300 + difference 2 1) sourceC1300) = raw20917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1300 sourceB1300 sourceC1300 difference raw20917; decide +kernel
    rw [ha]
    exact (canonical20917 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1300 + difference 1 3) (sourceB1300 + difference 3 1) sourceC1300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1128) := by
    have ha : (tripleCharges (sourceA1300 + difference 1 3) (sourceB1300 + difference 3 1) sourceC1300) = raw20918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1300 sourceB1300 sourceC1300 difference raw20918; decide +kernel
    rw [ha]
    exact (canonical20918 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1300 + difference 1 4) (sourceB1300 + difference 4 1) sourceC1300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1300 + difference 1 4) (sourceB1300 + difference 4 1) sourceC1300) = raw20919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1300 sourceB1300 sourceC1300 difference raw20919; decide +kernel
    rw [ha]
    exact (canonical20919 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1300 + difference 1 5) (sourceB1300 + difference 5 1) sourceC1300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1234) := by
    have ha : (tripleCharges (sourceA1300 + difference 1 5) (sourceB1300 + difference 5 1) sourceC1300) = raw20920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1300 sourceB1300 sourceC1300 difference raw20920; decide +kernel
    rw [ha]
    exact (canonical20920 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1300 + sourceB1300) sourceC1300) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1300 + sourceB1300) sourceC1300) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA1300 sourceB1300 sourceC1300 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1300 sourceB1300 sourceC1300
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1300, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1301 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1301 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1301 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm1301 : Integer.Sparse Master := [(Sum.inr 908, 1), (Sum.inr 1147, 1), (Sum.inr 1153, 1), (Sum.inr 1157, 1), (Sum.inr 1239, 1), (Sum.inr 2022, 1), (Sum.inr 4084, -1)]

theorem sourceEq1301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1301 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1301 + difference 0 1) (sourceB1301 + difference 1 0) sourceC1301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA1301 + difference 0 1) (sourceB1301 + difference 1 0) sourceC1301) = raw20921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1301 sourceB1301 sourceC1301 difference raw20921; decide +kernel
    rw [ha]
    exact (canonical20921 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1301 + difference 1 1) (sourceB1301 + difference 1 1) sourceC1301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1301 + difference 1 1) (sourceB1301 + difference 1 1) sourceC1301) = raw20910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1301 sourceB1301 sourceC1301 difference raw20910; decide +kernel
    rw [ha]
    exact (canonical20910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1301 + difference 2 1) (sourceB1301 + difference 1 2) sourceC1301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1147) := by
    have ha : (tripleCharges (sourceA1301 + difference 2 1) (sourceB1301 + difference 1 2) sourceC1301) = raw20922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1301 sourceB1301 sourceC1301 difference raw20922; decide +kernel
    rw [ha]
    exact (canonical20922 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1301 + difference 3 1) (sourceB1301 + difference 1 3) sourceC1301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1157) := by
    have ha : (tripleCharges (sourceA1301 + difference 3 1) (sourceB1301 + difference 1 3) sourceC1301) = raw20923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1301 sourceB1301 sourceC1301 difference raw20923; decide +kernel
    rw [ha]
    exact (canonical20923 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1301 + difference 4 1) (sourceB1301 + difference 1 4) sourceC1301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1153) := by
    have ha : (tripleCharges (sourceA1301 + difference 4 1) (sourceB1301 + difference 1 4) sourceC1301) = raw20924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1301 sourceB1301 sourceC1301 difference raw20924; decide +kernel
    rw [ha]
    exact (canonical20924 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1301 + difference 5 1) (sourceB1301 + difference 1 5) sourceC1301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 908) := by
    have ha : (tripleCharges (sourceA1301 + difference 5 1) (sourceB1301 + difference 1 5) sourceC1301) = raw20925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1301 sourceB1301 sourceC1301 difference raw20925; decide +kernel
    rw [ha]
    exact (canonical20925 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1301 + sourceB1301) sourceC1301) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1301 + sourceB1301) sourceC1301) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA1301 sourceB1301 sourceC1301 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1301 sourceB1301 sourceC1301
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1301, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1302 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1302 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1302 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm1302 : Integer.Sparse Master := [(Sum.inr 934, 1), (Sum.inr 1128, 2), (Sum.inr 1143, 1), (Sum.inr 1239, 1), (Sum.inr 2060, 1), (Sum.inr 4084, -1)]

theorem sourceEq1302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1302 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1302 + difference 0 3) (sourceB1302 + difference 3 0) sourceC1302) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2060) := by
    have ha : (tripleCharges (sourceA1302 + difference 0 3) (sourceB1302 + difference 3 0) sourceC1302) = raw20926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1302 sourceB1302 sourceC1302 difference raw20926; decide +kernel
    rw [ha]
    exact (canonical20926 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1302 + difference 1 3) (sourceB1302 + difference 3 1) sourceC1302) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1128) := by
    have ha : (tripleCharges (sourceA1302 + difference 1 3) (sourceB1302 + difference 3 1) sourceC1302) = raw20918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1302 sourceB1302 sourceC1302 difference raw20918; decide +kernel
    rw [ha]
    exact (canonical20918 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1302 + difference 2 3) (sourceB1302 + difference 3 2) sourceC1302) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1128) := by
    have ha : (tripleCharges (sourceA1302 + difference 2 3) (sourceB1302 + difference 3 2) sourceC1302) = raw20927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1302 sourceB1302 sourceC1302 difference raw20927; decide +kernel
    rw [ha]
    exact (canonical20927 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1302 + difference 3 3) (sourceB1302 + difference 3 3) sourceC1302) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1302 + difference 3 3) (sourceB1302 + difference 3 3) sourceC1302) = raw20910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1302 sourceB1302 sourceC1302 difference raw20910; decide +kernel
    rw [ha]
    exact (canonical20910 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1302 + difference 4 3) (sourceB1302 + difference 3 4) sourceC1302) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1143) := by
    have ha : (tripleCharges (sourceA1302 + difference 4 3) (sourceB1302 + difference 3 4) sourceC1302) = raw20928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1302 sourceB1302 sourceC1302 difference raw20928; decide +kernel
    rw [ha]
    exact (canonical20928 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1302 + difference 5 3) (sourceB1302 + difference 3 5) sourceC1302) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1302 + difference 5 3) (sourceB1302 + difference 3 5) sourceC1302) = raw20929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1302 sourceB1302 sourceC1302 difference raw20929; decide +kernel
    rw [ha]
    exact (canonical20929 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1302 + sourceB1302) sourceC1302) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1302 + sourceB1302) sourceC1302) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA1302 sourceB1302 sourceC1302 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1302 sourceB1302 sourceC1302
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1302, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1303 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1303 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1303 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm1303 : Integer.Sparse Master := [(Sum.inr 4140, 2), (Sum.inr 4142, 1), (Sum.inr 4147, 1), (Sum.inr 4174, 1), (Sum.inr 4202, 2), (Sum.inr 4225, 1), (Sum.inr 4257, 1), (Sum.inr 4514, 2), (Sum.inr 4519, 1), (Sum.inr 4521, 2), (Sum.inr 4525, 2), (Sum.inr 4543, 2), (Sum.inr 4583, 2), (Sum.inr 4602, 2), (Sum.inr 4605, 1), (Sum.inr 4612, 1), (Sum.inr 4623, 1), (Sum.inr 4807, 2), (Sum.inr 4843, 1), (Sum.inr 4890, 1), (Sum.inr 5294, 1)]

theorem sourceEq1303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1303 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1303 + difference 0 1) (sourceB1303 + difference 1 0) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1303 + difference 0 1) (sourceB1303 + difference 1 0) sourceC1303) = raw4618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw4618; decide +kernel
    rw [ha]
    exact (canonical4618 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1303 + difference 0 2) (sourceB1303 + difference 2 0) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1303 + difference 0 2) (sourceB1303 + difference 2 0) sourceC1303) = raw4619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw4619; decide +kernel
    rw [ha]
    exact (canonical4619 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1303 + difference 0 3) (sourceB1303 + difference 3 0) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA1303 + difference 0 3) (sourceB1303 + difference 3 0) sourceC1303) = raw4620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw4620; decide +kernel
    rw [ha]
    exact (canonical4620 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1303 + difference 0 4) (sourceB1303 + difference 4 0) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA1303 + difference 0 4) (sourceB1303 + difference 4 0) sourceC1303) = raw2686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw2686; decide +kernel
    rw [ha]
    exact (canonical2686 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1303 + difference 0 5) (sourceB1303 + difference 5 0) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1303 + difference 0 5) (sourceB1303 + difference 5 0) sourceC1303) = raw2681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw2681; decide +kernel
    rw [ha]
    exact (canonical2681 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1303 + difference 1 0) (sourceB1303 + difference 0 1) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4140) := by
    have ha : (tripleCharges (sourceA1303 + difference 1 0) (sourceB1303 + difference 0 1) sourceC1303) = raw20930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20930; decide +kernel
    rw [ha]
    exact (canonical20930 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1303 + difference 1 2) (sourceB1303 + difference 2 1) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4521) := by
    have ha : (tripleCharges (sourceA1303 + difference 1 2) (sourceB1303 + difference 2 1) sourceC1303) = raw20931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20931; decide +kernel
    rw [ha]
    exact (canonical20931 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1303 + difference 1 3) (sourceB1303 + difference 3 1) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4514) := by
    have ha : (tripleCharges (sourceA1303 + difference 1 3) (sourceB1303 + difference 3 1) sourceC1303) = raw20932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20932; decide +kernel
    rw [ha]
    exact (canonical20932 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1303 + difference 1 4) (sourceB1303 + difference 4 1) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA1303 + difference 1 4) (sourceB1303 + difference 4 1) sourceC1303) = raw4605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw4605; decide +kernel
    rw [ha]
    exact (canonical4605 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1303 + difference 1 5) (sourceB1303 + difference 5 1) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1303 + difference 1 5) (sourceB1303 + difference 5 1) sourceC1303) = raw7968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw7968; decide +kernel
    rw [ha]
    exact (canonical7968 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1303 + difference 2 0) (sourceB1303 + difference 0 2) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4140) := by
    have ha : (tripleCharges (sourceA1303 + difference 2 0) (sourceB1303 + difference 0 2) sourceC1303) = raw20933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20933; decide +kernel
    rw [ha]
    exact (canonical20933 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1303 + difference 2 1) (sourceB1303 + difference 1 2) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4521) := by
    have ha : (tripleCharges (sourceA1303 + difference 2 1) (sourceB1303 + difference 1 2) sourceC1303) = raw20934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20934; decide +kernel
    rw [ha]
    exact (canonical20934 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1303 + difference 2 3) (sourceB1303 + difference 3 2) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4514) := by
    have ha : (tripleCharges (sourceA1303 + difference 2 3) (sourceB1303 + difference 3 2) sourceC1303) = raw20935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20935; decide +kernel
    rw [ha]
    exact (canonical20935 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1303 + difference 2 4) (sourceB1303 + difference 4 2) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA1303 + difference 2 4) (sourceB1303 + difference 4 2) sourceC1303) = raw4609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw4609; decide +kernel
    rw [ha]
    exact (canonical4609 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1303 + difference 2 5) (sourceB1303 + difference 5 2) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1303 + difference 2 5) (sourceB1303 + difference 5 2) sourceC1303) = raw7972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw7972; decide +kernel
    rw [ha]
    exact (canonical7972 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1303 + difference 3 0) (sourceB1303 + difference 0 3) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4174) := by
    have ha : (tripleCharges (sourceA1303 + difference 3 0) (sourceB1303 + difference 0 3) sourceC1303) = raw20936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20936; decide +kernel
    rw [ha]
    exact (canonical20936 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1303 + difference 3 1) (sourceB1303 + difference 1 3) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA1303 + difference 3 1) (sourceB1303 + difference 1 3) sourceC1303) = raw20937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20937; decide +kernel
    rw [ha]
    exact (canonical20937 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1303 + difference 3 2) (sourceB1303 + difference 2 3) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA1303 + difference 3 2) (sourceB1303 + difference 2 3) sourceC1303) = raw20938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20938; decide +kernel
    rw [ha]
    exact (canonical20938 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1303 + difference 3 4) (sourceB1303 + difference 4 3) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1303 + difference 3 4) (sourceB1303 + difference 4 3) sourceC1303) = raw4613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw4613; decide +kernel
    rw [ha]
    exact (canonical4613 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1303 + difference 3 5) (sourceB1303 + difference 5 3) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1303 + difference 3 5) (sourceB1303 + difference 5 3) sourceC1303) = raw7976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw7976; decide +kernel
    rw [ha]
    exact (canonical7976 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1303 + difference 4 0) (sourceB1303 + difference 0 4) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4147) := by
    have ha : (tripleCharges (sourceA1303 + difference 4 0) (sourceB1303 + difference 0 4) sourceC1303) = raw20939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20939; decide +kernel
    rw [ha]
    exact (canonical20939 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1303 + difference 4 1) (sourceB1303 + difference 1 4) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4525) := by
    have ha : (tripleCharges (sourceA1303 + difference 4 1) (sourceB1303 + difference 1 4) sourceC1303) = raw20940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20940; decide +kernel
    rw [ha]
    exact (canonical20940 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1303 + difference 4 2) (sourceB1303 + difference 2 4) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4525) := by
    have ha : (tripleCharges (sourceA1303 + difference 4 2) (sourceB1303 + difference 2 4) sourceC1303) = raw20941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20941; decide +kernel
    rw [ha]
    exact (canonical20941 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1303 + difference 4 3) (sourceB1303 + difference 3 4) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4519) := by
    have ha : (tripleCharges (sourceA1303 + difference 4 3) (sourceB1303 + difference 3 4) sourceC1303) = raw20942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20942; decide +kernel
    rw [ha]
    exact (canonical20942 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1303 + difference 4 5) (sourceB1303 + difference 5 4) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1303 + difference 4 5) (sourceB1303 + difference 5 4) sourceC1303) = raw7980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw7980; decide +kernel
    rw [ha]
    exact (canonical7980 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1303 + difference 5 0) (sourceB1303 + difference 0 5) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4142) := by
    have ha : (tripleCharges (sourceA1303 + difference 5 0) (sourceB1303 + difference 0 5) sourceC1303) = raw20943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20943; decide +kernel
    rw [ha]
    exact (canonical20943 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1303 + difference 5 1) (sourceB1303 + difference 1 5) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4202) := by
    have ha : (tripleCharges (sourceA1303 + difference 5 1) (sourceB1303 + difference 1 5) sourceC1303) = raw20944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20944; decide +kernel
    rw [ha]
    exact (canonical20944 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1303 + difference 5 2) (sourceB1303 + difference 2 5) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4202) := by
    have ha : (tripleCharges (sourceA1303 + difference 5 2) (sourceB1303 + difference 2 5) sourceC1303) = raw20945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20945; decide +kernel
    rw [ha]
    exact (canonical20945 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1303 + difference 5 3) (sourceB1303 + difference 3 5) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4225) := by
    have ha : (tripleCharges (sourceA1303 + difference 5 3) (sourceB1303 + difference 3 5) sourceC1303) = raw20946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20946; decide +kernel
    rw [ha]
    exact (canonical20946 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1303 + difference 5 4) (sourceB1303 + difference 4 5) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4257) := by
    have ha : (tripleCharges (sourceA1303 + difference 5 4) (sourceB1303 + difference 4 5) sourceC1303) = raw4621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw4621; decide +kernel
    rw [ha]
    exact (canonical4621 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1303 sourceB1303 sourceC1303
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1303, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1304 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1304 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1304 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm1304 : Integer.Sparse Master := [(Sum.inr 568, 2), (Sum.inr 570, 1), (Sum.inr 575, 1), (Sum.inr 602, 1), (Sum.inr 705, 2), (Sum.inr 726, 1), (Sum.inr 791, 1), (Sum.inr 1098, 2), (Sum.inr 1103, 1), (Sum.inr 1105, 2), (Sum.inr 1109, 2), (Sum.inr 1128, 2), (Sum.inr 1202, 2), (Sum.inr 1236, 2), (Sum.inr 1239, 1), (Sum.inr 1246, 1), (Sum.inr 1300, 1), (Sum.inr 2025, 2), (Sum.inr 2062, 1), (Sum.inr 2247, 1), (Sum.inr 3101, 1)]

theorem sourceEq1304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1304 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1304 + difference 0 1) (sourceB1304 + difference 1 0) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1304 + difference 0 1) (sourceB1304 + difference 1 0) sourceC1304) = raw4640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw4640; decide +kernel
    rw [ha]
    exact (canonical4640 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1304 + difference 0 2) (sourceB1304 + difference 2 0) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1304 + difference 0 2) (sourceB1304 + difference 2 0) sourceC1304) = raw4641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw4641; decide +kernel
    rw [ha]
    exact (canonical4641 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1304 + difference 0 3) (sourceB1304 + difference 3 0) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA1304 + difference 0 3) (sourceB1304 + difference 3 0) sourceC1304) = raw4642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw4642; decide +kernel
    rw [ha]
    exact (canonical4642 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1304 + difference 0 4) (sourceB1304 + difference 4 0) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA1304 + difference 0 4) (sourceB1304 + difference 4 0) sourceC1304) = raw2716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw2716; decide +kernel
    rw [ha]
    exact (canonical2716 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1304 + difference 0 5) (sourceB1304 + difference 5 0) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA1304 + difference 0 5) (sourceB1304 + difference 5 0) sourceC1304) = raw2711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw2711; decide +kernel
    rw [ha]
    exact (canonical2711 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1304 + difference 1 0) (sourceB1304 + difference 0 1) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 568) := by
    have ha : (tripleCharges (sourceA1304 + difference 1 0) (sourceB1304 + difference 0 1) sourceC1304) = raw20947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20947; decide +kernel
    rw [ha]
    exact (canonical20947 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1304 + difference 1 2) (sourceB1304 + difference 2 1) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1105) := by
    have ha : (tripleCharges (sourceA1304 + difference 1 2) (sourceB1304 + difference 2 1) sourceC1304) = raw20948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20948; decide +kernel
    rw [ha]
    exact (canonical20948 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1304 + difference 1 3) (sourceB1304 + difference 3 1) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1098) := by
    have ha : (tripleCharges (sourceA1304 + difference 1 3) (sourceB1304 + difference 3 1) sourceC1304) = raw20949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20949; decide +kernel
    rw [ha]
    exact (canonical20949 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1304 + difference 1 4) (sourceB1304 + difference 4 1) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA1304 + difference 1 4) (sourceB1304 + difference 4 1) sourceC1304) = raw4627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw4627; decide +kernel
    rw [ha]
    exact (canonical4627 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1304 + difference 1 5) (sourceB1304 + difference 5 1) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1304 + difference 1 5) (sourceB1304 + difference 5 1) sourceC1304) = raw7985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw7985; decide +kernel
    rw [ha]
    exact (canonical7985 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1304 + difference 2 0) (sourceB1304 + difference 0 2) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 568) := by
    have ha : (tripleCharges (sourceA1304 + difference 2 0) (sourceB1304 + difference 0 2) sourceC1304) = raw20950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20950; decide +kernel
    rw [ha]
    exact (canonical20950 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1304 + difference 2 1) (sourceB1304 + difference 1 2) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1105) := by
    have ha : (tripleCharges (sourceA1304 + difference 2 1) (sourceB1304 + difference 1 2) sourceC1304) = raw20951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20951; decide +kernel
    rw [ha]
    exact (canonical20951 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1304 + difference 2 3) (sourceB1304 + difference 3 2) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1098) := by
    have ha : (tripleCharges (sourceA1304 + difference 2 3) (sourceB1304 + difference 3 2) sourceC1304) = raw20952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20952; decide +kernel
    rw [ha]
    exact (canonical20952 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1304 + difference 2 4) (sourceB1304 + difference 4 2) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA1304 + difference 2 4) (sourceB1304 + difference 4 2) sourceC1304) = raw4631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw4631; decide +kernel
    rw [ha]
    exact (canonical4631 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1304 + difference 2 5) (sourceB1304 + difference 5 2) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1304 + difference 2 5) (sourceB1304 + difference 5 2) sourceC1304) = raw7989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw7989; decide +kernel
    rw [ha]
    exact (canonical7989 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1304 + difference 3 0) (sourceB1304 + difference 0 3) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 602) := by
    have ha : (tripleCharges (sourceA1304 + difference 3 0) (sourceB1304 + difference 0 3) sourceC1304) = raw20953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20953; decide +kernel
    rw [ha]
    exact (canonical20953 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1304 + difference 3 1) (sourceB1304 + difference 1 3) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1128) := by
    have ha : (tripleCharges (sourceA1304 + difference 3 1) (sourceB1304 + difference 1 3) sourceC1304) = raw20954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20954; decide +kernel
    rw [ha]
    exact (canonical20954 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1304 + difference 3 2) (sourceB1304 + difference 2 3) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1128) := by
    have ha : (tripleCharges (sourceA1304 + difference 3 2) (sourceB1304 + difference 2 3) sourceC1304) = raw20955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20955; decide +kernel
    rw [ha]
    exact (canonical20955 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1304 + difference 3 4) (sourceB1304 + difference 4 3) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1304 + difference 3 4) (sourceB1304 + difference 4 3) sourceC1304) = raw4635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw4635; decide +kernel
    rw [ha]
    exact (canonical4635 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1304 + difference 3 5) (sourceB1304 + difference 5 3) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1300) := by
    have ha : (tripleCharges (sourceA1304 + difference 3 5) (sourceB1304 + difference 5 3) sourceC1304) = raw7993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw7993; decide +kernel
    rw [ha]
    exact (canonical7993 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1304 + difference 4 0) (sourceB1304 + difference 0 4) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 575) := by
    have ha : (tripleCharges (sourceA1304 + difference 4 0) (sourceB1304 + difference 0 4) sourceC1304) = raw20956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20956; decide +kernel
    rw [ha]
    exact (canonical20956 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1304 + difference 4 1) (sourceB1304 + difference 1 4) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1109) := by
    have ha : (tripleCharges (sourceA1304 + difference 4 1) (sourceB1304 + difference 1 4) sourceC1304) = raw20957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20957; decide +kernel
    rw [ha]
    exact (canonical20957 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1304 + difference 4 2) (sourceB1304 + difference 2 4) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1109) := by
    have ha : (tripleCharges (sourceA1304 + difference 4 2) (sourceB1304 + difference 2 4) sourceC1304) = raw20958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20958; decide +kernel
    rw [ha]
    exact (canonical20958 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1304 + difference 4 3) (sourceB1304 + difference 3 4) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1103) := by
    have ha : (tripleCharges (sourceA1304 + difference 4 3) (sourceB1304 + difference 3 4) sourceC1304) = raw20959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20959; decide +kernel
    rw [ha]
    exact (canonical20959 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1304 + difference 4 5) (sourceB1304 + difference 5 4) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1304 + difference 4 5) (sourceB1304 + difference 5 4) sourceC1304) = raw7997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw7997; decide +kernel
    rw [ha]
    exact (canonical7997 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1304 + difference 5 0) (sourceB1304 + difference 0 5) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 570) := by
    have ha : (tripleCharges (sourceA1304 + difference 5 0) (sourceB1304 + difference 0 5) sourceC1304) = raw20960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20960; decide +kernel
    rw [ha]
    exact (canonical20960 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1304 + difference 5 1) (sourceB1304 + difference 1 5) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 705) := by
    have ha : (tripleCharges (sourceA1304 + difference 5 1) (sourceB1304 + difference 1 5) sourceC1304) = raw20961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20961; decide +kernel
    rw [ha]
    exact (canonical20961 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1304 + difference 5 2) (sourceB1304 + difference 2 5) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 705) := by
    have ha : (tripleCharges (sourceA1304 + difference 5 2) (sourceB1304 + difference 2 5) sourceC1304) = raw20962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20962; decide +kernel
    rw [ha]
    exact (canonical20962 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1304 + difference 5 3) (sourceB1304 + difference 3 5) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 726) := by
    have ha : (tripleCharges (sourceA1304 + difference 5 3) (sourceB1304 + difference 3 5) sourceC1304) = raw20963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw20963; decide +kernel
    rw [ha]
    exact (canonical20963 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1304 + difference 5 4) (sourceB1304 + difference 4 5) sourceC1304) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 791) := by
    have ha : (tripleCharges (sourceA1304 + difference 5 4) (sourceB1304 + difference 4 5) sourceC1304) = raw4643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1304 sourceB1304 sourceC1304 difference raw4643; decide +kernel
    rw [ha]
    exact (canonical4643 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1304 sourceB1304 sourceC1304
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1304, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1305 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1305 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1305 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1305 : Integer.Sparse Master := [(Sum.inr 4398, 2), (Sum.inr 4416, 2), (Sum.inr 4421, 1), (Sum.inr 4426, 1), (Sum.inr 4430, 1), (Sum.inr 4442, 2), (Sum.inr 4463, 1), (Sum.inr 4464, 1), (Sum.inr 4478, 1), (Sum.inr 4488, 1), (Sum.inr 4501, 1), (Sum.inr 4562, 2), (Sum.inr 4572, 1), (Sum.inr 4576, 2), (Sum.inr 4583, 2), (Sum.inr 4588, 2), (Sum.inr 4591, 2), (Sum.inr 4605, 2), (Sum.inr 4608, 1), (Sum.inr 4621, 1), (Sum.inr 4625, 1)]

theorem sourceEq1305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1305 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1305 + difference 0 1) (sourceB1305 + difference 1 0) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA1305 + difference 0 1) (sourceB1305 + difference 1 0) sourceC1305) = raw20964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20964; decide +kernel
    rw [ha]
    exact (canonical20964 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1305 + difference 0 2) (sourceB1305 + difference 2 0) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA1305 + difference 0 2) (sourceB1305 + difference 2 0) sourceC1305) = raw20965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20965; decide +kernel
    rw [ha]
    exact (canonical20965 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1305 + difference 0 3) (sourceB1305 + difference 3 0) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4478) := by
    have ha : (tripleCharges (sourceA1305 + difference 0 3) (sourceB1305 + difference 3 0) sourceC1305) = raw20966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20966; decide +kernel
    rw [ha]
    exact (canonical20966 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1305 + difference 0 4) (sourceB1305 + difference 4 0) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA1305 + difference 0 4) (sourceB1305 + difference 4 0) sourceC1305) = raw20570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20570; decide +kernel
    rw [ha]
    exact (canonical20570 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1305 + difference 0 5) (sourceB1305 + difference 5 0) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1305 + difference 0 5) (sourceB1305 + difference 5 0) sourceC1305) = raw20416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20416; decide +kernel
    rw [ha]
    exact (canonical20416 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1305 + difference 1 0) (sourceB1305 + difference 0 1) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1305 + difference 1 0) (sourceB1305 + difference 0 1) sourceC1305) = raw20967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20967; decide +kernel
    rw [ha]
    exact (canonical20967 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1305 + difference 1 2) (sourceB1305 + difference 2 1) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4576) := by
    have ha : (tripleCharges (sourceA1305 + difference 1 2) (sourceB1305 + difference 2 1) sourceC1305) = raw20968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20968; decide +kernel
    rw [ha]
    exact (canonical20968 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1305 + difference 1 3) (sourceB1305 + difference 3 1) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4562) := by
    have ha : (tripleCharges (sourceA1305 + difference 1 3) (sourceB1305 + difference 3 1) sourceC1305) = raw20969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20969; decide +kernel
    rw [ha]
    exact (canonical20969 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1305 + difference 1 4) (sourceB1305 + difference 4 1) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4588) := by
    have ha : (tripleCharges (sourceA1305 + difference 1 4) (sourceB1305 + difference 4 1) sourceC1305) = raw20574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20574; decide +kernel
    rw [ha]
    exact (canonical20574 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1305 + difference 1 5) (sourceB1305 + difference 5 1) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1305 + difference 1 5) (sourceB1305 + difference 5 1) sourceC1305) = raw20421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20421; decide +kernel
    rw [ha]
    exact (canonical20421 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1305 + difference 2 0) (sourceB1305 + difference 0 2) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1305 + difference 2 0) (sourceB1305 + difference 0 2) sourceC1305) = raw20970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20970; decide +kernel
    rw [ha]
    exact (canonical20970 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1305 + difference 2 1) (sourceB1305 + difference 1 2) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4576) := by
    have ha : (tripleCharges (sourceA1305 + difference 2 1) (sourceB1305 + difference 1 2) sourceC1305) = raw20971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20971; decide +kernel
    rw [ha]
    exact (canonical20971 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1305 + difference 2 3) (sourceB1305 + difference 3 2) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4562) := by
    have ha : (tripleCharges (sourceA1305 + difference 2 3) (sourceB1305 + difference 3 2) sourceC1305) = raw20972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20972; decide +kernel
    rw [ha]
    exact (canonical20972 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1305 + difference 2 4) (sourceB1305 + difference 4 2) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4588) := by
    have ha : (tripleCharges (sourceA1305 + difference 2 4) (sourceB1305 + difference 4 2) sourceC1305) = raw20578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20578; decide +kernel
    rw [ha]
    exact (canonical20578 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1305 + difference 2 5) (sourceB1305 + difference 5 2) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1305 + difference 2 5) (sourceB1305 + difference 5 2) sourceC1305) = raw20426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20426; decide +kernel
    rw [ha]
    exact (canonical20426 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1305 + difference 3 0) (sourceB1305 + difference 0 3) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1305 + difference 3 0) (sourceB1305 + difference 0 3) sourceC1305) = raw20439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20439; decide +kernel
    rw [ha]
    exact (canonical20439 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1305 + difference 3 1) (sourceB1305 + difference 1 3) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1305 + difference 3 1) (sourceB1305 + difference 1 3) sourceC1305) = raw20440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20440; decide +kernel
    rw [ha]
    exact (canonical20440 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1305 + difference 3 2) (sourceB1305 + difference 2 3) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1305 + difference 3 2) (sourceB1305 + difference 2 3) sourceC1305) = raw20441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20441; decide +kernel
    rw [ha]
    exact (canonical20441 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1305 + difference 3 4) (sourceB1305 + difference 4 3) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA1305 + difference 3 4) (sourceB1305 + difference 4 3) sourceC1305) = raw20443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20443; decide +kernel
    rw [ha]
    exact (canonical20443 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1305 + difference 3 5) (sourceB1305 + difference 5 3) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1305 + difference 3 5) (sourceB1305 + difference 5 3) sourceC1305) = raw20584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20584; decide +kernel
    rw [ha]
    exact (canonical20584 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1305 + difference 4 0) (sourceB1305 + difference 0 4) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4426) := by
    have ha : (tripleCharges (sourceA1305 + difference 4 0) (sourceB1305 + difference 0 4) sourceC1305) = raw20808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20808; decide +kernel
    rw [ha]
    exact (canonical20808 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1305 + difference 4 1) (sourceB1305 + difference 1 4) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA1305 + difference 4 1) (sourceB1305 + difference 1 4) sourceC1305) = raw20809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20809; decide +kernel
    rw [ha]
    exact (canonical20809 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1305 + difference 4 2) (sourceB1305 + difference 2 4) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA1305 + difference 4 2) (sourceB1305 + difference 2 4) sourceC1305) = raw20810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20810; decide +kernel
    rw [ha]
    exact (canonical20810 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1305 + difference 4 3) (sourceB1305 + difference 3 4) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA1305 + difference 4 3) (sourceB1305 + difference 3 4) sourceC1305) = raw20811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20811; decide +kernel
    rw [ha]
    exact (canonical20811 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1305 + difference 4 5) (sourceB1305 + difference 5 4) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1305 + difference 4 5) (sourceB1305 + difference 5 4) sourceC1305) = raw20437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20437; decide +kernel
    rw [ha]
    exact (canonical20437 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1305 + difference 5 0) (sourceB1305 + difference 0 5) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4421) := by
    have ha : (tripleCharges (sourceA1305 + difference 5 0) (sourceB1305 + difference 0 5) sourceC1305) = raw20973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20973; decide +kernel
    rw [ha]
    exact (canonical20973 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1305 + difference 5 1) (sourceB1305 + difference 1 5) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4416) := by
    have ha : (tripleCharges (sourceA1305 + difference 5 1) (sourceB1305 + difference 1 5) sourceC1305) = raw20974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20974; decide +kernel
    rw [ha]
    exact (canonical20974 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1305 + difference 5 2) (sourceB1305 + difference 2 5) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4416) := by
    have ha : (tripleCharges (sourceA1305 + difference 5 2) (sourceB1305 + difference 2 5) sourceC1305) = raw20975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20975; decide +kernel
    rw [ha]
    exact (canonical20975 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1305 + difference 5 3) (sourceB1305 + difference 3 5) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4430) := by
    have ha : (tripleCharges (sourceA1305 + difference 5 3) (sourceB1305 + difference 3 5) sourceC1305) = raw20976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20976; decide +kernel
    rw [ha]
    exact (canonical20976 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1305 + difference 5 4) (sourceB1305 + difference 4 5) sourceC1305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4488) := by
    have ha : (tripleCharges (sourceA1305 + difference 5 4) (sourceB1305 + difference 4 5) sourceC1305) = raw20588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1305 sourceB1305 sourceC1305 difference raw20588; decide +kernel
    rw [ha]
    exact (canonical20588 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1305 sourceB1305 sourceC1305
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1305, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1306 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1306 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1306 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1306 : Integer.Sparse Master := [(Sum.inr 1024, 2), (Sum.inr 1046, 1), (Sum.inr 1047, 1), (Sum.inr 1061, 1), (Sum.inr 1207, 2), (Sum.inr 1217, 2), (Sum.inr 1218, 2), (Sum.inr 1225, 2), (Sum.inr 1251, 2), (Sum.inr 1252, 2), (Sum.inr 1269, 1), (Sum.inr 1271, 2), (Sum.inr 1272, 1), (Sum.inr 1281, 1), (Sum.inr 1282, 1), (Sum.inr 1307, 1), (Sum.inr 1308, 1), (Sum.inr 1399, 2), (Sum.inr 1428, 1), (Sum.inr 1429, 1), (Sum.inr 1452, 1)]

theorem sourceEq1306 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1306 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1306 + difference 0 1) (sourceB1306 + difference 1 0) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA1306 + difference 0 1) (sourceB1306 + difference 1 0) sourceC1306) = raw20977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20977; decide +kernel
    rw [ha]
    exact (canonical20977 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1306 + difference 0 2) (sourceB1306 + difference 2 0) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA1306 + difference 0 2) (sourceB1306 + difference 2 0) sourceC1306) = raw20978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20978; decide +kernel
    rw [ha]
    exact (canonical20978 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1306 + difference 0 3) (sourceB1306 + difference 3 0) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1061) := by
    have ha : (tripleCharges (sourceA1306 + difference 0 3) (sourceB1306 + difference 3 0) sourceC1306) = raw20979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20979; decide +kernel
    rw [ha]
    exact (canonical20979 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1306 + difference 0 4) (sourceB1306 + difference 4 0) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA1306 + difference 0 4) (sourceB1306 + difference 4 0) sourceC1306) = raw20622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20622; decide +kernel
    rw [ha]
    exact (canonical20622 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1306 + difference 0 5) (sourceB1306 + difference 5 0) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1306 + difference 0 5) (sourceB1306 + difference 5 0) sourceC1306) = raw20446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20446; decide +kernel
    rw [ha]
    exact (canonical20446 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1306 + difference 1 0) (sourceB1306 + difference 0 1) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1399) := by
    have ha : (tripleCharges (sourceA1306 + difference 1 0) (sourceB1306 + difference 0 1) sourceC1306) = raw20980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20980; decide +kernel
    rw [ha]
    exact (canonical20980 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1306 + difference 1 2) (sourceB1306 + difference 2 1) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1207) := by
    have ha : (tripleCharges (sourceA1306 + difference 1 2) (sourceB1306 + difference 2 1) sourceC1306) = raw20981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20981; decide +kernel
    rw [ha]
    exact (canonical20981 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1306 + difference 1 3) (sourceB1306 + difference 3 1) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1225) := by
    have ha : (tripleCharges (sourceA1306 + difference 1 3) (sourceB1306 + difference 3 1) sourceC1306) = raw20982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20982; decide +kernel
    rw [ha]
    exact (canonical20982 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1306 + difference 1 4) (sourceB1306 + difference 4 1) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA1306 + difference 1 4) (sourceB1306 + difference 4 1) sourceC1306) = raw20626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20626; decide +kernel
    rw [ha]
    exact (canonical20626 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1306 + difference 1 5) (sourceB1306 + difference 5 1) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1306 + difference 1 5) (sourceB1306 + difference 5 1) sourceC1306) = raw20451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20451; decide +kernel
    rw [ha]
    exact (canonical20451 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1306 + difference 2 0) (sourceB1306 + difference 0 2) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1399) := by
    have ha : (tripleCharges (sourceA1306 + difference 2 0) (sourceB1306 + difference 0 2) sourceC1306) = raw20983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20983; decide +kernel
    rw [ha]
    exact (canonical20983 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1306 + difference 2 1) (sourceB1306 + difference 1 2) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1207) := by
    have ha : (tripleCharges (sourceA1306 + difference 2 1) (sourceB1306 + difference 1 2) sourceC1306) = raw20984 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20984; decide +kernel
    rw [ha]
    exact (canonical20984 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1306 + difference 2 3) (sourceB1306 + difference 3 2) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1225) := by
    have ha : (tripleCharges (sourceA1306 + difference 2 3) (sourceB1306 + difference 3 2) sourceC1306) = raw20985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20985; decide +kernel
    rw [ha]
    exact (canonical20985 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1306 + difference 2 4) (sourceB1306 + difference 4 2) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA1306 + difference 2 4) (sourceB1306 + difference 4 2) sourceC1306) = raw20630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20630; decide +kernel
    rw [ha]
    exact (canonical20630 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1306 + difference 2 5) (sourceB1306 + difference 5 2) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1306 + difference 2 5) (sourceB1306 + difference 5 2) sourceC1306) = raw20456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20456; decide +kernel
    rw [ha]
    exact (canonical20456 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1306 + difference 3 0) (sourceB1306 + difference 0 3) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1452) := by
    have ha : (tripleCharges (sourceA1306 + difference 3 0) (sourceB1306 + difference 0 3) sourceC1306) = raw20469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20469; decide +kernel
    rw [ha]
    exact (canonical20469 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1306 + difference 3 1) (sourceB1306 + difference 1 3) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1306 + difference 3 1) (sourceB1306 + difference 1 3) sourceC1306) = raw20470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20470; decide +kernel
    rw [ha]
    exact (canonical20470 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1306 + difference 3 2) (sourceB1306 + difference 2 3) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1306 + difference 3 2) (sourceB1306 + difference 2 3) sourceC1306) = raw20471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20471; decide +kernel
    rw [ha]
    exact (canonical20471 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1306 + difference 3 4) (sourceB1306 + difference 4 3) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1308) := by
    have ha : (tripleCharges (sourceA1306 + difference 3 4) (sourceB1306 + difference 4 3) sourceC1306) = raw20473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20473; decide +kernel
    rw [ha]
    exact (canonical20473 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1306 + difference 3 5) (sourceB1306 + difference 5 3) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1306 + difference 3 5) (sourceB1306 + difference 5 3) sourceC1306) = raw20636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20636; decide +kernel
    rw [ha]
    exact (canonical20636 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1306 + difference 4 0) (sourceB1306 + difference 0 4) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1428) := by
    have ha : (tripleCharges (sourceA1306 + difference 4 0) (sourceB1306 + difference 0 4) sourceC1306) = raw20986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20986; decide +kernel
    rw [ha]
    exact (canonical20986 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1306 + difference 4 1) (sourceB1306 + difference 1 4) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1251) := by
    have ha : (tripleCharges (sourceA1306 + difference 4 1) (sourceB1306 + difference 1 4) sourceC1306) = raw20987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20987; decide +kernel
    rw [ha]
    exact (canonical20987 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1306 + difference 4 2) (sourceB1306 + difference 2 4) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1251) := by
    have ha : (tripleCharges (sourceA1306 + difference 4 2) (sourceB1306 + difference 2 4) sourceC1306) = raw20988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20988; decide +kernel
    rw [ha]
    exact (canonical20988 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1306 + difference 4 3) (sourceB1306 + difference 3 4) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1281) := by
    have ha : (tripleCharges (sourceA1306 + difference 4 3) (sourceB1306 + difference 3 4) sourceC1306) = raw20989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20989; decide +kernel
    rw [ha]
    exact (canonical20989 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1306 + difference 4 5) (sourceB1306 + difference 5 4) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1269) := by
    have ha : (tripleCharges (sourceA1306 + difference 4 5) (sourceB1306 + difference 5 4) sourceC1306) = raw20467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20467; decide +kernel
    rw [ha]
    exact (canonical20467 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1306 + difference 5 0) (sourceB1306 + difference 0 5) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1429) := by
    have ha : (tripleCharges (sourceA1306 + difference 5 0) (sourceB1306 + difference 0 5) sourceC1306) = raw20990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20990; decide +kernel
    rw [ha]
    exact (canonical20990 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1306 + difference 5 1) (sourceB1306 + difference 1 5) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1252) := by
    have ha : (tripleCharges (sourceA1306 + difference 5 1) (sourceB1306 + difference 1 5) sourceC1306) = raw20991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20991; decide +kernel
    rw [ha]
    exact (canonical20991 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1306 + difference 5 2) (sourceB1306 + difference 2 5) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1252) := by
    have ha : (tripleCharges (sourceA1306 + difference 5 2) (sourceB1306 + difference 2 5) sourceC1306) = raw20992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20992; decide +kernel
    rw [ha]
    exact (canonical20992 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1306 + difference 5 3) (sourceB1306 + difference 3 5) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1282) := by
    have ha : (tripleCharges (sourceA1306 + difference 5 3) (sourceB1306 + difference 3 5) sourceC1306) = raw20993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20993; decide +kernel
    rw [ha]
    exact (canonical20993 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1306 + difference 5 4) (sourceB1306 + difference 4 5) sourceC1306) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1272) := by
    have ha : (tripleCharges (sourceA1306 + difference 5 4) (sourceB1306 + difference 4 5) sourceC1306) = raw20640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1306 sourceB1306 sourceC1306 difference raw20640; decide +kernel
    rw [ha]
    exact (canonical20640 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1306 sourceB1306 sourceC1306
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1306, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1307 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1307 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1307 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1307 : Integer.Sparse Master := [(Sum.inr 1002, 1), (Sum.inr 1599, 2), (Sum.inr 1625, 1), (Sum.inr 1730, 1), (Sum.inr 2226, 1), (Sum.inr 4070, -1)]

theorem sourceEq1307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1307 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1307 + difference 0 0) (sourceB1307 + difference 0 0) sourceC1307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1307 + difference 0 0) (sourceB1307 + difference 0 0) sourceC1307) = raw20994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1307 sourceB1307 sourceC1307 difference raw20994; decide +kernel
    rw [ha]
    exact (canonical20994 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1307 + difference 1 0) (sourceB1307 + difference 0 1) sourceC1307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1599) := by
    have ha : (tripleCharges (sourceA1307 + difference 1 0) (sourceB1307 + difference 0 1) sourceC1307) = raw20995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1307 sourceB1307 sourceC1307 difference raw20995; decide +kernel
    rw [ha]
    exact (canonical20995 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1307 + difference 2 0) (sourceB1307 + difference 0 2) sourceC1307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1599) := by
    have ha : (tripleCharges (sourceA1307 + difference 2 0) (sourceB1307 + difference 0 2) sourceC1307) = raw20996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1307 sourceB1307 sourceC1307 difference raw20996; decide +kernel
    rw [ha]
    exact (canonical20996 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1307 + difference 3 0) (sourceB1307 + difference 0 3) sourceC1307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1307 + difference 3 0) (sourceB1307 + difference 0 3) sourceC1307) = raw20480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1307 sourceB1307 sourceC1307 difference raw20480; decide +kernel
    rw [ha]
    exact (canonical20480 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1307 + difference 4 0) (sourceB1307 + difference 0 4) sourceC1307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1625) := by
    have ha : (tripleCharges (sourceA1307 + difference 4 0) (sourceB1307 + difference 0 4) sourceC1307) = raw20843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1307 sourceB1307 sourceC1307 difference raw20843; decide +kernel
    rw [ha]
    exact (canonical20843 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1307 + difference 5 0) (sourceB1307 + difference 0 5) sourceC1307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1002) := by
    have ha : (tripleCharges (sourceA1307 + difference 5 0) (sourceB1307 + difference 0 5) sourceC1307) = raw20997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1307 sourceB1307 sourceC1307 difference raw20997; decide +kernel
    rw [ha]
    exact (canonical20997 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1307 + sourceB1307) sourceC1307) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1307 + sourceB1307) sourceC1307) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1307 sourceB1307 sourceC1307 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1307 sourceB1307 sourceC1307
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1307, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1308 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1308 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC1308 : Charge := ![2, 0, 0, 1, 1, -4]
def sourceForm1308 : Integer.Sparse Master := [(Sum.inr 1231, 1), (Sum.inr 1637, 2), (Sum.inr 1650, 1), (Sum.inr 1710, 1), (Sum.inr 2737, 1), (Sum.inr 4069, -1)]

theorem sourceEq1308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1308 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1308 + difference 0 0) (sourceB1308 + difference 0 0) sourceC1308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1231) := by
    have ha : (tripleCharges (sourceA1308 + difference 0 0) (sourceB1308 + difference 0 0) sourceC1308) = raw19864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1308 sourceB1308 sourceC1308 difference raw19864; decide +kernel
    rw [ha]
    exact (canonical19864 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1308 + difference 0 1) (sourceB1308 + difference 1 0) sourceC1308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1637) := by
    have ha : (tripleCharges (sourceA1308 + difference 0 1) (sourceB1308 + difference 1 0) sourceC1308) = raw20998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1308 sourceB1308 sourceC1308 difference raw20998; decide +kernel
    rw [ha]
    exact (canonical20998 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1308 + difference 0 2) (sourceB1308 + difference 2 0) sourceC1308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1637) := by
    have ha : (tripleCharges (sourceA1308 + difference 0 2) (sourceB1308 + difference 2 0) sourceC1308) = raw20999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1308 sourceB1308 sourceC1308 difference raw20999; decide +kernel
    rw [ha]
    exact (canonical20999 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1308 + difference 0 3) (sourceB1308 + difference 3 0) sourceC1308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1650) := by
    have ha : (tripleCharges (sourceA1308 + difference 0 3) (sourceB1308 + difference 3 0) sourceC1308) = raw21000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1308 sourceB1308 sourceC1308 difference raw21000; decide +kernel
    rw [ha]
    exact (canonical21000 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1308 + difference 0 4) (sourceB1308 + difference 4 0) sourceC1308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1308 + difference 0 4) (sourceB1308 + difference 4 0) sourceC1308) = raw19855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1308 sourceB1308 sourceC1308 difference raw19855; decide +kernel
    rw [ha]
    exact (canonical19855 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1308 + difference 0 5) (sourceB1308 + difference 5 0) sourceC1308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1308 + difference 0 5) (sourceB1308 + difference 5 0) sourceC1308) = raw21001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1308 sourceB1308 sourceC1308 difference raw21001; decide +kernel
    rw [ha]
    exact (canonical21001 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1308 + sourceB1308) sourceC1308) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1308 + sourceB1308) sourceC1308) = raw19856 := by
      apply Matrix.ext; unfold doubleCharges sourceA1308 sourceB1308 sourceC1308 raw19856; decide +kernel
    rw [ha]
    exact (canonical19856 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1308 sourceB1308 sourceC1308
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1308, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1309 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1309 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC1309 : Charge := ![2, 0, 0, 2, -2, -2]
def sourceForm1309 : Integer.Sparse Master := [(Sum.inr 1191, 1), (Sum.inr 2391, 2), (Sum.inr 2407, 1), (Sum.inr 2680, 1), (Sum.inr 2686, 1), (Sum.inr 4089, -1)]

theorem sourceEq1309 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1309 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1309 + difference 0 0) (sourceB1309 + difference 0 0) sourceC1309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1191) := by
    have ha : (tripleCharges (sourceA1309 + difference 0 0) (sourceB1309 + difference 0 0) sourceC1309) = raw21002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1309 sourceB1309 sourceC1309 difference raw21002; decide +kernel
    rw [ha]
    exact (canonical21002 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1309 + difference 0 1) (sourceB1309 + difference 1 0) sourceC1309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2391) := by
    have ha : (tripleCharges (sourceA1309 + difference 0 1) (sourceB1309 + difference 1 0) sourceC1309) = raw21003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1309 sourceB1309 sourceC1309 difference raw21003; decide +kernel
    rw [ha]
    exact (canonical21003 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1309 + difference 0 2) (sourceB1309 + difference 2 0) sourceC1309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2391) := by
    have ha : (tripleCharges (sourceA1309 + difference 0 2) (sourceB1309 + difference 2 0) sourceC1309) = raw21004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1309 sourceB1309 sourceC1309 difference raw21004; decide +kernel
    rw [ha]
    exact (canonical21004 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1309 + difference 0 3) (sourceB1309 + difference 3 0) sourceC1309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2407) := by
    have ha : (tripleCharges (sourceA1309 + difference 0 3) (sourceB1309 + difference 3 0) sourceC1309) = raw21005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1309 sourceB1309 sourceC1309 difference raw21005; decide +kernel
    rw [ha]
    exact (canonical21005 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1309 + difference 0 4) (sourceB1309 + difference 4 0) sourceC1309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2680) := by
    have ha : (tripleCharges (sourceA1309 + difference 0 4) (sourceB1309 + difference 4 0) sourceC1309) = raw21006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1309 sourceB1309 sourceC1309 difference raw21006; decide +kernel
    rw [ha]
    exact (canonical21006 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1309 + difference 0 5) (sourceB1309 + difference 5 0) sourceC1309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA1309 + difference 0 5) (sourceB1309 + difference 5 0) sourceC1309) = raw21007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1309 sourceB1309 sourceC1309 difference raw21007; decide +kernel
    rw [ha]
    exact (canonical21007 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1309 + sourceB1309) sourceC1309) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA1309 + sourceB1309) sourceC1309) = raw21008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1309 sourceB1309 sourceC1309 raw21008; decide +kernel
    rw [ha]
    exact (canonical21008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1309 sourceB1309 sourceC1309
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1309, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1310 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1310 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC1310 : Charge := ![2, 0, 0, 2, -2, -2]
def sourceForm1310 : Integer.Sparse Master := [(Sum.inr 1185, 2), (Sum.inr 1191, 1), (Sum.inr 1193, 1), (Sum.inr 1288, 1), (Sum.inr 2686, 1), (Sum.inr 4089, -1)]

theorem sourceEq1310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1310 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1310 + difference 0 5) (sourceB1310 + difference 5 0) sourceC1310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA1310 + difference 0 5) (sourceB1310 + difference 5 0) sourceC1310) = raw21007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1310 sourceB1310 sourceC1310 difference raw21007; decide +kernel
    rw [ha]
    exact (canonical21007 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1310 + difference 1 5) (sourceB1310 + difference 5 1) sourceC1310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1185) := by
    have ha : (tripleCharges (sourceA1310 + difference 1 5) (sourceB1310 + difference 5 1) sourceC1310) = raw21009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1310 sourceB1310 sourceC1310 difference raw21009; decide +kernel
    rw [ha]
    exact (canonical21009 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1310 + difference 2 5) (sourceB1310 + difference 5 2) sourceC1310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1185) := by
    have ha : (tripleCharges (sourceA1310 + difference 2 5) (sourceB1310 + difference 5 2) sourceC1310) = raw21010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1310 sourceB1310 sourceC1310 difference raw21010; decide +kernel
    rw [ha]
    exact (canonical21010 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1310 + difference 3 5) (sourceB1310 + difference 5 3) sourceC1310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1288) := by
    have ha : (tripleCharges (sourceA1310 + difference 3 5) (sourceB1310 + difference 5 3) sourceC1310) = raw21011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1310 sourceB1310 sourceC1310 difference raw21011; decide +kernel
    rw [ha]
    exact (canonical21011 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1310 + difference 4 5) (sourceB1310 + difference 5 4) sourceC1310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1193) := by
    have ha : (tripleCharges (sourceA1310 + difference 4 5) (sourceB1310 + difference 5 4) sourceC1310) = raw21012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1310 sourceB1310 sourceC1310 difference raw21012; decide +kernel
    rw [ha]
    exact (canonical21012 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1310 + difference 5 5) (sourceB1310 + difference 5 5) sourceC1310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1191) := by
    have ha : (tripleCharges (sourceA1310 + difference 5 5) (sourceB1310 + difference 5 5) sourceC1310) = raw21002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1310 sourceB1310 sourceC1310 difference raw21002; decide +kernel
    rw [ha]
    exact (canonical21002 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1310 + sourceB1310) sourceC1310) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA1310 + sourceB1310) sourceC1310) = raw21008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1310 sourceB1310 sourceC1310 raw21008; decide +kernel
    rw [ha]
    exact (canonical21008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1310 sourceB1310 sourceC1310
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1310, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1311 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1311 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1311 : Charge := ![2, 0, 0, 2, -1, -3]
def sourceForm1311 : Integer.Sparse Master := [(Sum.inr 1190, 1), (Sum.inr 1924, 2), (Sum.inr 1950, 1), (Sum.inr 2218, 1), (Sum.inr 2685, 1), (Sum.inr 4082, -1)]

theorem sourceEq1311 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1311 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1311 + difference 0 0) (sourceB1311 + difference 0 0) sourceC1311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA1311 + difference 0 0) (sourceB1311 + difference 0 0) sourceC1311) = raw21013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1311 sourceB1311 sourceC1311 difference raw21013; decide +kernel
    rw [ha]
    exact (canonical21013 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1311 + difference 0 1) (sourceB1311 + difference 1 0) sourceC1311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA1311 + difference 0 1) (sourceB1311 + difference 1 0) sourceC1311) = raw21014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1311 sourceB1311 sourceC1311 difference raw21014; decide +kernel
    rw [ha]
    exact (canonical21014 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1311 + difference 0 2) (sourceB1311 + difference 2 0) sourceC1311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA1311 + difference 0 2) (sourceB1311 + difference 2 0) sourceC1311) = raw21015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1311 sourceB1311 sourceC1311 difference raw21015; decide +kernel
    rw [ha]
    exact (canonical21015 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1311 + difference 0 3) (sourceB1311 + difference 3 0) sourceC1311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1950) := by
    have ha : (tripleCharges (sourceA1311 + difference 0 3) (sourceB1311 + difference 3 0) sourceC1311) = raw21016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1311 sourceB1311 sourceC1311 difference raw21016; decide +kernel
    rw [ha]
    exact (canonical21016 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1311 + difference 0 4) (sourceB1311 + difference 4 0) sourceC1311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1311 + difference 0 4) (sourceB1311 + difference 4 0) sourceC1311) = raw21017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1311 sourceB1311 sourceC1311 difference raw21017; decide +kernel
    rw [ha]
    exact (canonical21017 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1311 + difference 0 5) (sourceB1311 + difference 5 0) sourceC1311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA1311 + difference 0 5) (sourceB1311 + difference 5 0) sourceC1311) = raw21018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1311 sourceB1311 sourceC1311 difference raw21018; decide +kernel
    rw [ha]
    exact (canonical21018 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1311 + sourceB1311) sourceC1311) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1311 + sourceB1311) sourceC1311) = raw21019 := by
      apply Matrix.ext; unfold doubleCharges sourceA1311 sourceB1311 sourceC1311 raw21019; decide +kernel
    rw [ha]
    exact (canonical21019 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1311 sourceB1311 sourceC1311
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1311, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
