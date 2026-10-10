import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical39

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA128 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB128 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC128 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceForm128 : Integer.Sparse Master := [(Sum.inr 1059, 3), (Sum.inr 1064, 1), (Sum.inr 1091, 1), (Sum.inr 2281, 1), (Sum.inr 4084, -1)]

theorem sourceEq128 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm128 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA128 + difference 5 0) (sourceB128 + difference 0 5) sourceC128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1064) := by
    have ha : (tripleCharges (sourceA128 + difference 5 0) (sourceB128 + difference 0 5) sourceC128) = raw4532 := by
      apply Matrix.ext; unfold tripleCharges sourceA128 sourceB128 sourceC128 difference raw4532; decide +kernel
    rw [ha]
    exact (canonical4532 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA128 + difference 5 1) (sourceB128 + difference 1 5) sourceC128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA128 + difference 5 1) (sourceB128 + difference 1 5) sourceC128) = raw4540 := by
      apply Matrix.ext; unfold tripleCharges sourceA128 sourceB128 sourceC128 difference raw4540; decide +kernel
    rw [ha]
    exact (canonical4540 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA128 + difference 5 2) (sourceB128 + difference 2 5) sourceC128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA128 + difference 5 2) (sourceB128 + difference 2 5) sourceC128) = raw4547 := by
      apply Matrix.ext; unfold tripleCharges sourceA128 sourceB128 sourceC128 difference raw4547; decide +kernel
    rw [ha]
    exact (canonical4547 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA128 + difference 5 3) (sourceB128 + difference 3 5) sourceC128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA128 + difference 5 3) (sourceB128 + difference 3 5) sourceC128) = raw4548 := by
      apply Matrix.ext; unfold tripleCharges sourceA128 sourceB128 sourceC128 difference raw4548; decide +kernel
    rw [ha]
    exact (canonical4548 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA128 + difference 5 4) (sourceB128 + difference 4 5) sourceC128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA128 + difference 5 4) (sourceB128 + difference 4 5) sourceC128) = raw4546 := by
      apply Matrix.ext; unfold tripleCharges sourceA128 sourceB128 sourceC128 difference raw4546; decide +kernel
    rw [ha]
    exact (canonical4546 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA128 + difference 5 5) (sourceB128 + difference 5 5) sourceC128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA128 + difference 5 5) (sourceB128 + difference 5 5) sourceC128) = raw4521 := by
      apply Matrix.ext; unfold tripleCharges sourceA128 sourceB128 sourceC128 difference raw4521; decide +kernel
    rw [ha]
    exact (canonical4521 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA128 + sourceB128) sourceC128) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA128 + sourceB128) sourceC128) = raw4527 := by
      apply Matrix.ext; unfold doubleCharges sourceA128 sourceB128 sourceC128 raw4527; decide +kernel
    rw [ha]
    exact (canonical4527 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA128 sourceB128 sourceC128
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm128, Integer.Sparse.eval]
  linarith only [hs]

def sourceA129 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB129 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC129 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm129 : Integer.Sparse Master := [(Sum.inr 4500, 3), (Sum.inr 4508, 1), (Sum.inr 4510, 1), (Sum.inr 4836, 6), (Sum.inr 4844, 3), (Sum.inr 4845, 3), (Sum.inr 4890, 3), (Sum.inr 4892, 3), (Sum.inr 4897, 1), (Sum.inr 4899, 1), (Sum.inr 4900, 1), (Sum.inr 5268, 3), (Sum.inr 5296, 1)]

theorem sourceEq129 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm129 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA129 + difference 0 1) (sourceB129 + difference 1 0) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA129 + difference 0 1) (sourceB129 + difference 1 0) sourceC129) = raw4037 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4037; decide +kernel
    rw [ha]
    exact (canonical4037 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA129 + difference 0 2) (sourceB129 + difference 2 0) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA129 + difference 0 2) (sourceB129 + difference 2 0) sourceC129) = raw4549 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4549; decide +kernel
    rw [ha]
    exact (canonical4549 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA129 + difference 0 3) (sourceB129 + difference 3 0) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA129 + difference 0 3) (sourceB129 + difference 3 0) sourceC129) = raw4550 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4550; decide +kernel
    rw [ha]
    exact (canonical4550 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA129 + difference 0 4) (sourceB129 + difference 4 0) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA129 + difference 0 4) (sourceB129 + difference 4 0) sourceC129) = raw4345 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4345; decide +kernel
    rw [ha]
    exact (canonical4345 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA129 + difference 0 5) (sourceB129 + difference 5 0) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA129 + difference 0 5) (sourceB129 + difference 5 0) sourceC129) = raw4551 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4551; decide +kernel
    rw [ha]
    exact (canonical4551 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA129 + difference 1 0) (sourceB129 + difference 0 1) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA129 + difference 1 0) (sourceB129 + difference 0 1) sourceC129) = raw3662 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw3662; decide +kernel
    rw [ha]
    exact (canonical3662 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA129 + difference 1 2) (sourceB129 + difference 2 1) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA129 + difference 1 2) (sourceB129 + difference 2 1) sourceC129) = raw4552 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4552; decide +kernel
    rw [ha]
    exact (canonical4552 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA129 + difference 1 3) (sourceB129 + difference 3 1) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA129 + difference 1 3) (sourceB129 + difference 3 1) sourceC129) = raw4553 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4553; decide +kernel
    rw [ha]
    exact (canonical4553 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA129 + difference 1 4) (sourceB129 + difference 4 1) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA129 + difference 1 4) (sourceB129 + difference 4 1) sourceC129) = raw4350 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4350; decide +kernel
    rw [ha]
    exact (canonical4350 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA129 + difference 1 5) (sourceB129 + difference 5 1) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA129 + difference 1 5) (sourceB129 + difference 5 1) sourceC129) = raw4554 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4554; decide +kernel
    rw [ha]
    exact (canonical4554 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA129 + difference 2 0) (sourceB129 + difference 0 2) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA129 + difference 2 0) (sourceB129 + difference 0 2) sourceC129) = raw3667 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw3667; decide +kernel
    rw [ha]
    exact (canonical3667 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA129 + difference 2 1) (sourceB129 + difference 1 2) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA129 + difference 2 1) (sourceB129 + difference 1 2) sourceC129) = raw4045 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4045; decide +kernel
    rw [ha]
    exact (canonical4045 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA129 + difference 2 3) (sourceB129 + difference 3 2) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA129 + difference 2 3) (sourceB129 + difference 3 2) sourceC129) = raw4555 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4555; decide +kernel
    rw [ha]
    exact (canonical4555 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA129 + difference 2 4) (sourceB129 + difference 4 2) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA129 + difference 2 4) (sourceB129 + difference 4 2) sourceC129) = raw3857 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw3857; decide +kernel
    rw [ha]
    exact (canonical3857 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA129 + difference 2 5) (sourceB129 + difference 5 2) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA129 + difference 2 5) (sourceB129 + difference 5 2) sourceC129) = raw4556 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4556; decide +kernel
    rw [ha]
    exact (canonical4556 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA129 + difference 3 0) (sourceB129 + difference 0 3) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA129 + difference 3 0) (sourceB129 + difference 0 3) sourceC129) = raw3873 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw3873; decide +kernel
    rw [ha]
    exact (canonical3873 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA129 + difference 3 1) (sourceB129 + difference 1 3) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA129 + difference 3 1) (sourceB129 + difference 1 3) sourceC129) = raw3655 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw3655; decide +kernel
    rw [ha]
    exact (canonical3655 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA129 + difference 3 2) (sourceB129 + difference 2 3) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA129 + difference 3 2) (sourceB129 + difference 2 3) sourceC129) = raw3656 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw3656; decide +kernel
    rw [ha]
    exact (canonical3656 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA129 + difference 3 4) (sourceB129 + difference 4 3) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA129 + difference 3 4) (sourceB129 + difference 4 3) sourceC129) = raw3658 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw3658; decide +kernel
    rw [ha]
    exact (canonical3658 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA129 + difference 3 5) (sourceB129 + difference 5 3) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA129 + difference 3 5) (sourceB129 + difference 5 3) sourceC129) = raw3659 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw3659; decide +kernel
    rw [ha]
    exact (canonical3659 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA129 + difference 4 0) (sourceB129 + difference 0 4) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4900) := by
    have ha : (tripleCharges (sourceA129 + difference 4 0) (sourceB129 + difference 0 4) sourceC129) = raw3678 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw3678; decide +kernel
    rw [ha]
    exact (canonical3678 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA129 + difference 4 1) (sourceB129 + difference 1 4) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA129 + difference 4 1) (sourceB129 + difference 1 4) sourceC129) = raw4053 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4053; decide +kernel
    rw [ha]
    exact (canonical4053 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA129 + difference 4 2) (sourceB129 + difference 2 4) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA129 + difference 4 2) (sourceB129 + difference 2 4) sourceC129) = raw4557 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4557; decide +kernel
    rw [ha]
    exact (canonical4557 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA129 + difference 4 3) (sourceB129 + difference 3 4) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA129 + difference 4 3) (sourceB129 + difference 3 4) sourceC129) = raw4558 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4558; decide +kernel
    rw [ha]
    exact (canonical4558 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA129 + difference 4 5) (sourceB129 + difference 5 4) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4508) := by
    have ha : (tripleCharges (sourceA129 + difference 4 5) (sourceB129 + difference 5 4) sourceC129) = raw4559 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4559; decide +kernel
    rw [ha]
    exact (canonical4559 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA129 + difference 5 0) (sourceB129 + difference 0 5) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA129 + difference 5 0) (sourceB129 + difference 0 5) sourceC129) = raw3683 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw3683; decide +kernel
    rw [ha]
    exact (canonical3683 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA129 + difference 5 1) (sourceB129 + difference 1 5) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA129 + difference 5 1) (sourceB129 + difference 1 5) sourceC129) = raw4244 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4244; decide +kernel
    rw [ha]
    exact (canonical4244 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA129 + difference 5 2) (sourceB129 + difference 2 5) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA129 + difference 5 2) (sourceB129 + difference 2 5) sourceC129) = raw4038 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4038; decide +kernel
    rw [ha]
    exact (canonical4038 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA129 + difference 5 3) (sourceB129 + difference 3 5) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA129 + difference 5 3) (sourceB129 + difference 3 5) sourceC129) = raw4039 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4039; decide +kernel
    rw [ha]
    exact (canonical4039 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA129 + difference 5 4) (sourceB129 + difference 4 5) sourceC129) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA129 + difference 5 4) (sourceB129 + difference 4 5) sourceC129) = raw4040 := by
      apply Matrix.ext; unfold tripleCharges sourceA129 sourceB129 sourceC129 difference raw4040; decide +kernel
    rw [ha]
    exact (canonical4040 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA129 sourceB129 sourceC129
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm129, Integer.Sparse.eval]
  linarith only [hs]

def sourceA130 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB130 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC130 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm130 : Integer.Sparse Master := [(Sum.inr 1436, 3), (Sum.inr 1438, 1), (Sum.inr 1454, 1), (Sum.inr 2136, 3), (Sum.inr 2255, 3), (Sum.inr 2281, 1), (Sum.inr 2285, 1), (Sum.inr 2716, 6), (Sum.inr 2734, 3), (Sum.inr 2755, 3), (Sum.inr 2770, 1), (Sum.inr 3095, 3), (Sum.inr 3114, 1)]

theorem sourceEq130 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm130 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA130 + difference 0 1) (sourceB130 + difference 1 0) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA130 + difference 0 1) (sourceB130 + difference 1 0) sourceC130) = raw4063 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4063; decide +kernel
    rw [ha]
    exact (canonical4063 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA130 + difference 0 2) (sourceB130 + difference 2 0) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA130 + difference 0 2) (sourceB130 + difference 2 0) sourceC130) = raw4560 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4560; decide +kernel
    rw [ha]
    exact (canonical4560 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA130 + difference 0 3) (sourceB130 + difference 3 0) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA130 + difference 0 3) (sourceB130 + difference 3 0) sourceC130) = raw4561 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4561; decide +kernel
    rw [ha]
    exact (canonical4561 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA130 + difference 0 4) (sourceB130 + difference 4 0) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA130 + difference 0 4) (sourceB130 + difference 4 0) sourceC130) = raw4360 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4360; decide +kernel
    rw [ha]
    exact (canonical4360 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA130 + difference 0 5) (sourceB130 + difference 5 0) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1454) := by
    have ha : (tripleCharges (sourceA130 + difference 0 5) (sourceB130 + difference 5 0) sourceC130) = raw4562 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4562; decide +kernel
    rw [ha]
    exact (canonical4562 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA130 + difference 1 0) (sourceB130 + difference 0 1) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA130 + difference 1 0) (sourceB130 + difference 0 1) sourceC130) = raw3692 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw3692; decide +kernel
    rw [ha]
    exact (canonical3692 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA130 + difference 1 2) (sourceB130 + difference 2 1) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA130 + difference 1 2) (sourceB130 + difference 2 1) sourceC130) = raw4563 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4563; decide +kernel
    rw [ha]
    exact (canonical4563 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA130 + difference 1 3) (sourceB130 + difference 3 1) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA130 + difference 1 3) (sourceB130 + difference 3 1) sourceC130) = raw4564 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4564; decide +kernel
    rw [ha]
    exact (canonical4564 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA130 + difference 1 4) (sourceB130 + difference 4 1) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA130 + difference 1 4) (sourceB130 + difference 4 1) sourceC130) = raw4365 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4365; decide +kernel
    rw [ha]
    exact (canonical4365 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA130 + difference 1 5) (sourceB130 + difference 5 1) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA130 + difference 1 5) (sourceB130 + difference 5 1) sourceC130) = raw4565 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4565; decide +kernel
    rw [ha]
    exact (canonical4565 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA130 + difference 2 0) (sourceB130 + difference 0 2) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA130 + difference 2 0) (sourceB130 + difference 0 2) sourceC130) = raw3697 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw3697; decide +kernel
    rw [ha]
    exact (canonical3697 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA130 + difference 2 1) (sourceB130 + difference 1 2) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA130 + difference 2 1) (sourceB130 + difference 1 2) sourceC130) = raw4071 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4071; decide +kernel
    rw [ha]
    exact (canonical4071 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA130 + difference 2 3) (sourceB130 + difference 3 2) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA130 + difference 2 3) (sourceB130 + difference 3 2) sourceC130) = raw4566 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4566; decide +kernel
    rw [ha]
    exact (canonical4566 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA130 + difference 2 4) (sourceB130 + difference 4 2) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA130 + difference 2 4) (sourceB130 + difference 4 2) sourceC130) = raw3879 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw3879; decide +kernel
    rw [ha]
    exact (canonical3879 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA130 + difference 2 5) (sourceB130 + difference 5 2) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA130 + difference 2 5) (sourceB130 + difference 5 2) sourceC130) = raw4567 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4567; decide +kernel
    rw [ha]
    exact (canonical4567 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA130 + difference 3 0) (sourceB130 + difference 0 3) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA130 + difference 3 0) (sourceB130 + difference 0 3) sourceC130) = raw3895 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw3895; decide +kernel
    rw [ha]
    exact (canonical3895 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA130 + difference 3 1) (sourceB130 + difference 1 3) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA130 + difference 3 1) (sourceB130 + difference 1 3) sourceC130) = raw3685 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw3685; decide +kernel
    rw [ha]
    exact (canonical3685 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA130 + difference 3 2) (sourceB130 + difference 2 3) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA130 + difference 3 2) (sourceB130 + difference 2 3) sourceC130) = raw3686 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw3686; decide +kernel
    rw [ha]
    exact (canonical3686 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA130 + difference 3 4) (sourceB130 + difference 4 3) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA130 + difference 3 4) (sourceB130 + difference 4 3) sourceC130) = raw3688 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw3688; decide +kernel
    rw [ha]
    exact (canonical3688 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA130 + difference 3 5) (sourceB130 + difference 5 3) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA130 + difference 3 5) (sourceB130 + difference 5 3) sourceC130) = raw3689 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw3689; decide +kernel
    rw [ha]
    exact (canonical3689 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA130 + difference 4 0) (sourceB130 + difference 0 4) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2285) := by
    have ha : (tripleCharges (sourceA130 + difference 4 0) (sourceB130 + difference 0 4) sourceC130) = raw3708 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw3708; decide +kernel
    rw [ha]
    exact (canonical3708 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA130 + difference 4 1) (sourceB130 + difference 1 4) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA130 + difference 4 1) (sourceB130 + difference 1 4) sourceC130) = raw4079 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4079; decide +kernel
    rw [ha]
    exact (canonical4079 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA130 + difference 4 2) (sourceB130 + difference 2 4) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA130 + difference 4 2) (sourceB130 + difference 2 4) sourceC130) = raw4568 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4568; decide +kernel
    rw [ha]
    exact (canonical4568 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA130 + difference 4 3) (sourceB130 + difference 3 4) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA130 + difference 4 3) (sourceB130 + difference 3 4) sourceC130) = raw4569 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4569; decide +kernel
    rw [ha]
    exact (canonical4569 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA130 + difference 4 5) (sourceB130 + difference 5 4) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1438) := by
    have ha : (tripleCharges (sourceA130 + difference 4 5) (sourceB130 + difference 5 4) sourceC130) = raw4570 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4570; decide +kernel
    rw [ha]
    exact (canonical4570 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA130 + difference 5 0) (sourceB130 + difference 0 5) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA130 + difference 5 0) (sourceB130 + difference 0 5) sourceC130) = raw3713 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw3713; decide +kernel
    rw [ha]
    exact (canonical3713 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA130 + difference 5 1) (sourceB130 + difference 1 5) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA130 + difference 5 1) (sourceB130 + difference 1 5) sourceC130) = raw4262 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4262; decide +kernel
    rw [ha]
    exact (canonical4262 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA130 + difference 5 2) (sourceB130 + difference 2 5) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA130 + difference 5 2) (sourceB130 + difference 2 5) sourceC130) = raw4064 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4064; decide +kernel
    rw [ha]
    exact (canonical4064 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA130 + difference 5 3) (sourceB130 + difference 3 5) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA130 + difference 5 3) (sourceB130 + difference 3 5) sourceC130) = raw4065 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4065; decide +kernel
    rw [ha]
    exact (canonical4065 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA130 + difference 5 4) (sourceB130 + difference 4 5) sourceC130) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA130 + difference 5 4) (sourceB130 + difference 4 5) sourceC130) = raw4066 := by
      apply Matrix.ext; unfold tripleCharges sourceA130 sourceB130 sourceC130 difference raw4066; decide +kernel
    rw [ha]
    exact (canonical4066 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA130 sourceB130 sourceC130
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm130, Integer.Sparse.eval]
  linarith only [hs]

def sourceA131 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB131 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC131 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm131 : Integer.Sparse Master := [(Sum.inr 1716, 3), (Sum.inr 1741, 1), (Sum.inr 1747, 1), (Sum.inr 2197, 6), (Sum.inr 2218, 3), (Sum.inr 2222, 3), (Sum.inr 2247, 3), (Sum.inr 2255, 3), (Sum.inr 2268, 1), (Sum.inr 2285, 1), (Sum.inr 2734, 3), (Sum.inr 2770, 1), (Sum.inr 2778, 1)]

theorem sourceEq131 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm131 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA131 + difference 0 1) (sourceB131 + difference 1 0) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA131 + difference 0 1) (sourceB131 + difference 1 0) sourceC131) = raw4571 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4571; decide +kernel
    rw [ha]
    exact (canonical4571 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA131 + difference 0 2) (sourceB131 + difference 2 0) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA131 + difference 0 2) (sourceB131 + difference 2 0) sourceC131) = raw4572 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4572; decide +kernel
    rw [ha]
    exact (canonical4572 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA131 + difference 0 3) (sourceB131 + difference 3 0) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA131 + difference 0 3) (sourceB131 + difference 3 0) sourceC131) = raw4573 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4573; decide +kernel
    rw [ha]
    exact (canonical4573 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA131 + difference 0 4) (sourceB131 + difference 4 0) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA131 + difference 0 4) (sourceB131 + difference 4 0) sourceC131) = raw4574 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4574; decide +kernel
    rw [ha]
    exact (canonical4574 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA131 + difference 0 5) (sourceB131 + difference 5 0) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA131 + difference 0 5) (sourceB131 + difference 5 0) sourceC131) = raw4575 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4575; decide +kernel
    rw [ha]
    exact (canonical4575 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA131 + difference 1 0) (sourceB131 + difference 0 1) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA131 + difference 1 0) (sourceB131 + difference 0 1) sourceC131) = raw4576 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4576; decide +kernel
    rw [ha]
    exact (canonical4576 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA131 + difference 1 2) (sourceB131 + difference 2 1) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA131 + difference 1 2) (sourceB131 + difference 2 1) sourceC131) = raw4577 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4577; decide +kernel
    rw [ha]
    exact (canonical4577 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA131 + difference 1 3) (sourceB131 + difference 3 1) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA131 + difference 1 3) (sourceB131 + difference 3 1) sourceC131) = raw4578 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4578; decide +kernel
    rw [ha]
    exact (canonical4578 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA131 + difference 1 4) (sourceB131 + difference 4 1) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA131 + difference 1 4) (sourceB131 + difference 4 1) sourceC131) = raw4579 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4579; decide +kernel
    rw [ha]
    exact (canonical4579 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA131 + difference 1 5) (sourceB131 + difference 5 1) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA131 + difference 1 5) (sourceB131 + difference 5 1) sourceC131) = raw4580 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4580; decide +kernel
    rw [ha]
    exact (canonical4580 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA131 + difference 2 0) (sourceB131 + difference 0 2) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA131 + difference 2 0) (sourceB131 + difference 0 2) sourceC131) = raw4581 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4581; decide +kernel
    rw [ha]
    exact (canonical4581 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA131 + difference 2 1) (sourceB131 + difference 1 2) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA131 + difference 2 1) (sourceB131 + difference 1 2) sourceC131) = raw4582 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4582; decide +kernel
    rw [ha]
    exact (canonical4582 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA131 + difference 2 3) (sourceB131 + difference 3 2) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA131 + difference 2 3) (sourceB131 + difference 3 2) sourceC131) = raw4583 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4583; decide +kernel
    rw [ha]
    exact (canonical4583 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA131 + difference 2 4) (sourceB131 + difference 4 2) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA131 + difference 2 4) (sourceB131 + difference 4 2) sourceC131) = raw4584 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4584; decide +kernel
    rw [ha]
    exact (canonical4584 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA131 + difference 2 5) (sourceB131 + difference 5 2) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA131 + difference 2 5) (sourceB131 + difference 5 2) sourceC131) = raw4585 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4585; decide +kernel
    rw [ha]
    exact (canonical4585 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA131 + difference 3 0) (sourceB131 + difference 0 3) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA131 + difference 3 0) (sourceB131 + difference 0 3) sourceC131) = raw4586 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4586; decide +kernel
    rw [ha]
    exact (canonical4586 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA131 + difference 3 1) (sourceB131 + difference 1 3) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA131 + difference 3 1) (sourceB131 + difference 1 3) sourceC131) = raw4587 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4587; decide +kernel
    rw [ha]
    exact (canonical4587 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA131 + difference 3 2) (sourceB131 + difference 2 3) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA131 + difference 3 2) (sourceB131 + difference 2 3) sourceC131) = raw4588 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4588; decide +kernel
    rw [ha]
    exact (canonical4588 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA131 + difference 3 4) (sourceB131 + difference 4 3) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA131 + difference 3 4) (sourceB131 + difference 4 3) sourceC131) = raw4589 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4589; decide +kernel
    rw [ha]
    exact (canonical4589 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA131 + difference 3 5) (sourceB131 + difference 5 3) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA131 + difference 3 5) (sourceB131 + difference 5 3) sourceC131) = raw4590 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4590; decide +kernel
    rw [ha]
    exact (canonical4590 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA131 + difference 4 0) (sourceB131 + difference 0 4) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2285) := by
    have ha : (tripleCharges (sourceA131 + difference 4 0) (sourceB131 + difference 0 4) sourceC131) = raw4591 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4591; decide +kernel
    rw [ha]
    exact (canonical4591 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA131 + difference 4 1) (sourceB131 + difference 1 4) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA131 + difference 4 1) (sourceB131 + difference 1 4) sourceC131) = raw4592 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4592; decide +kernel
    rw [ha]
    exact (canonical4592 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA131 + difference 4 2) (sourceB131 + difference 2 4) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA131 + difference 4 2) (sourceB131 + difference 2 4) sourceC131) = raw4593 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4593; decide +kernel
    rw [ha]
    exact (canonical4593 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA131 + difference 4 3) (sourceB131 + difference 3 4) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA131 + difference 4 3) (sourceB131 + difference 3 4) sourceC131) = raw4594 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4594; decide +kernel
    rw [ha]
    exact (canonical4594 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA131 + difference 4 5) (sourceB131 + difference 5 4) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1747) := by
    have ha : (tripleCharges (sourceA131 + difference 4 5) (sourceB131 + difference 5 4) sourceC131) = raw4595 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4595; decide +kernel
    rw [ha]
    exact (canonical4595 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA131 + difference 5 0) (sourceB131 + difference 0 5) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2778) := by
    have ha : (tripleCharges (sourceA131 + difference 5 0) (sourceB131 + difference 0 5) sourceC131) = raw4596 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4596; decide +kernel
    rw [ha]
    exact (canonical4596 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA131 + difference 5 1) (sourceB131 + difference 1 5) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA131 + difference 5 1) (sourceB131 + difference 1 5) sourceC131) = raw4597 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4597; decide +kernel
    rw [ha]
    exact (canonical4597 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA131 + difference 5 2) (sourceB131 + difference 2 5) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA131 + difference 5 2) (sourceB131 + difference 2 5) sourceC131) = raw4598 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4598; decide +kernel
    rw [ha]
    exact (canonical4598 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA131 + difference 5 3) (sourceB131 + difference 3 5) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA131 + difference 5 3) (sourceB131 + difference 3 5) sourceC131) = raw4599 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4599; decide +kernel
    rw [ha]
    exact (canonical4599 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA131 + difference 5 4) (sourceB131 + difference 4 5) sourceC131) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA131 + difference 5 4) (sourceB131 + difference 4 5) sourceC131) = raw4600 := by
      apply Matrix.ext; unfold tripleCharges sourceA131 sourceB131 sourceC131 difference raw4600; decide +kernel
    rw [ha]
    exact (canonical4600 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA131 sourceB131 sourceC131
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm131, Integer.Sparse.eval]
  linarith only [hs]

def sourceA132 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB132 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC132 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm132 : Integer.Sparse Master := [(Sum.inr 1094, 1), (Sum.inr 2065, 3), (Sum.inr 2292, 1), (Sum.inr 2294, 1), (Sum.inr 4085, -1)]

theorem sourceEq132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm132 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA132 + difference 0 0) (sourceB132 + difference 0 0) sourceC132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA132 + difference 0 0) (sourceB132 + difference 0 0) sourceC132) = raw3718 := by
      apply Matrix.ext; unfold tripleCharges sourceA132 sourceB132 sourceC132 difference raw3718; decide +kernel
    rw [ha]
    exact (canonical3718 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA132 + difference 0 1) (sourceB132 + difference 1 0) sourceC132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA132 + difference 0 1) (sourceB132 + difference 1 0) sourceC132) = raw4090 := by
      apply Matrix.ext; unfold tripleCharges sourceA132 sourceB132 sourceC132 difference raw4090; decide +kernel
    rw [ha]
    exact (canonical4090 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA132 + difference 0 2) (sourceB132 + difference 2 0) sourceC132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA132 + difference 0 2) (sourceB132 + difference 2 0) sourceC132) = raw4601 := by
      apply Matrix.ext; unfold tripleCharges sourceA132 sourceB132 sourceC132 difference raw4601; decide +kernel
    rw [ha]
    exact (canonical4601 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA132 + difference 0 3) (sourceB132 + difference 3 0) sourceC132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA132 + difference 0 3) (sourceB132 + difference 3 0) sourceC132) = raw4602 := by
      apply Matrix.ext; unfold tripleCharges sourceA132 sourceB132 sourceC132 difference raw4602; decide +kernel
    rw [ha]
    exact (canonical4602 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA132 + difference 0 4) (sourceB132 + difference 4 0) sourceC132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA132 + difference 0 4) (sourceB132 + difference 4 0) sourceC132) = raw4375 := by
      apply Matrix.ext; unfold tripleCharges sourceA132 sourceB132 sourceC132 difference raw4375; decide +kernel
    rw [ha]
    exact (canonical4375 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA132 + difference 0 5) (sourceB132 + difference 5 0) sourceC132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1094) := by
    have ha : (tripleCharges (sourceA132 + difference 0 5) (sourceB132 + difference 5 0) sourceC132) = raw4603 := by
      apply Matrix.ext; unfold tripleCharges sourceA132 sourceB132 sourceC132 difference raw4603; decide +kernel
    rw [ha]
    exact (canonical4603 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA132 + sourceB132) sourceC132) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA132 + sourceB132) sourceC132) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA132 sourceB132 sourceC132 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA132 sourceB132 sourceC132
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm132, Integer.Sparse.eval]
  linarith only [hs]

def sourceA133 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB133 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC133 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm133 : Integer.Sparse Master := [(Sum.inr 4253, 2), (Sum.inr 4257, 1), (Sum.inr 4270, 2), (Sum.inr 4583, 2), (Sum.inr 4605, 2), (Sum.inr 4729, 2), (Sum.inr 4742, 4), (Sum.inr 4807, 4), (Sum.inr 4843, 2), (Sum.inr 4889, 2), (Sum.inr 4896, 2), (Sum.inr 5284, 2), (Sum.inr 5294, 2), (Sum.inr 5453, 1)]

theorem sourceEq133 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm133 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA133 + difference 0 1) (sourceB133 + difference 1 0) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA133 + difference 0 1) (sourceB133 + difference 1 0) sourceC133) = raw2687 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw2687; decide +kernel
    rw [ha]
    exact (canonical2687 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA133 + difference 0 2) (sourceB133 + difference 2 0) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA133 + difference 0 2) (sourceB133 + difference 2 0) sourceC133) = raw2688 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw2688; decide +kernel
    rw [ha]
    exact (canonical2688 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA133 + difference 0 3) (sourceB133 + difference 3 0) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA133 + difference 0 3) (sourceB133 + difference 3 0) sourceC133) = raw2689 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw2689; decide +kernel
    rw [ha]
    exact (canonical2689 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA133 + difference 0 4) (sourceB133 + difference 4 0) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA133 + difference 0 4) (sourceB133 + difference 4 0) sourceC133) = raw2690 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw2690; decide +kernel
    rw [ha]
    exact (canonical2690 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA133 + difference 0 5) (sourceB133 + difference 5 0) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA133 + difference 0 5) (sourceB133 + difference 5 0) sourceC133) = raw4604 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4604; decide +kernel
    rw [ha]
    exact (canonical4604 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA133 + difference 1 0) (sourceB133 + difference 0 1) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA133 + difference 1 0) (sourceB133 + difference 0 1) sourceC133) = raw4605 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4605; decide +kernel
    rw [ha]
    exact (canonical4605 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA133 + difference 1 2) (sourceB133 + difference 2 1) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4729) := by
    have ha : (tripleCharges (sourceA133 + difference 1 2) (sourceB133 + difference 2 1) sourceC133) = raw4606 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4606; decide +kernel
    rw [ha]
    exact (canonical4606 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA133 + difference 1 3) (sourceB133 + difference 3 1) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA133 + difference 1 3) (sourceB133 + difference 3 1) sourceC133) = raw4607 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4607; decide +kernel
    rw [ha]
    exact (canonical4607 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA133 + difference 1 4) (sourceB133 + difference 4 1) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA133 + difference 1 4) (sourceB133 + difference 4 1) sourceC133) = raw4608 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4608; decide +kernel
    rw [ha]
    exact (canonical4608 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA133 + difference 1 5) (sourceB133 + difference 5 1) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA133 + difference 1 5) (sourceB133 + difference 5 1) sourceC133) = raw2666 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw2666; decide +kernel
    rw [ha]
    exact (canonical2666 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA133 + difference 2 0) (sourceB133 + difference 0 2) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA133 + difference 2 0) (sourceB133 + difference 0 2) sourceC133) = raw4609 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4609; decide +kernel
    rw [ha]
    exact (canonical4609 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA133 + difference 2 1) (sourceB133 + difference 1 2) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4729) := by
    have ha : (tripleCharges (sourceA133 + difference 2 1) (sourceB133 + difference 1 2) sourceC133) = raw4610 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4610; decide +kernel
    rw [ha]
    exact (canonical4610 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA133 + difference 2 3) (sourceB133 + difference 3 2) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA133 + difference 2 3) (sourceB133 + difference 3 2) sourceC133) = raw4611 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4611; decide +kernel
    rw [ha]
    exact (canonical4611 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA133 + difference 2 4) (sourceB133 + difference 4 2) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA133 + difference 2 4) (sourceB133 + difference 4 2) sourceC133) = raw4612 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4612; decide +kernel
    rw [ha]
    exact (canonical4612 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA133 + difference 2 5) (sourceB133 + difference 5 2) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA133 + difference 2 5) (sourceB133 + difference 5 2) sourceC133) = raw2671 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw2671; decide +kernel
    rw [ha]
    exact (canonical2671 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA133 + difference 3 0) (sourceB133 + difference 0 3) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA133 + difference 3 0) (sourceB133 + difference 0 3) sourceC133) = raw4613 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4613; decide +kernel
    rw [ha]
    exact (canonical4613 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA133 + difference 3 1) (sourceB133 + difference 1 3) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA133 + difference 3 1) (sourceB133 + difference 1 3) sourceC133) = raw4614 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4614; decide +kernel
    rw [ha]
    exact (canonical4614 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA133 + difference 3 2) (sourceB133 + difference 2 3) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA133 + difference 3 2) (sourceB133 + difference 2 3) sourceC133) = raw4615 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4615; decide +kernel
    rw [ha]
    exact (canonical4615 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA133 + difference 3 4) (sourceB133 + difference 4 3) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA133 + difference 3 4) (sourceB133 + difference 4 3) sourceC133) = raw4616 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4616; decide +kernel
    rw [ha]
    exact (canonical4616 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA133 + difference 3 5) (sourceB133 + difference 5 3) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA133 + difference 3 5) (sourceB133 + difference 5 3) sourceC133) = raw2676 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw2676; decide +kernel
    rw [ha]
    exact (canonical2676 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA133 + difference 4 0) (sourceB133 + difference 0 4) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA133 + difference 4 0) (sourceB133 + difference 0 4) sourceC133) = raw4617 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4617; decide +kernel
    rw [ha]
    exact (canonical4617 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA133 + difference 4 1) (sourceB133 + difference 1 4) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA133 + difference 4 1) (sourceB133 + difference 1 4) sourceC133) = raw4618 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4618; decide +kernel
    rw [ha]
    exact (canonical4618 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA133 + difference 4 2) (sourceB133 + difference 2 4) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA133 + difference 4 2) (sourceB133 + difference 2 4) sourceC133) = raw4619 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4619; decide +kernel
    rw [ha]
    exact (canonical4619 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA133 + difference 4 3) (sourceB133 + difference 3 4) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA133 + difference 4 3) (sourceB133 + difference 3 4) sourceC133) = raw4620 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4620; decide +kernel
    rw [ha]
    exact (canonical4620 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA133 + difference 4 5) (sourceB133 + difference 5 4) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA133 + difference 4 5) (sourceB133 + difference 5 4) sourceC133) = raw2681 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw2681; decide +kernel
    rw [ha]
    exact (canonical2681 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA133 + difference 5 0) (sourceB133 + difference 0 5) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4257) := by
    have ha : (tripleCharges (sourceA133 + difference 5 0) (sourceB133 + difference 0 5) sourceC133) = raw4621 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4621; decide +kernel
    rw [ha]
    exact (canonical4621 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA133 + difference 5 1) (sourceB133 + difference 1 5) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4253) := by
    have ha : (tripleCharges (sourceA133 + difference 5 1) (sourceB133 + difference 1 5) sourceC133) = raw4622 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4622; decide +kernel
    rw [ha]
    exact (canonical4622 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA133 + difference 5 2) (sourceB133 + difference 2 5) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4253) := by
    have ha : (tripleCharges (sourceA133 + difference 5 2) (sourceB133 + difference 2 5) sourceC133) = raw4623 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4623; decide +kernel
    rw [ha]
    exact (canonical4623 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA133 + difference 5 3) (sourceB133 + difference 3 5) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA133 + difference 5 3) (sourceB133 + difference 3 5) sourceC133) = raw4624 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4624; decide +kernel
    rw [ha]
    exact (canonical4624 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA133 + difference 5 4) (sourceB133 + difference 4 5) sourceC133) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA133 + difference 5 4) (sourceB133 + difference 4 5) sourceC133) = raw4625 := by
      apply Matrix.ext; unfold tripleCharges sourceA133 sourceB133 sourceC133 difference raw4625; decide +kernel
    rw [ha]
    exact (canonical4625 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA133 sourceB133 sourceC133
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm133, Integer.Sparse.eval]
  linarith only [hs]

def sourceA134 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB134 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC134 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm134 : Integer.Sparse Master := [(Sum.inr 787, 2), (Sum.inr 791, 1), (Sum.inr 813, 2), (Sum.inr 1202, 2), (Sum.inr 1239, 2), (Sum.inr 1898, 2), (Sum.inr 1915, 4), (Sum.inr 2025, 4), (Sum.inr 2062, 2), (Sum.inr 2245, 2), (Sum.inr 2266, 2), (Sum.inr 3077, 2), (Sum.inr 3101, 2), (Sum.inr 3912, 1)]

theorem sourceEq134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm134 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA134 + difference 0 1) (sourceB134 + difference 1 0) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA134 + difference 0 1) (sourceB134 + difference 1 0) sourceC134) = raw2717 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw2717; decide +kernel
    rw [ha]
    exact (canonical2717 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA134 + difference 0 2) (sourceB134 + difference 2 0) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA134 + difference 0 2) (sourceB134 + difference 2 0) sourceC134) = raw2718 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw2718; decide +kernel
    rw [ha]
    exact (canonical2718 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA134 + difference 0 3) (sourceB134 + difference 3 0) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA134 + difference 0 3) (sourceB134 + difference 3 0) sourceC134) = raw2719 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw2719; decide +kernel
    rw [ha]
    exact (canonical2719 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA134 + difference 0 4) (sourceB134 + difference 4 0) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA134 + difference 0 4) (sourceB134 + difference 4 0) sourceC134) = raw2720 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw2720; decide +kernel
    rw [ha]
    exact (canonical2720 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA134 + difference 0 5) (sourceB134 + difference 5 0) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3912) := by
    have ha : (tripleCharges (sourceA134 + difference 0 5) (sourceB134 + difference 5 0) sourceC134) = raw4626 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4626; decide +kernel
    rw [ha]
    exact (canonical4626 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA134 + difference 1 0) (sourceB134 + difference 0 1) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA134 + difference 1 0) (sourceB134 + difference 0 1) sourceC134) = raw4627 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4627; decide +kernel
    rw [ha]
    exact (canonical4627 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA134 + difference 1 2) (sourceB134 + difference 2 1) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA134 + difference 1 2) (sourceB134 + difference 2 1) sourceC134) = raw4628 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4628; decide +kernel
    rw [ha]
    exact (canonical4628 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA134 + difference 1 3) (sourceB134 + difference 3 1) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1915) := by
    have ha : (tripleCharges (sourceA134 + difference 1 3) (sourceB134 + difference 3 1) sourceC134) = raw4629 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4629; decide +kernel
    rw [ha]
    exact (canonical4629 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA134 + difference 1 4) (sourceB134 + difference 4 1) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1915) := by
    have ha : (tripleCharges (sourceA134 + difference 1 4) (sourceB134 + difference 4 1) sourceC134) = raw4630 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4630; decide +kernel
    rw [ha]
    exact (canonical4630 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA134 + difference 1 5) (sourceB134 + difference 5 1) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA134 + difference 1 5) (sourceB134 + difference 5 1) sourceC134) = raw2696 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw2696; decide +kernel
    rw [ha]
    exact (canonical2696 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA134 + difference 2 0) (sourceB134 + difference 0 2) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA134 + difference 2 0) (sourceB134 + difference 0 2) sourceC134) = raw4631 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4631; decide +kernel
    rw [ha]
    exact (canonical4631 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA134 + difference 2 1) (sourceB134 + difference 1 2) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA134 + difference 2 1) (sourceB134 + difference 1 2) sourceC134) = raw4632 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4632; decide +kernel
    rw [ha]
    exact (canonical4632 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA134 + difference 2 3) (sourceB134 + difference 3 2) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1915) := by
    have ha : (tripleCharges (sourceA134 + difference 2 3) (sourceB134 + difference 3 2) sourceC134) = raw4633 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4633; decide +kernel
    rw [ha]
    exact (canonical4633 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA134 + difference 2 4) (sourceB134 + difference 4 2) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1915) := by
    have ha : (tripleCharges (sourceA134 + difference 2 4) (sourceB134 + difference 4 2) sourceC134) = raw4634 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4634; decide +kernel
    rw [ha]
    exact (canonical4634 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA134 + difference 2 5) (sourceB134 + difference 5 2) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA134 + difference 2 5) (sourceB134 + difference 5 2) sourceC134) = raw2701 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw2701; decide +kernel
    rw [ha]
    exact (canonical2701 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA134 + difference 3 0) (sourceB134 + difference 0 3) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA134 + difference 3 0) (sourceB134 + difference 0 3) sourceC134) = raw4635 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4635; decide +kernel
    rw [ha]
    exact (canonical4635 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA134 + difference 3 1) (sourceB134 + difference 1 3) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA134 + difference 3 1) (sourceB134 + difference 1 3) sourceC134) = raw4636 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4636; decide +kernel
    rw [ha]
    exact (canonical4636 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA134 + difference 3 2) (sourceB134 + difference 2 3) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA134 + difference 3 2) (sourceB134 + difference 2 3) sourceC134) = raw4637 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4637; decide +kernel
    rw [ha]
    exact (canonical4637 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA134 + difference 3 4) (sourceB134 + difference 4 3) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA134 + difference 3 4) (sourceB134 + difference 4 3) sourceC134) = raw4638 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4638; decide +kernel
    rw [ha]
    exact (canonical4638 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA134 + difference 3 5) (sourceB134 + difference 5 3) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA134 + difference 3 5) (sourceB134 + difference 5 3) sourceC134) = raw2706 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw2706; decide +kernel
    rw [ha]
    exact (canonical2706 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA134 + difference 4 0) (sourceB134 + difference 0 4) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA134 + difference 4 0) (sourceB134 + difference 0 4) sourceC134) = raw4639 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4639; decide +kernel
    rw [ha]
    exact (canonical4639 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA134 + difference 4 1) (sourceB134 + difference 1 4) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA134 + difference 4 1) (sourceB134 + difference 1 4) sourceC134) = raw4640 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4640; decide +kernel
    rw [ha]
    exact (canonical4640 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA134 + difference 4 2) (sourceB134 + difference 2 4) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA134 + difference 4 2) (sourceB134 + difference 2 4) sourceC134) = raw4641 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4641; decide +kernel
    rw [ha]
    exact (canonical4641 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA134 + difference 4 3) (sourceB134 + difference 3 4) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA134 + difference 4 3) (sourceB134 + difference 3 4) sourceC134) = raw4642 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4642; decide +kernel
    rw [ha]
    exact (canonical4642 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA134 + difference 4 5) (sourceB134 + difference 5 4) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA134 + difference 4 5) (sourceB134 + difference 5 4) sourceC134) = raw2711 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw2711; decide +kernel
    rw [ha]
    exact (canonical2711 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA134 + difference 5 0) (sourceB134 + difference 0 5) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 791) := by
    have ha : (tripleCharges (sourceA134 + difference 5 0) (sourceB134 + difference 0 5) sourceC134) = raw4643 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4643; decide +kernel
    rw [ha]
    exact (canonical4643 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA134 + difference 5 1) (sourceB134 + difference 1 5) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA134 + difference 5 1) (sourceB134 + difference 1 5) sourceC134) = raw4644 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4644; decide +kernel
    rw [ha]
    exact (canonical4644 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA134 + difference 5 2) (sourceB134 + difference 2 5) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA134 + difference 5 2) (sourceB134 + difference 2 5) sourceC134) = raw4645 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4645; decide +kernel
    rw [ha]
    exact (canonical4645 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA134 + difference 5 3) (sourceB134 + difference 3 5) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA134 + difference 5 3) (sourceB134 + difference 3 5) sourceC134) = raw4646 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4646; decide +kernel
    rw [ha]
    exact (canonical4646 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA134 + difference 5 4) (sourceB134 + difference 4 5) sourceC134) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA134 + difference 5 4) (sourceB134 + difference 4 5) sourceC134) = raw4647 := by
      apply Matrix.ext; unfold tripleCharges sourceA134 sourceB134 sourceC134 difference raw4647; decide +kernel
    rw [ha]
    exact (canonical4647 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA134 sourceB134 sourceC134
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm134, Integer.Sparse.eval]
  linarith only [hs]

def sourceA135 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB135 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC135 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm135 : Integer.Sparse Master := [(Sum.inr 4440, 2), (Sum.inr 4442, 2), (Sum.inr 4445, 1), (Sum.inr 4463, 2), (Sum.inr 4464, 2), (Sum.inr 4792, 2), (Sum.inr 4807, 4), (Sum.inr 4853, 4), (Sum.inr 4871, 2), (Sum.inr 4888, 2), (Sum.inr 4895, 2), (Sum.inr 5270, 2), (Sum.inr 5295, 2), (Sum.inr 5306, 1)]

theorem sourceEq135 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm135 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA135 + difference 0 1) (sourceB135 + difference 1 0) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA135 + difference 0 1) (sourceB135 + difference 1 0) sourceC135) = raw4648 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4648; decide +kernel
    rw [ha]
    exact (canonical4648 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA135 + difference 0 2) (sourceB135 + difference 2 0) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA135 + difference 0 2) (sourceB135 + difference 2 0) sourceC135) = raw4649 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4649; decide +kernel
    rw [ha]
    exact (canonical4649 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA135 + difference 0 3) (sourceB135 + difference 3 0) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA135 + difference 0 3) (sourceB135 + difference 3 0) sourceC135) = raw4650 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4650; decide +kernel
    rw [ha]
    exact (canonical4650 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA135 + difference 0 4) (sourceB135 + difference 4 0) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA135 + difference 0 4) (sourceB135 + difference 4 0) sourceC135) = raw4651 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4651; decide +kernel
    rw [ha]
    exact (canonical4651 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA135 + difference 0 5) (sourceB135 + difference 5 0) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA135 + difference 0 5) (sourceB135 + difference 5 0) sourceC135) = raw4652 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4652; decide +kernel
    rw [ha]
    exact (canonical4652 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA135 + difference 1 0) (sourceB135 + difference 0 1) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA135 + difference 1 0) (sourceB135 + difference 0 1) sourceC135) = raw4653 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4653; decide +kernel
    rw [ha]
    exact (canonical4653 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA135 + difference 1 2) (sourceB135 + difference 2 1) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA135 + difference 1 2) (sourceB135 + difference 2 1) sourceC135) = raw4654 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4654; decide +kernel
    rw [ha]
    exact (canonical4654 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA135 + difference 1 3) (sourceB135 + difference 3 1) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA135 + difference 1 3) (sourceB135 + difference 3 1) sourceC135) = raw4655 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4655; decide +kernel
    rw [ha]
    exact (canonical4655 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA135 + difference 1 4) (sourceB135 + difference 4 1) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA135 + difference 1 4) (sourceB135 + difference 4 1) sourceC135) = raw4656 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4656; decide +kernel
    rw [ha]
    exact (canonical4656 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA135 + difference 1 5) (sourceB135 + difference 5 1) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA135 + difference 1 5) (sourceB135 + difference 5 1) sourceC135) = raw4657 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4657; decide +kernel
    rw [ha]
    exact (canonical4657 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA135 + difference 2 0) (sourceB135 + difference 0 2) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA135 + difference 2 0) (sourceB135 + difference 0 2) sourceC135) = raw4658 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4658; decide +kernel
    rw [ha]
    exact (canonical4658 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA135 + difference 2 1) (sourceB135 + difference 1 2) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA135 + difference 2 1) (sourceB135 + difference 1 2) sourceC135) = raw4659 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4659; decide +kernel
    rw [ha]
    exact (canonical4659 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA135 + difference 2 3) (sourceB135 + difference 3 2) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA135 + difference 2 3) (sourceB135 + difference 3 2) sourceC135) = raw4660 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4660; decide +kernel
    rw [ha]
    exact (canonical4660 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA135 + difference 2 4) (sourceB135 + difference 4 2) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA135 + difference 2 4) (sourceB135 + difference 4 2) sourceC135) = raw4661 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4661; decide +kernel
    rw [ha]
    exact (canonical4661 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA135 + difference 2 5) (sourceB135 + difference 5 2) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA135 + difference 2 5) (sourceB135 + difference 5 2) sourceC135) = raw4662 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4662; decide +kernel
    rw [ha]
    exact (canonical4662 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA135 + difference 3 0) (sourceB135 + difference 0 3) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA135 + difference 3 0) (sourceB135 + difference 0 3) sourceC135) = raw4663 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4663; decide +kernel
    rw [ha]
    exact (canonical4663 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA135 + difference 3 1) (sourceB135 + difference 1 3) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA135 + difference 3 1) (sourceB135 + difference 1 3) sourceC135) = raw4664 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4664; decide +kernel
    rw [ha]
    exact (canonical4664 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA135 + difference 3 2) (sourceB135 + difference 2 3) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA135 + difference 3 2) (sourceB135 + difference 2 3) sourceC135) = raw4665 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4665; decide +kernel
    rw [ha]
    exact (canonical4665 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA135 + difference 3 4) (sourceB135 + difference 4 3) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA135 + difference 3 4) (sourceB135 + difference 4 3) sourceC135) = raw4666 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4666; decide +kernel
    rw [ha]
    exact (canonical4666 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA135 + difference 3 5) (sourceB135 + difference 5 3) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA135 + difference 3 5) (sourceB135 + difference 5 3) sourceC135) = raw4667 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4667; decide +kernel
    rw [ha]
    exact (canonical4667 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA135 + difference 4 0) (sourceB135 + difference 0 4) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA135 + difference 4 0) (sourceB135 + difference 0 4) sourceC135) = raw4668 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4668; decide +kernel
    rw [ha]
    exact (canonical4668 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA135 + difference 4 1) (sourceB135 + difference 1 4) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA135 + difference 4 1) (sourceB135 + difference 1 4) sourceC135) = raw4669 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4669; decide +kernel
    rw [ha]
    exact (canonical4669 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA135 + difference 4 2) (sourceB135 + difference 2 4) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA135 + difference 4 2) (sourceB135 + difference 2 4) sourceC135) = raw4670 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4670; decide +kernel
    rw [ha]
    exact (canonical4670 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA135 + difference 4 3) (sourceB135 + difference 3 4) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA135 + difference 4 3) (sourceB135 + difference 3 4) sourceC135) = raw4671 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4671; decide +kernel
    rw [ha]
    exact (canonical4671 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA135 + difference 4 5) (sourceB135 + difference 5 4) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA135 + difference 4 5) (sourceB135 + difference 5 4) sourceC135) = raw4672 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4672; decide +kernel
    rw [ha]
    exact (canonical4672 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA135 + difference 5 0) (sourceB135 + difference 0 5) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4445) := by
    have ha : (tripleCharges (sourceA135 + difference 5 0) (sourceB135 + difference 0 5) sourceC135) = raw4673 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4673; decide +kernel
    rw [ha]
    exact (canonical4673 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA135 + difference 5 1) (sourceB135 + difference 1 5) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA135 + difference 5 1) (sourceB135 + difference 1 5) sourceC135) = raw4674 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4674; decide +kernel
    rw [ha]
    exact (canonical4674 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA135 + difference 5 2) (sourceB135 + difference 2 5) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA135 + difference 5 2) (sourceB135 + difference 2 5) sourceC135) = raw4675 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4675; decide +kernel
    rw [ha]
    exact (canonical4675 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA135 + difference 5 3) (sourceB135 + difference 3 5) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA135 + difference 5 3) (sourceB135 + difference 3 5) sourceC135) = raw4676 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4676; decide +kernel
    rw [ha]
    exact (canonical4676 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA135 + difference 5 4) (sourceB135 + difference 4 5) sourceC135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA135 + difference 5 4) (sourceB135 + difference 4 5) sourceC135) = raw4677 := by
      apply Matrix.ext; unfold tripleCharges sourceA135 sourceB135 sourceC135 difference raw4677; decide +kernel
    rw [ha]
    exact (canonical4677 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA135 sourceB135 sourceC135
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm135, Integer.Sparse.eval]
  linarith only [hs]

def sourceA136 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB136 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC136 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm136 : Integer.Sparse Master := [(Sum.inr 1024, 2), (Sum.inr 1027, 1), (Sum.inr 1047, 2), (Sum.inr 1388, 2), (Sum.inr 1413, 2), (Sum.inr 2471, 2), (Sum.inr 2486, 4), (Sum.inr 2574, 4), (Sum.inr 2602, 2), (Sum.inr 2754, 2), (Sum.inr 2769, 2), (Sum.inr 3120, 1), (Sum.inr 3227, 2), (Sum.inr 3229, 2)]

theorem sourceEq136 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm136 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA136 + difference 0 1) (sourceB136 + difference 1 0) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA136 + difference 0 1) (sourceB136 + difference 1 0) sourceC136) = raw4678 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4678; decide +kernel
    rw [ha]
    exact (canonical4678 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA136 + difference 0 2) (sourceB136 + difference 2 0) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA136 + difference 0 2) (sourceB136 + difference 2 0) sourceC136) = raw4679 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4679; decide +kernel
    rw [ha]
    exact (canonical4679 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA136 + difference 0 3) (sourceB136 + difference 3 0) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA136 + difference 0 3) (sourceB136 + difference 3 0) sourceC136) = raw4680 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4680; decide +kernel
    rw [ha]
    exact (canonical4680 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA136 + difference 0 4) (sourceB136 + difference 4 0) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA136 + difference 0 4) (sourceB136 + difference 4 0) sourceC136) = raw4681 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4681; decide +kernel
    rw [ha]
    exact (canonical4681 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA136 + difference 0 5) (sourceB136 + difference 5 0) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA136 + difference 0 5) (sourceB136 + difference 5 0) sourceC136) = raw4682 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4682; decide +kernel
    rw [ha]
    exact (canonical4682 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA136 + difference 1 0) (sourceB136 + difference 0 1) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA136 + difference 1 0) (sourceB136 + difference 0 1) sourceC136) = raw4683 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4683; decide +kernel
    rw [ha]
    exact (canonical4683 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA136 + difference 1 2) (sourceB136 + difference 2 1) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA136 + difference 1 2) (sourceB136 + difference 2 1) sourceC136) = raw4684 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4684; decide +kernel
    rw [ha]
    exact (canonical4684 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA136 + difference 1 3) (sourceB136 + difference 3 1) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA136 + difference 1 3) (sourceB136 + difference 3 1) sourceC136) = raw4685 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4685; decide +kernel
    rw [ha]
    exact (canonical4685 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA136 + difference 1 4) (sourceB136 + difference 4 1) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA136 + difference 1 4) (sourceB136 + difference 4 1) sourceC136) = raw4686 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4686; decide +kernel
    rw [ha]
    exact (canonical4686 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA136 + difference 1 5) (sourceB136 + difference 5 1) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA136 + difference 1 5) (sourceB136 + difference 5 1) sourceC136) = raw4687 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4687; decide +kernel
    rw [ha]
    exact (canonical4687 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA136 + difference 2 0) (sourceB136 + difference 0 2) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA136 + difference 2 0) (sourceB136 + difference 0 2) sourceC136) = raw4688 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4688; decide +kernel
    rw [ha]
    exact (canonical4688 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA136 + difference 2 1) (sourceB136 + difference 1 2) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA136 + difference 2 1) (sourceB136 + difference 1 2) sourceC136) = raw4689 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4689; decide +kernel
    rw [ha]
    exact (canonical4689 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA136 + difference 2 3) (sourceB136 + difference 3 2) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA136 + difference 2 3) (sourceB136 + difference 3 2) sourceC136) = raw4690 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4690; decide +kernel
    rw [ha]
    exact (canonical4690 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA136 + difference 2 4) (sourceB136 + difference 4 2) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA136 + difference 2 4) (sourceB136 + difference 4 2) sourceC136) = raw4691 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4691; decide +kernel
    rw [ha]
    exact (canonical4691 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA136 + difference 2 5) (sourceB136 + difference 5 2) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA136 + difference 2 5) (sourceB136 + difference 5 2) sourceC136) = raw4692 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4692; decide +kernel
    rw [ha]
    exact (canonical4692 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA136 + difference 3 0) (sourceB136 + difference 0 3) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA136 + difference 3 0) (sourceB136 + difference 0 3) sourceC136) = raw4693 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4693; decide +kernel
    rw [ha]
    exact (canonical4693 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA136 + difference 3 1) (sourceB136 + difference 1 3) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA136 + difference 3 1) (sourceB136 + difference 1 3) sourceC136) = raw4694 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4694; decide +kernel
    rw [ha]
    exact (canonical4694 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA136 + difference 3 2) (sourceB136 + difference 2 3) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA136 + difference 3 2) (sourceB136 + difference 2 3) sourceC136) = raw4695 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4695; decide +kernel
    rw [ha]
    exact (canonical4695 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA136 + difference 3 4) (sourceB136 + difference 4 3) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2602) := by
    have ha : (tripleCharges (sourceA136 + difference 3 4) (sourceB136 + difference 4 3) sourceC136) = raw4696 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4696; decide +kernel
    rw [ha]
    exact (canonical4696 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA136 + difference 3 5) (sourceB136 + difference 5 3) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA136 + difference 3 5) (sourceB136 + difference 5 3) sourceC136) = raw4697 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4697; decide +kernel
    rw [ha]
    exact (canonical4697 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA136 + difference 4 0) (sourceB136 + difference 0 4) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA136 + difference 4 0) (sourceB136 + difference 0 4) sourceC136) = raw4698 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4698; decide +kernel
    rw [ha]
    exact (canonical4698 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA136 + difference 4 1) (sourceB136 + difference 1 4) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA136 + difference 4 1) (sourceB136 + difference 1 4) sourceC136) = raw4699 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4699; decide +kernel
    rw [ha]
    exact (canonical4699 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA136 + difference 4 2) (sourceB136 + difference 2 4) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA136 + difference 4 2) (sourceB136 + difference 2 4) sourceC136) = raw4700 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4700; decide +kernel
    rw [ha]
    exact (canonical4700 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA136 + difference 4 3) (sourceB136 + difference 3 4) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2602) := by
    have ha : (tripleCharges (sourceA136 + difference 4 3) (sourceB136 + difference 3 4) sourceC136) = raw4701 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4701; decide +kernel
    rw [ha]
    exact (canonical4701 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA136 + difference 4 5) (sourceB136 + difference 5 4) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA136 + difference 4 5) (sourceB136 + difference 5 4) sourceC136) = raw4702 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4702; decide +kernel
    rw [ha]
    exact (canonical4702 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA136 + difference 5 0) (sourceB136 + difference 0 5) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1027) := by
    have ha : (tripleCharges (sourceA136 + difference 5 0) (sourceB136 + difference 0 5) sourceC136) = raw4703 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4703; decide +kernel
    rw [ha]
    exact (canonical4703 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA136 + difference 5 1) (sourceB136 + difference 1 5) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA136 + difference 5 1) (sourceB136 + difference 1 5) sourceC136) = raw4704 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4704; decide +kernel
    rw [ha]
    exact (canonical4704 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA136 + difference 5 2) (sourceB136 + difference 2 5) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA136 + difference 5 2) (sourceB136 + difference 2 5) sourceC136) = raw4705 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4705; decide +kernel
    rw [ha]
    exact (canonical4705 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA136 + difference 5 3) (sourceB136 + difference 3 5) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1413) := by
    have ha : (tripleCharges (sourceA136 + difference 5 3) (sourceB136 + difference 3 5) sourceC136) = raw4706 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4706; decide +kernel
    rw [ha]
    exact (canonical4706 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA136 + difference 5 4) (sourceB136 + difference 4 5) sourceC136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1413) := by
    have ha : (tripleCharges (sourceA136 + difference 5 4) (sourceB136 + difference 4 5) sourceC136) = raw4707 := by
      apply Matrix.ext; unfold tripleCharges sourceA136 sourceB136 sourceC136 difference raw4707; decide +kernel
    rw [ha]
    exact (canonical4707 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA136 sourceB136 sourceC136
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm136, Integer.Sparse.eval]
  linarith only [hs]

def sourceA137 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB137 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC137 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm137 : Integer.Sparse Master := [(Sum.inr 1723, 2), (Sum.inr 1744, 2), (Sum.inr 1745, 2), (Sum.inr 1749, 1), (Sum.inr 1750, 2), (Sum.inr 2201, 2), (Sum.inr 2224, 4), (Sum.inr 2259, 4), (Sum.inr 2262, 2), (Sum.inr 2287, 2), (Sum.inr 2291, 2), (Sum.inr 2738, 2), (Sum.inr 2781, 2), (Sum.inr 2784, 1)]

theorem sourceEq137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm137 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA137 + difference 0 1) (sourceB137 + difference 1 0) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA137 + difference 0 1) (sourceB137 + difference 1 0) sourceC137) = raw4708 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4708; decide +kernel
    rw [ha]
    exact (canonical4708 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA137 + difference 0 2) (sourceB137 + difference 2 0) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA137 + difference 0 2) (sourceB137 + difference 2 0) sourceC137) = raw4709 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4709; decide +kernel
    rw [ha]
    exact (canonical4709 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA137 + difference 0 3) (sourceB137 + difference 3 0) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA137 + difference 0 3) (sourceB137 + difference 3 0) sourceC137) = raw4710 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4710; decide +kernel
    rw [ha]
    exact (canonical4710 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA137 + difference 0 4) (sourceB137 + difference 4 0) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA137 + difference 0 4) (sourceB137 + difference 4 0) sourceC137) = raw4711 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4711; decide +kernel
    rw [ha]
    exact (canonical4711 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA137 + difference 0 5) (sourceB137 + difference 5 0) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA137 + difference 0 5) (sourceB137 + difference 5 0) sourceC137) = raw4712 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4712; decide +kernel
    rw [ha]
    exact (canonical4712 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA137 + difference 1 0) (sourceB137 + difference 0 1) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA137 + difference 1 0) (sourceB137 + difference 0 1) sourceC137) = raw4713 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4713; decide +kernel
    rw [ha]
    exact (canonical4713 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA137 + difference 1 2) (sourceB137 + difference 2 1) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA137 + difference 1 2) (sourceB137 + difference 2 1) sourceC137) = raw4714 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4714; decide +kernel
    rw [ha]
    exact (canonical4714 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA137 + difference 1 3) (sourceB137 + difference 3 1) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA137 + difference 1 3) (sourceB137 + difference 3 1) sourceC137) = raw4715 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4715; decide +kernel
    rw [ha]
    exact (canonical4715 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA137 + difference 1 4) (sourceB137 + difference 4 1) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA137 + difference 1 4) (sourceB137 + difference 4 1) sourceC137) = raw4716 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4716; decide +kernel
    rw [ha]
    exact (canonical4716 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA137 + difference 1 5) (sourceB137 + difference 5 1) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA137 + difference 1 5) (sourceB137 + difference 5 1) sourceC137) = raw4717 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4717; decide +kernel
    rw [ha]
    exact (canonical4717 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA137 + difference 2 0) (sourceB137 + difference 0 2) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA137 + difference 2 0) (sourceB137 + difference 0 2) sourceC137) = raw4718 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4718; decide +kernel
    rw [ha]
    exact (canonical4718 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA137 + difference 2 1) (sourceB137 + difference 1 2) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA137 + difference 2 1) (sourceB137 + difference 1 2) sourceC137) = raw4719 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4719; decide +kernel
    rw [ha]
    exact (canonical4719 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA137 + difference 2 3) (sourceB137 + difference 3 2) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA137 + difference 2 3) (sourceB137 + difference 3 2) sourceC137) = raw4720 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4720; decide +kernel
    rw [ha]
    exact (canonical4720 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA137 + difference 2 4) (sourceB137 + difference 4 2) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA137 + difference 2 4) (sourceB137 + difference 4 2) sourceC137) = raw4721 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4721; decide +kernel
    rw [ha]
    exact (canonical4721 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA137 + difference 2 5) (sourceB137 + difference 5 2) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA137 + difference 2 5) (sourceB137 + difference 5 2) sourceC137) = raw4722 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4722; decide +kernel
    rw [ha]
    exact (canonical4722 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA137 + difference 3 0) (sourceB137 + difference 0 3) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA137 + difference 3 0) (sourceB137 + difference 0 3) sourceC137) = raw4723 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4723; decide +kernel
    rw [ha]
    exact (canonical4723 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA137 + difference 3 1) (sourceB137 + difference 1 3) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA137 + difference 3 1) (sourceB137 + difference 1 3) sourceC137) = raw4724 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4724; decide +kernel
    rw [ha]
    exact (canonical4724 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA137 + difference 3 2) (sourceB137 + difference 2 3) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA137 + difference 3 2) (sourceB137 + difference 2 3) sourceC137) = raw4725 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4725; decide +kernel
    rw [ha]
    exact (canonical4725 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA137 + difference 3 4) (sourceB137 + difference 4 3) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA137 + difference 3 4) (sourceB137 + difference 4 3) sourceC137) = raw4726 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4726; decide +kernel
    rw [ha]
    exact (canonical4726 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA137 + difference 3 5) (sourceB137 + difference 5 3) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA137 + difference 3 5) (sourceB137 + difference 5 3) sourceC137) = raw4727 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4727; decide +kernel
    rw [ha]
    exact (canonical4727 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA137 + difference 4 0) (sourceB137 + difference 0 4) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA137 + difference 4 0) (sourceB137 + difference 0 4) sourceC137) = raw4728 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4728; decide +kernel
    rw [ha]
    exact (canonical4728 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA137 + difference 4 1) (sourceB137 + difference 1 4) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA137 + difference 4 1) (sourceB137 + difference 1 4) sourceC137) = raw4729 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4729; decide +kernel
    rw [ha]
    exact (canonical4729 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA137 + difference 4 2) (sourceB137 + difference 2 4) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA137 + difference 4 2) (sourceB137 + difference 2 4) sourceC137) = raw4730 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4730; decide +kernel
    rw [ha]
    exact (canonical4730 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA137 + difference 4 3) (sourceB137 + difference 3 4) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA137 + difference 4 3) (sourceB137 + difference 3 4) sourceC137) = raw4731 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4731; decide +kernel
    rw [ha]
    exact (canonical4731 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA137 + difference 4 5) (sourceB137 + difference 5 4) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA137 + difference 4 5) (sourceB137 + difference 5 4) sourceC137) = raw4732 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4732; decide +kernel
    rw [ha]
    exact (canonical4732 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA137 + difference 5 0) (sourceB137 + difference 0 5) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1749) := by
    have ha : (tripleCharges (sourceA137 + difference 5 0) (sourceB137 + difference 0 5) sourceC137) = raw4733 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4733; decide +kernel
    rw [ha]
    exact (canonical4733 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA137 + difference 5 1) (sourceB137 + difference 1 5) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA137 + difference 5 1) (sourceB137 + difference 1 5) sourceC137) = raw4734 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4734; decide +kernel
    rw [ha]
    exact (canonical4734 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA137 + difference 5 2) (sourceB137 + difference 2 5) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA137 + difference 5 2) (sourceB137 + difference 2 5) sourceC137) = raw4735 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4735; decide +kernel
    rw [ha]
    exact (canonical4735 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA137 + difference 5 3) (sourceB137 + difference 3 5) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA137 + difference 5 3) (sourceB137 + difference 3 5) sourceC137) = raw4736 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4736; decide +kernel
    rw [ha]
    exact (canonical4736 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA137 + difference 5 4) (sourceB137 + difference 4 5) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA137 + difference 5 4) (sourceB137 + difference 4 5) sourceC137) = raw4737 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4737; decide +kernel
    rw [ha]
    exact (canonical4737 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA137 sourceB137 sourceC137
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm137, Integer.Sparse.eval]
  linarith only [hs]

def sourceA138 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB138 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC138 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm138 : Integer.Sparse Master := [(Sum.inr 2244, 2), (Sum.inr 2247, 1), (Sum.inr 2265, 2), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

theorem sourceEq138 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm138 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA138 + difference 0 0) (sourceB138 + difference 0 0) sourceC138) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA138 + difference 0 0) (sourceB138 + difference 0 0) sourceC138) = raw4738 := by
      apply Matrix.ext; unfold tripleCharges sourceA138 sourceB138 sourceC138 difference raw4738; decide +kernel
    rw [ha]
    exact (canonical4738 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA138 + difference 0 1) (sourceB138 + difference 1 0) sourceC138) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA138 + difference 0 1) (sourceB138 + difference 1 0) sourceC138) = raw4739 := by
      apply Matrix.ext; unfold tripleCharges sourceA138 sourceB138 sourceC138 difference raw4739; decide +kernel
    rw [ha]
    exact (canonical4739 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA138 + difference 0 2) (sourceB138 + difference 2 0) sourceC138) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA138 + difference 0 2) (sourceB138 + difference 2 0) sourceC138) = raw4740 := by
      apply Matrix.ext; unfold tripleCharges sourceA138 sourceB138 sourceC138 difference raw4740; decide +kernel
    rw [ha]
    exact (canonical4740 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA138 + difference 0 3) (sourceB138 + difference 3 0) sourceC138) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA138 + difference 0 3) (sourceB138 + difference 3 0) sourceC138) = raw4741 := by
      apply Matrix.ext; unfold tripleCharges sourceA138 sourceB138 sourceC138 difference raw4741; decide +kernel
    rw [ha]
    exact (canonical4741 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA138 + difference 0 4) (sourceB138 + difference 4 0) sourceC138) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA138 + difference 0 4) (sourceB138 + difference 4 0) sourceC138) = raw4742 := by
      apply Matrix.ext; unfold tripleCharges sourceA138 sourceB138 sourceC138 difference raw4742; decide +kernel
    rw [ha]
    exact (canonical4742 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA138 + difference 0 5) (sourceB138 + difference 5 0) sourceC138) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3623) := by
    have ha : (tripleCharges (sourceA138 + difference 0 5) (sourceB138 + difference 5 0) sourceC138) = raw4743 := by
      apply Matrix.ext; unfold tripleCharges sourceA138 sourceB138 sourceC138 difference raw4743; decide +kernel
    rw [ha]
    exact (canonical4743 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA138 + sourceB138) sourceC138) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA138 + sourceB138) sourceC138) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA138 sourceB138 sourceC138 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA138 sourceB138 sourceC138
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm138, Integer.Sparse.eval]
  linarith only [hs]

def sourceA139 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB139 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC139 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm139 : Integer.Sparse Master := [(Sum.inr 1027, 1), (Sum.inr 1385, 2), (Sum.inr 1408, 2), (Sum.inr 2247, 1), (Sum.inr 4083, -1)]

theorem sourceEq139 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm139 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA139 + difference 0 0) (sourceB139 + difference 0 0) sourceC139) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA139 + difference 0 0) (sourceB139 + difference 0 0) sourceC139) = raw4738 := by
      apply Matrix.ext; unfold tripleCharges sourceA139 sourceB139 sourceC139 difference raw4738; decide +kernel
    rw [ha]
    exact (canonical4738 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA139 + difference 1 0) (sourceB139 + difference 0 1) sourceC139) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1385) := by
    have ha : (tripleCharges (sourceA139 + difference 1 0) (sourceB139 + difference 0 1) sourceC139) = raw4745 := by
      apply Matrix.ext; unfold tripleCharges sourceA139 sourceB139 sourceC139 difference raw4745; decide +kernel
    rw [ha]
    exact (canonical4745 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA139 + difference 2 0) (sourceB139 + difference 0 2) sourceC139) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1385) := by
    have ha : (tripleCharges (sourceA139 + difference 2 0) (sourceB139 + difference 0 2) sourceC139) = raw4746 := by
      apply Matrix.ext; unfold tripleCharges sourceA139 sourceB139 sourceC139 difference raw4746; decide +kernel
    rw [ha]
    exact (canonical4746 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA139 + difference 3 0) (sourceB139 + difference 0 3) sourceC139) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA139 + difference 3 0) (sourceB139 + difference 0 3) sourceC139) = raw4747 := by
      apply Matrix.ext; unfold tripleCharges sourceA139 sourceB139 sourceC139 difference raw4747; decide +kernel
    rw [ha]
    exact (canonical4747 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA139 + difference 4 0) (sourceB139 + difference 0 4) sourceC139) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA139 + difference 4 0) (sourceB139 + difference 0 4) sourceC139) = raw4748 := by
      apply Matrix.ext; unfold tripleCharges sourceA139 sourceB139 sourceC139 difference raw4748; decide +kernel
    rw [ha]
    exact (canonical4748 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA139 + difference 5 0) (sourceB139 + difference 0 5) sourceC139) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1027) := by
    have ha : (tripleCharges (sourceA139 + difference 5 0) (sourceB139 + difference 0 5) sourceC139) = raw4749 := by
      apply Matrix.ext; unfold tripleCharges sourceA139 sourceB139 sourceC139 difference raw4749; decide +kernel
    rw [ha]
    exact (canonical4749 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA139 + sourceB139) sourceC139) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA139 + sourceB139) sourceC139) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA139 sourceB139 sourceC139 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA139 sourceB139 sourceC139
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm139, Integer.Sparse.eval]
  linarith only [hs]

def sourceA140 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB140 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC140 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm140 : Integer.Sparse Master := [(Sum.inr 1385, 1), (Sum.inr 2009, 1), (Sum.inr 2025, 2), (Sum.inr 2247, 1), (Sum.inr 3075, 1), (Sum.inr 4083, -1)]

theorem sourceEq140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm140 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA140 + difference 1 0) (sourceB140 + difference 0 1) sourceC140) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1385) := by
    have ha : (tripleCharges (sourceA140 + difference 1 0) (sourceB140 + difference 0 1) sourceC140) = raw4745 := by
      apply Matrix.ext; unfold tripleCharges sourceA140 sourceB140 sourceC140 difference raw4745; decide +kernel
    rw [ha]
    exact (canonical4745 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA140 + difference 1 1) (sourceB140 + difference 1 1) sourceC140) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA140 + difference 1 1) (sourceB140 + difference 1 1) sourceC140) = raw4738 := by
      apply Matrix.ext; unfold tripleCharges sourceA140 sourceB140 sourceC140 difference raw4738; decide +kernel
    rw [ha]
    exact (canonical4738 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA140 + difference 1 2) (sourceB140 + difference 2 1) sourceC140) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA140 + difference 1 2) (sourceB140 + difference 2 1) sourceC140) = raw4750 := by
      apply Matrix.ext; unfold tripleCharges sourceA140 sourceB140 sourceC140 difference raw4750; decide +kernel
    rw [ha]
    exact (canonical4750 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA140 + difference 1 3) (sourceB140 + difference 3 1) sourceC140) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA140 + difference 1 3) (sourceB140 + difference 3 1) sourceC140) = raw4751 := by
      apply Matrix.ext; unfold tripleCharges sourceA140 sourceB140 sourceC140 difference raw4751; decide +kernel
    rw [ha]
    exact (canonical4751 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA140 + difference 1 4) (sourceB140 + difference 4 1) sourceC140) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA140 + difference 1 4) (sourceB140 + difference 4 1) sourceC140) = raw4752 := by
      apply Matrix.ext; unfold tripleCharges sourceA140 sourceB140 sourceC140 difference raw4752; decide +kernel
    rw [ha]
    exact (canonical4752 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA140 + difference 1 5) (sourceB140 + difference 5 1) sourceC140) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA140 + difference 1 5) (sourceB140 + difference 5 1) sourceC140) = raw4753 := by
      apply Matrix.ext; unfold tripleCharges sourceA140 sourceB140 sourceC140 difference raw4753; decide +kernel
    rw [ha]
    exact (canonical4753 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA140 + sourceB140) sourceC140) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA140 + sourceB140) sourceC140) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA140 sourceB140 sourceC140 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA140 sourceB140 sourceC140
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm140, Integer.Sparse.eval]
  linarith only [hs]

def sourceA141 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB141 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC141 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm141 : Integer.Sparse Master := [(Sum.inr 1022, 1), (Sum.inr 2009, 1), (Sum.inr 2090, 2), (Sum.inr 2244, 1), (Sum.inr 2247, 1), (Sum.inr 4083, -1)]

theorem sourceEq141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm141 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA141 + difference 0 1) (sourceB141 + difference 1 0) sourceC141) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA141 + difference 0 1) (sourceB141 + difference 1 0) sourceC141) = raw4739 := by
      apply Matrix.ext; unfold tripleCharges sourceA141 sourceB141 sourceC141 difference raw4739; decide +kernel
    rw [ha]
    exact (canonical4739 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA141 + difference 1 1) (sourceB141 + difference 1 1) sourceC141) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA141 + difference 1 1) (sourceB141 + difference 1 1) sourceC141) = raw4738 := by
      apply Matrix.ext; unfold tripleCharges sourceA141 sourceB141 sourceC141 difference raw4738; decide +kernel
    rw [ha]
    exact (canonical4738 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA141 + difference 2 1) (sourceB141 + difference 1 2) sourceC141) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA141 + difference 2 1) (sourceB141 + difference 1 2) sourceC141) = raw4754 := by
      apply Matrix.ext; unfold tripleCharges sourceA141 sourceB141 sourceC141 difference raw4754; decide +kernel
    rw [ha]
    exact (canonical4754 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA141 + difference 3 1) (sourceB141 + difference 1 3) sourceC141) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA141 + difference 3 1) (sourceB141 + difference 1 3) sourceC141) = raw4755 := by
      apply Matrix.ext; unfold tripleCharges sourceA141 sourceB141 sourceC141 difference raw4755; decide +kernel
    rw [ha]
    exact (canonical4755 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA141 + difference 4 1) (sourceB141 + difference 1 4) sourceC141) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA141 + difference 4 1) (sourceB141 + difference 1 4) sourceC141) = raw4756 := by
      apply Matrix.ext; unfold tripleCharges sourceA141 sourceB141 sourceC141 difference raw4756; decide +kernel
    rw [ha]
    exact (canonical4756 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA141 + difference 5 1) (sourceB141 + difference 1 5) sourceC141) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA141 + difference 5 1) (sourceB141 + difference 1 5) sourceC141) = raw4757 := by
      apply Matrix.ext; unfold tripleCharges sourceA141 sourceB141 sourceC141 difference raw4757; decide +kernel
    rw [ha]
    exact (canonical4757 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA141 + sourceB141) sourceC141) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA141 + sourceB141) sourceC141) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA141 sourceB141 sourceC141 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA141 sourceB141 sourceC141
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm141, Integer.Sparse.eval]
  linarith only [hs]

def sourceA142 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB142 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC142 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm142 : Integer.Sparse Master := [(Sum.inr 1408, 1), (Sum.inr 2090, 2), (Sum.inr 2112, 1), (Sum.inr 2247, 1), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

theorem sourceEq142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm142 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA142 + difference 3 0) (sourceB142 + difference 0 3) sourceC142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA142 + difference 3 0) (sourceB142 + difference 0 3) sourceC142) = raw4747 := by
      apply Matrix.ext; unfold tripleCharges sourceA142 sourceB142 sourceC142 difference raw4747; decide +kernel
    rw [ha]
    exact (canonical4747 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA142 + difference 3 1) (sourceB142 + difference 1 3) sourceC142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA142 + difference 3 1) (sourceB142 + difference 1 3) sourceC142) = raw4755 := by
      apply Matrix.ext; unfold tripleCharges sourceA142 sourceB142 sourceC142 difference raw4755; decide +kernel
    rw [ha]
    exact (canonical4755 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA142 + difference 3 2) (sourceB142 + difference 2 3) sourceC142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA142 + difference 3 2) (sourceB142 + difference 2 3) sourceC142) = raw4758 := by
      apply Matrix.ext; unfold tripleCharges sourceA142 sourceB142 sourceC142 difference raw4758; decide +kernel
    rw [ha]
    exact (canonical4758 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA142 + difference 3 3) (sourceB142 + difference 3 3) sourceC142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA142 + difference 3 3) (sourceB142 + difference 3 3) sourceC142) = raw4738 := by
      apply Matrix.ext; unfold tripleCharges sourceA142 sourceB142 sourceC142 difference raw4738; decide +kernel
    rw [ha]
    exact (canonical4738 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA142 + difference 3 4) (sourceB142 + difference 4 3) sourceC142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA142 + difference 3 4) (sourceB142 + difference 4 3) sourceC142) = raw4759 := by
      apply Matrix.ext; unfold tripleCharges sourceA142 sourceB142 sourceC142 difference raw4759; decide +kernel
    rw [ha]
    exact (canonical4759 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA142 + difference 3 5) (sourceB142 + difference 5 3) sourceC142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA142 + difference 3 5) (sourceB142 + difference 5 3) sourceC142) = raw4760 := by
      apply Matrix.ext; unfold tripleCharges sourceA142 sourceB142 sourceC142 difference raw4760; decide +kernel
    rw [ha]
    exact (canonical4760 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA142 + sourceB142) sourceC142) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA142 + sourceB142) sourceC142) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA142 sourceB142 sourceC142 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA142 sourceB142 sourceC142
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm142, Integer.Sparse.eval]
  linarith only [hs]

def sourceA143 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB143 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC143 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm143 : Integer.Sparse Master := [(Sum.inr 1046, 1), (Sum.inr 2025, 2), (Sum.inr 2112, 1), (Sum.inr 2247, 1), (Sum.inr 2265, 1), (Sum.inr 4083, -1)]

theorem sourceEq143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm143 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA143 + difference 0 3) (sourceB143 + difference 3 0) sourceC143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA143 + difference 0 3) (sourceB143 + difference 3 0) sourceC143) = raw4741 := by
      apply Matrix.ext; unfold tripleCharges sourceA143 sourceB143 sourceC143 difference raw4741; decide +kernel
    rw [ha]
    exact (canonical4741 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA143 + difference 1 3) (sourceB143 + difference 3 1) sourceC143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA143 + difference 1 3) (sourceB143 + difference 3 1) sourceC143) = raw4751 := by
      apply Matrix.ext; unfold tripleCharges sourceA143 sourceB143 sourceC143 difference raw4751; decide +kernel
    rw [ha]
    exact (canonical4751 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA143 + difference 2 3) (sourceB143 + difference 3 2) sourceC143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA143 + difference 2 3) (sourceB143 + difference 3 2) sourceC143) = raw4761 := by
      apply Matrix.ext; unfold tripleCharges sourceA143 sourceB143 sourceC143 difference raw4761; decide +kernel
    rw [ha]
    exact (canonical4761 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA143 + difference 3 3) (sourceB143 + difference 3 3) sourceC143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA143 + difference 3 3) (sourceB143 + difference 3 3) sourceC143) = raw4738 := by
      apply Matrix.ext; unfold tripleCharges sourceA143 sourceB143 sourceC143 difference raw4738; decide +kernel
    rw [ha]
    exact (canonical4738 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA143 + difference 4 3) (sourceB143 + difference 3 4) sourceC143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA143 + difference 4 3) (sourceB143 + difference 3 4) sourceC143) = raw4762 := by
      apply Matrix.ext; unfold tripleCharges sourceA143 sourceB143 sourceC143 difference raw4762; decide +kernel
    rw [ha]
    exact (canonical4762 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA143 + difference 5 3) (sourceB143 + difference 3 5) sourceC143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA143 + difference 5 3) (sourceB143 + difference 3 5) sourceC143) = raw4763 := by
      apply Matrix.ext; unfold tripleCharges sourceA143 sourceB143 sourceC143 difference raw4763; decide +kernel
    rw [ha]
    exact (canonical4763 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA143 + sourceB143) sourceC143) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA143 + sourceB143) sourceC143) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA143 sourceB143 sourceC143 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA143 sourceB143 sourceC143
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm143, Integer.Sparse.eval]
  linarith only [hs]

def sourceA144 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB144 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC144 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceForm144 : Integer.Sparse Master := [(Sum.inr 1022, 2), (Sum.inr 1027, 1), (Sum.inr 1046, 2), (Sum.inr 2247, 1), (Sum.inr 4083, -1)]

theorem sourceEq144 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm144 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA144 + difference 5 0) (sourceB144 + difference 0 5) sourceC144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1027) := by
    have ha : (tripleCharges (sourceA144 + difference 5 0) (sourceB144 + difference 0 5) sourceC144) = raw4749 := by
      apply Matrix.ext; unfold tripleCharges sourceA144 sourceB144 sourceC144 difference raw4749; decide +kernel
    rw [ha]
    exact (canonical4749 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA144 + difference 5 1) (sourceB144 + difference 1 5) sourceC144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA144 + difference 5 1) (sourceB144 + difference 1 5) sourceC144) = raw4757 := by
      apply Matrix.ext; unfold tripleCharges sourceA144 sourceB144 sourceC144 difference raw4757; decide +kernel
    rw [ha]
    exact (canonical4757 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA144 + difference 5 2) (sourceB144 + difference 2 5) sourceC144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA144 + difference 5 2) (sourceB144 + difference 2 5) sourceC144) = raw4764 := by
      apply Matrix.ext; unfold tripleCharges sourceA144 sourceB144 sourceC144 difference raw4764; decide +kernel
    rw [ha]
    exact (canonical4764 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA144 + difference 5 3) (sourceB144 + difference 3 5) sourceC144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA144 + difference 5 3) (sourceB144 + difference 3 5) sourceC144) = raw4763 := by
      apply Matrix.ext; unfold tripleCharges sourceA144 sourceB144 sourceC144 difference raw4763; decide +kernel
    rw [ha]
    exact (canonical4763 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA144 + difference 5 4) (sourceB144 + difference 4 5) sourceC144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA144 + difference 5 4) (sourceB144 + difference 4 5) sourceC144) = raw4765 := by
      apply Matrix.ext; unfold tripleCharges sourceA144 sourceB144 sourceC144 difference raw4765; decide +kernel
    rw [ha]
    exact (canonical4765 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA144 + difference 5 5) (sourceB144 + difference 5 5) sourceC144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA144 + difference 5 5) (sourceB144 + difference 5 5) sourceC144) = raw4738 := by
      apply Matrix.ext; unfold tripleCharges sourceA144 sourceB144 sourceC144 difference raw4738; decide +kernel
    rw [ha]
    exact (canonical4738 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA144 + sourceB144) sourceC144) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA144 + sourceB144) sourceC144) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA144 sourceB144 sourceC144 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA144 sourceB144 sourceC144
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm144, Integer.Sparse.eval]
  linarith only [hs]

def sourceA145 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB145 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC145 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm145 : Integer.Sparse Master := [(Sum.inr 4494, 2), (Sum.inr 4496, 1), (Sum.inr 4500, 2), (Sum.inr 4830, 2), (Sum.inr 4832, 2), (Sum.inr 4836, 4), (Sum.inr 4886, 2), (Sum.inr 4890, 5), (Sum.inr 4892, 2), (Sum.inr 4897, 2), (Sum.inr 4899, 2), (Sum.inr 5252, 2), (Sum.inr 5296, 2)]

theorem sourceEq145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm145 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA145 + difference 0 1) (sourceB145 + difference 1 0) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA145 + difference 0 1) (sourceB145 + difference 1 0) sourceC145) = raw4234 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4234; decide +kernel
    rw [ha]
    exact (canonical4234 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA145 + difference 0 2) (sourceB145 + difference 2 0) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA145 + difference 0 2) (sourceB145 + difference 2 0) sourceC145) = raw4766 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4766; decide +kernel
    rw [ha]
    exact (canonical4766 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA145 + difference 0 3) (sourceB145 + difference 3 0) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA145 + difference 0 3) (sourceB145 + difference 3 0) sourceC145) = raw4345 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4345; decide +kernel
    rw [ha]
    exact (canonical4345 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA145 + difference 0 4) (sourceB145 + difference 4 0) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA145 + difference 0 4) (sourceB145 + difference 4 0) sourceC145) = raw4767 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4767; decide +kernel
    rw [ha]
    exact (canonical4767 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA145 + difference 0 5) (sourceB145 + difference 5 0) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA145 + difference 0 5) (sourceB145 + difference 5 0) sourceC145) = raw4768 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4768; decide +kernel
    rw [ha]
    exact (canonical4768 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA145 + difference 1 0) (sourceB145 + difference 0 1) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4886) := by
    have ha : (tripleCharges (sourceA145 + difference 1 0) (sourceB145 + difference 0 1) sourceC145) = raw3663 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw3663; decide +kernel
    rw [ha]
    exact (canonical3663 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA145 + difference 1 2) (sourceB145 + difference 2 1) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4830) := by
    have ha : (tripleCharges (sourceA145 + difference 1 2) (sourceB145 + difference 2 1) sourceC145) = raw4769 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4769; decide +kernel
    rw [ha]
    exact (canonical4769 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA145 + difference 1 3) (sourceB145 + difference 3 1) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA145 + difference 1 3) (sourceB145 + difference 3 1) sourceC145) = raw4350 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4350; decide +kernel
    rw [ha]
    exact (canonical4350 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA145 + difference 1 4) (sourceB145 + difference 4 1) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA145 + difference 1 4) (sourceB145 + difference 4 1) sourceC145) = raw4770 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4770; decide +kernel
    rw [ha]
    exact (canonical4770 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA145 + difference 1 5) (sourceB145 + difference 5 1) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4494) := by
    have ha : (tripleCharges (sourceA145 + difference 1 5) (sourceB145 + difference 5 1) sourceC145) = raw4771 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4771; decide +kernel
    rw [ha]
    exact (canonical4771 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA145 + difference 2 0) (sourceB145 + difference 0 2) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4886) := by
    have ha : (tripleCharges (sourceA145 + difference 2 0) (sourceB145 + difference 0 2) sourceC145) = raw3668 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw3668; decide +kernel
    rw [ha]
    exact (canonical3668 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA145 + difference 2 1) (sourceB145 + difference 1 2) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4830) := by
    have ha : (tripleCharges (sourceA145 + difference 2 1) (sourceB145 + difference 1 2) sourceC145) = raw3856 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw3856; decide +kernel
    rw [ha]
    exact (canonical3856 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA145 + difference 2 3) (sourceB145 + difference 3 2) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA145 + difference 2 3) (sourceB145 + difference 3 2) sourceC145) = raw3857 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw3857; decide +kernel
    rw [ha]
    exact (canonical3857 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA145 + difference 2 4) (sourceB145 + difference 4 2) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA145 + difference 2 4) (sourceB145 + difference 4 2) sourceC145) = raw3858 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw3858; decide +kernel
    rw [ha]
    exact (canonical3858 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA145 + difference 2 5) (sourceB145 + difference 5 2) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4494) := by
    have ha : (tripleCharges (sourceA145 + difference 2 5) (sourceB145 + difference 5 2) sourceC145) = raw3859 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw3859; decide +kernel
    rw [ha]
    exact (canonical3859 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA145 + difference 3 0) (sourceB145 + difference 0 3) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA145 + difference 3 0) (sourceB145 + difference 0 3) sourceC145) = raw3673 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw3673; decide +kernel
    rw [ha]
    exact (canonical3673 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA145 + difference 3 1) (sourceB145 + difference 1 3) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA145 + difference 3 1) (sourceB145 + difference 1 3) sourceC145) = raw4243 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4243; decide +kernel
    rw [ha]
    exact (canonical4243 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA145 + difference 3 2) (sourceB145 + difference 2 3) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA145 + difference 3 2) (sourceB145 + difference 2 3) sourceC145) = raw4772 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4772; decide +kernel
    rw [ha]
    exact (canonical4772 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA145 + difference 3 4) (sourceB145 + difference 4 3) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA145 + difference 3 4) (sourceB145 + difference 4 3) sourceC145) = raw4773 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4773; decide +kernel
    rw [ha]
    exact (canonical4773 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA145 + difference 3 5) (sourceB145 + difference 5 3) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA145 + difference 3 5) (sourceB145 + difference 5 3) sourceC145) = raw4774 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4774; decide +kernel
    rw [ha]
    exact (canonical4774 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA145 + difference 4 0) (sourceB145 + difference 0 4) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA145 + difference 4 0) (sourceB145 + difference 0 4) sourceC145) = raw3873 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw3873; decide +kernel
    rw [ha]
    exact (canonical3873 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA145 + difference 4 1) (sourceB145 + difference 1 4) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA145 + difference 4 1) (sourceB145 + difference 1 4) sourceC145) = raw3655 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw3655; decide +kernel
    rw [ha]
    exact (canonical3655 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA145 + difference 4 2) (sourceB145 + difference 2 4) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA145 + difference 4 2) (sourceB145 + difference 2 4) sourceC145) = raw3656 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw3656; decide +kernel
    rw [ha]
    exact (canonical3656 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA145 + difference 4 3) (sourceB145 + difference 3 4) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA145 + difference 4 3) (sourceB145 + difference 3 4) sourceC145) = raw3657 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw3657; decide +kernel
    rw [ha]
    exact (canonical3657 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA145 + difference 4 5) (sourceB145 + difference 5 4) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA145 + difference 4 5) (sourceB145 + difference 5 4) sourceC145) = raw3659 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw3659; decide +kernel
    rw [ha]
    exact (canonical3659 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA145 + difference 5 0) (sourceB145 + difference 0 5) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA145 + difference 5 0) (sourceB145 + difference 0 5) sourceC145) = raw3684 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw3684; decide +kernel
    rw [ha]
    exact (canonical3684 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA145 + difference 5 1) (sourceB145 + difference 1 5) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA145 + difference 5 1) (sourceB145 + difference 1 5) sourceC145) = raw4048 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4048; decide +kernel
    rw [ha]
    exact (canonical4048 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA145 + difference 5 2) (sourceB145 + difference 2 5) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA145 + difference 5 2) (sourceB145 + difference 2 5) sourceC145) = raw4235 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4235; decide +kernel
    rw [ha]
    exact (canonical4235 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA145 + difference 5 3) (sourceB145 + difference 3 5) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA145 + difference 5 3) (sourceB145 + difference 3 5) sourceC145) = raw4040 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4040; decide +kernel
    rw [ha]
    exact (canonical4040 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA145 + difference 5 4) (sourceB145 + difference 4 5) sourceC145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA145 + difference 5 4) (sourceB145 + difference 4 5) sourceC145) = raw4236 := by
      apply Matrix.ext; unfold tripleCharges sourceA145 sourceB145 sourceC145 difference raw4236; decide +kernel
    rw [ha]
    exact (canonical4236 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA145 sourceB145 sourceC145
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm145, Integer.Sparse.eval]
  linarith only [hs]

def sourceA146 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB146 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC146 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm146 : Integer.Sparse Master := [(Sum.inr 1435, 2), (Sum.inr 1436, 2), (Sum.inr 1451, 1), (Sum.inr 2235, 2), (Sum.inr 2247, 1), (Sum.inr 2255, 2), (Sum.inr 2707, 2), (Sum.inr 2712, 2), (Sum.inr 2716, 4), (Sum.inr 2755, 4), (Sum.inr 2770, 2), (Sum.inr 2778, 2), (Sum.inr 3082, 2), (Sum.inr 3114, 2)]

theorem sourceEq146 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm146 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA146 + difference 0 1) (sourceB146 + difference 1 0) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3082) := by
    have ha : (tripleCharges (sourceA146 + difference 0 1) (sourceB146 + difference 1 0) sourceC146) = raw4252 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4252; decide +kernel
    rw [ha]
    exact (canonical4252 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA146 + difference 0 2) (sourceB146 + difference 2 0) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3082) := by
    have ha : (tripleCharges (sourceA146 + difference 0 2) (sourceB146 + difference 2 0) sourceC146) = raw4775 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4775; decide +kernel
    rw [ha]
    exact (canonical4775 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA146 + difference 0 3) (sourceB146 + difference 3 0) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA146 + difference 0 3) (sourceB146 + difference 3 0) sourceC146) = raw4360 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4360; decide +kernel
    rw [ha]
    exact (canonical4360 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA146 + difference 0 4) (sourceB146 + difference 4 0) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA146 + difference 0 4) (sourceB146 + difference 4 0) sourceC146) = raw4776 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4776; decide +kernel
    rw [ha]
    exact (canonical4776 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA146 + difference 0 5) (sourceB146 + difference 5 0) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1451) := by
    have ha : (tripleCharges (sourceA146 + difference 0 5) (sourceB146 + difference 5 0) sourceC146) = raw4777 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4777; decide +kernel
    rw [ha]
    exact (canonical4777 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA146 + difference 1 0) (sourceB146 + difference 0 1) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA146 + difference 1 0) (sourceB146 + difference 0 1) sourceC146) = raw3693 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw3693; decide +kernel
    rw [ha]
    exact (canonical3693 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA146 + difference 1 2) (sourceB146 + difference 2 1) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2707) := by
    have ha : (tripleCharges (sourceA146 + difference 1 2) (sourceB146 + difference 2 1) sourceC146) = raw4778 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4778; decide +kernel
    rw [ha]
    exact (canonical4778 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA146 + difference 1 3) (sourceB146 + difference 3 1) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA146 + difference 1 3) (sourceB146 + difference 3 1) sourceC146) = raw4365 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4365; decide +kernel
    rw [ha]
    exact (canonical4365 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA146 + difference 1 4) (sourceB146 + difference 4 1) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA146 + difference 1 4) (sourceB146 + difference 4 1) sourceC146) = raw4779 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4779; decide +kernel
    rw [ha]
    exact (canonical4779 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA146 + difference 1 5) (sourceB146 + difference 5 1) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1435) := by
    have ha : (tripleCharges (sourceA146 + difference 1 5) (sourceB146 + difference 5 1) sourceC146) = raw4780 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4780; decide +kernel
    rw [ha]
    exact (canonical4780 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA146 + difference 2 0) (sourceB146 + difference 0 2) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA146 + difference 2 0) (sourceB146 + difference 0 2) sourceC146) = raw3698 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw3698; decide +kernel
    rw [ha]
    exact (canonical3698 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA146 + difference 2 1) (sourceB146 + difference 1 2) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2707) := by
    have ha : (tripleCharges (sourceA146 + difference 2 1) (sourceB146 + difference 1 2) sourceC146) = raw3878 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw3878; decide +kernel
    rw [ha]
    exact (canonical3878 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA146 + difference 2 3) (sourceB146 + difference 3 2) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA146 + difference 2 3) (sourceB146 + difference 3 2) sourceC146) = raw3879 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw3879; decide +kernel
    rw [ha]
    exact (canonical3879 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA146 + difference 2 4) (sourceB146 + difference 4 2) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA146 + difference 2 4) (sourceB146 + difference 4 2) sourceC146) = raw3880 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw3880; decide +kernel
    rw [ha]
    exact (canonical3880 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA146 + difference 2 5) (sourceB146 + difference 5 2) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1435) := by
    have ha : (tripleCharges (sourceA146 + difference 2 5) (sourceB146 + difference 5 2) sourceC146) = raw3881 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw3881; decide +kernel
    rw [ha]
    exact (canonical3881 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA146 + difference 3 0) (sourceB146 + difference 0 3) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA146 + difference 3 0) (sourceB146 + difference 0 3) sourceC146) = raw3703 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw3703; decide +kernel
    rw [ha]
    exact (canonical3703 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA146 + difference 3 1) (sourceB146 + difference 1 3) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA146 + difference 3 1) (sourceB146 + difference 1 3) sourceC146) = raw4261 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4261; decide +kernel
    rw [ha]
    exact (canonical4261 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA146 + difference 3 2) (sourceB146 + difference 2 3) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA146 + difference 3 2) (sourceB146 + difference 2 3) sourceC146) = raw4781 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4781; decide +kernel
    rw [ha]
    exact (canonical4781 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA146 + difference 3 4) (sourceB146 + difference 4 3) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2778) := by
    have ha : (tripleCharges (sourceA146 + difference 3 4) (sourceB146 + difference 4 3) sourceC146) = raw4782 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4782; decide +kernel
    rw [ha]
    exact (canonical4782 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA146 + difference 3 5) (sourceB146 + difference 5 3) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA146 + difference 3 5) (sourceB146 + difference 5 3) sourceC146) = raw4783 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4783; decide +kernel
    rw [ha]
    exact (canonical4783 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA146 + difference 4 0) (sourceB146 + difference 0 4) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA146 + difference 4 0) (sourceB146 + difference 0 4) sourceC146) = raw3895 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw3895; decide +kernel
    rw [ha]
    exact (canonical3895 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA146 + difference 4 1) (sourceB146 + difference 1 4) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA146 + difference 4 1) (sourceB146 + difference 1 4) sourceC146) = raw3685 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw3685; decide +kernel
    rw [ha]
    exact (canonical3685 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA146 + difference 4 2) (sourceB146 + difference 2 4) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA146 + difference 4 2) (sourceB146 + difference 2 4) sourceC146) = raw3686 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw3686; decide +kernel
    rw [ha]
    exact (canonical3686 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA146 + difference 4 3) (sourceB146 + difference 3 4) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2778) := by
    have ha : (tripleCharges (sourceA146 + difference 4 3) (sourceB146 + difference 3 4) sourceC146) = raw3687 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw3687; decide +kernel
    rw [ha]
    exact (canonical3687 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA146 + difference 4 5) (sourceB146 + difference 5 4) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA146 + difference 4 5) (sourceB146 + difference 5 4) sourceC146) = raw3689 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw3689; decide +kernel
    rw [ha]
    exact (canonical3689 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA146 + difference 5 0) (sourceB146 + difference 0 5) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA146 + difference 5 0) (sourceB146 + difference 0 5) sourceC146) = raw3714 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw3714; decide +kernel
    rw [ha]
    exact (canonical3714 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA146 + difference 5 1) (sourceB146 + difference 1 5) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA146 + difference 5 1) (sourceB146 + difference 1 5) sourceC146) = raw4074 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4074; decide +kernel
    rw [ha]
    exact (canonical4074 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA146 + difference 5 2) (sourceB146 + difference 2 5) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA146 + difference 5 2) (sourceB146 + difference 2 5) sourceC146) = raw4253 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4253; decide +kernel
    rw [ha]
    exact (canonical4253 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA146 + difference 5 3) (sourceB146 + difference 3 5) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA146 + difference 5 3) (sourceB146 + difference 3 5) sourceC146) = raw4066 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4066; decide +kernel
    rw [ha]
    exact (canonical4066 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA146 + difference 5 4) (sourceB146 + difference 4 5) sourceC146) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA146 + difference 5 4) (sourceB146 + difference 4 5) sourceC146) = raw4254 := by
      apply Matrix.ext; unfold tripleCharges sourceA146 sourceB146 sourceC146 difference raw4254; decide +kernel
    rw [ha]
    exact (canonical4254 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA146 sourceB146 sourceC146
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm146, Integer.Sparse.eval]
  linarith only [hs]

def sourceA147 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB147 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC147 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm147 : Integer.Sparse Master := [(Sum.inr 1700, 2), (Sum.inr 1710, 1), (Sum.inr 1716, 2), (Sum.inr 2187, 2), (Sum.inr 2193, 2), (Sum.inr 2197, 4), (Sum.inr 2235, 2), (Sum.inr 2247, 4), (Sum.inr 2255, 2), (Sum.inr 2268, 2), (Sum.inr 2281, 2), (Sum.inr 2712, 2), (Sum.inr 2755, 1), (Sum.inr 2770, 2)]

theorem sourceEq147 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm147 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA147 + difference 0 1) (sourceB147 + difference 1 0) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA147 + difference 0 1) (sourceB147 + difference 1 0) sourceC147) = raw4784 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4784; decide +kernel
    rw [ha]
    exact (canonical4784 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA147 + difference 0 2) (sourceB147 + difference 2 0) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA147 + difference 0 2) (sourceB147 + difference 2 0) sourceC147) = raw4785 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4785; decide +kernel
    rw [ha]
    exact (canonical4785 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA147 + difference 0 3) (sourceB147 + difference 3 0) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA147 + difference 0 3) (sourceB147 + difference 3 0) sourceC147) = raw4574 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4574; decide +kernel
    rw [ha]
    exact (canonical4574 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA147 + difference 0 4) (sourceB147 + difference 4 0) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA147 + difference 0 4) (sourceB147 + difference 4 0) sourceC147) = raw4786 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4786; decide +kernel
    rw [ha]
    exact (canonical4786 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA147 + difference 0 5) (sourceB147 + difference 5 0) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA147 + difference 0 5) (sourceB147 + difference 5 0) sourceC147) = raw4787 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4787; decide +kernel
    rw [ha]
    exact (canonical4787 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA147 + difference 1 0) (sourceB147 + difference 0 1) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA147 + difference 1 0) (sourceB147 + difference 0 1) sourceC147) = raw4788 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4788; decide +kernel
    rw [ha]
    exact (canonical4788 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA147 + difference 1 2) (sourceB147 + difference 2 1) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2187) := by
    have ha : (tripleCharges (sourceA147 + difference 1 2) (sourceB147 + difference 2 1) sourceC147) = raw4789 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4789; decide +kernel
    rw [ha]
    exact (canonical4789 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA147 + difference 1 3) (sourceB147 + difference 3 1) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA147 + difference 1 3) (sourceB147 + difference 3 1) sourceC147) = raw4579 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4579; decide +kernel
    rw [ha]
    exact (canonical4579 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA147 + difference 1 4) (sourceB147 + difference 4 1) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA147 + difference 1 4) (sourceB147 + difference 4 1) sourceC147) = raw4790 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4790; decide +kernel
    rw [ha]
    exact (canonical4790 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA147 + difference 1 5) (sourceB147 + difference 5 1) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA147 + difference 1 5) (sourceB147 + difference 5 1) sourceC147) = raw4791 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4791; decide +kernel
    rw [ha]
    exact (canonical4791 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA147 + difference 2 0) (sourceB147 + difference 0 2) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA147 + difference 2 0) (sourceB147 + difference 0 2) sourceC147) = raw4792 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4792; decide +kernel
    rw [ha]
    exact (canonical4792 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA147 + difference 2 1) (sourceB147 + difference 1 2) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2187) := by
    have ha : (tripleCharges (sourceA147 + difference 2 1) (sourceB147 + difference 1 2) sourceC147) = raw4793 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4793; decide +kernel
    rw [ha]
    exact (canonical4793 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA147 + difference 2 3) (sourceB147 + difference 3 2) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA147 + difference 2 3) (sourceB147 + difference 3 2) sourceC147) = raw4584 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4584; decide +kernel
    rw [ha]
    exact (canonical4584 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA147 + difference 2 4) (sourceB147 + difference 4 2) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA147 + difference 2 4) (sourceB147 + difference 4 2) sourceC147) = raw4794 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4794; decide +kernel
    rw [ha]
    exact (canonical4794 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA147 + difference 2 5) (sourceB147 + difference 5 2) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA147 + difference 2 5) (sourceB147 + difference 5 2) sourceC147) = raw4795 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4795; decide +kernel
    rw [ha]
    exact (canonical4795 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA147 + difference 3 0) (sourceB147 + difference 0 3) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA147 + difference 3 0) (sourceB147 + difference 0 3) sourceC147) = raw4796 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4796; decide +kernel
    rw [ha]
    exact (canonical4796 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA147 + difference 3 1) (sourceB147 + difference 1 3) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA147 + difference 3 1) (sourceB147 + difference 1 3) sourceC147) = raw4797 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4797; decide +kernel
    rw [ha]
    exact (canonical4797 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA147 + difference 3 2) (sourceB147 + difference 2 3) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA147 + difference 3 2) (sourceB147 + difference 2 3) sourceC147) = raw4798 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4798; decide +kernel
    rw [ha]
    exact (canonical4798 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA147 + difference 3 4) (sourceB147 + difference 4 3) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA147 + difference 3 4) (sourceB147 + difference 4 3) sourceC147) = raw4799 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4799; decide +kernel
    rw [ha]
    exact (canonical4799 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA147 + difference 3 5) (sourceB147 + difference 5 3) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA147 + difference 3 5) (sourceB147 + difference 5 3) sourceC147) = raw4800 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4800; decide +kernel
    rw [ha]
    exact (canonical4800 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA147 + difference 4 0) (sourceB147 + difference 0 4) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA147 + difference 4 0) (sourceB147 + difference 0 4) sourceC147) = raw4586 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4586; decide +kernel
    rw [ha]
    exact (canonical4586 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA147 + difference 4 1) (sourceB147 + difference 1 4) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA147 + difference 4 1) (sourceB147 + difference 1 4) sourceC147) = raw4587 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4587; decide +kernel
    rw [ha]
    exact (canonical4587 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA147 + difference 4 2) (sourceB147 + difference 2 4) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA147 + difference 4 2) (sourceB147 + difference 2 4) sourceC147) = raw4588 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4588; decide +kernel
    rw [ha]
    exact (canonical4588 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA147 + difference 4 3) (sourceB147 + difference 3 4) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA147 + difference 4 3) (sourceB147 + difference 3 4) sourceC147) = raw4801 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4801; decide +kernel
    rw [ha]
    exact (canonical4801 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA147 + difference 4 5) (sourceB147 + difference 5 4) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA147 + difference 4 5) (sourceB147 + difference 5 4) sourceC147) = raw4590 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4590; decide +kernel
    rw [ha]
    exact (canonical4590 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA147 + difference 5 0) (sourceB147 + difference 0 5) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA147 + difference 5 0) (sourceB147 + difference 0 5) sourceC147) = raw4802 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4802; decide +kernel
    rw [ha]
    exact (canonical4802 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA147 + difference 5 1) (sourceB147 + difference 1 5) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA147 + difference 5 1) (sourceB147 + difference 1 5) sourceC147) = raw4803 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4803; decide +kernel
    rw [ha]
    exact (canonical4803 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA147 + difference 5 2) (sourceB147 + difference 2 5) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA147 + difference 5 2) (sourceB147 + difference 2 5) sourceC147) = raw4804 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4804; decide +kernel
    rw [ha]
    exact (canonical4804 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA147 + difference 5 3) (sourceB147 + difference 3 5) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA147 + difference 5 3) (sourceB147 + difference 3 5) sourceC147) = raw4600 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4600; decide +kernel
    rw [ha]
    exact (canonical4600 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA147 + difference 5 4) (sourceB147 + difference 4 5) sourceC147) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA147 + difference 5 4) (sourceB147 + difference 4 5) sourceC147) = raw4805 := by
      apply Matrix.ext; unfold tripleCharges sourceA147 sourceB147 sourceC147 difference raw4805; decide +kernel
    rw [ha]
    exact (canonical4805 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA147 sourceB147 sourceC147
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm147, Integer.Sparse.eval]
  linarith only [hs]

def sourceA148 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB148 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC148 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm148 : Integer.Sparse Master := [(Sum.inr 1080, 1), (Sum.inr 2052, 2), (Sum.inr 2290, 1), (Sum.inr 2292, 2), (Sum.inr 4085, -1)]

theorem sourceEq148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm148 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA148 + difference 0 0) (sourceB148 + difference 0 0) sourceC148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA148 + difference 0 0) (sourceB148 + difference 0 0) sourceC148) = raw3719 := by
      apply Matrix.ext; unfold tripleCharges sourceA148 sourceB148 sourceC148 difference raw3719; decide +kernel
    rw [ha]
    exact (canonical3719 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA148 + difference 0 1) (sourceB148 + difference 1 0) sourceC148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA148 + difference 0 1) (sourceB148 + difference 1 0) sourceC148) = raw4271 := by
      apply Matrix.ext; unfold tripleCharges sourceA148 sourceB148 sourceC148 difference raw4271; decide +kernel
    rw [ha]
    exact (canonical4271 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA148 + difference 0 2) (sourceB148 + difference 2 0) sourceC148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA148 + difference 0 2) (sourceB148 + difference 2 0) sourceC148) = raw4806 := by
      apply Matrix.ext; unfold tripleCharges sourceA148 sourceB148 sourceC148 difference raw4806; decide +kernel
    rw [ha]
    exact (canonical4806 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA148 + difference 0 3) (sourceB148 + difference 3 0) sourceC148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA148 + difference 0 3) (sourceB148 + difference 3 0) sourceC148) = raw4375 := by
      apply Matrix.ext; unfold tripleCharges sourceA148 sourceB148 sourceC148 difference raw4375; decide +kernel
    rw [ha]
    exact (canonical4375 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA148 + difference 0 4) (sourceB148 + difference 4 0) sourceC148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA148 + difference 0 4) (sourceB148 + difference 4 0) sourceC148) = raw4807 := by
      apply Matrix.ext; unfold tripleCharges sourceA148 sourceB148 sourceC148 difference raw4807; decide +kernel
    rw [ha]
    exact (canonical4807 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA148 + difference 0 5) (sourceB148 + difference 5 0) sourceC148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA148 + difference 0 5) (sourceB148 + difference 5 0) sourceC148) = raw4808 := by
      apply Matrix.ext; unfold tripleCharges sourceA148 sourceB148 sourceC148 difference raw4808; decide +kernel
    rw [ha]
    exact (canonical4808 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA148 + sourceB148) sourceC148) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA148 + sourceB148) sourceC148) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA148 sourceB148 sourceC148 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA148 sourceB148 sourceC148
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm148, Integer.Sparse.eval]
  linarith only [hs]

def sourceA149 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB149 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC149 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm149 : Integer.Sparse Master := [(Sum.inr 4591, 4), (Sum.inr 4594, 1), (Sum.inr 4608, 2), (Sum.inr 4609, 2), (Sum.inr 5075, 4), (Sum.inr 5107, 1), (Sum.inr 5127, 2), (Sum.inr 5147, 4), (Sum.inr 5201, 1), (Sum.inr 5258, 4), (Sum.inr 5274, 2), (Sum.inr 5291, 2), (Sum.inr 5441, 1)]

theorem sourceEq149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm149 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA149 + difference 0 1) (sourceB149 + difference 1 0) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA149 + difference 0 1) (sourceB149 + difference 1 0) sourceC149) = raw4809 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4809; decide +kernel
    rw [ha]
    exact (canonical4809 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA149 + difference 0 2) (sourceB149 + difference 2 0) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA149 + difference 0 2) (sourceB149 + difference 2 0) sourceC149) = raw4810 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4810; decide +kernel
    rw [ha]
    exact (canonical4810 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA149 + difference 0 3) (sourceB149 + difference 3 0) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA149 + difference 0 3) (sourceB149 + difference 3 0) sourceC149) = raw4811 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4811; decide +kernel
    rw [ha]
    exact (canonical4811 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA149 + difference 0 4) (sourceB149 + difference 4 0) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA149 + difference 0 4) (sourceB149 + difference 4 0) sourceC149) = raw4812 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4812; decide +kernel
    rw [ha]
    exact (canonical4812 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA149 + difference 0 5) (sourceB149 + difference 5 0) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA149 + difference 0 5) (sourceB149 + difference 5 0) sourceC149) = raw4813 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4813; decide +kernel
    rw [ha]
    exact (canonical4813 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA149 + difference 1 0) (sourceB149 + difference 0 1) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA149 + difference 1 0) (sourceB149 + difference 0 1) sourceC149) = raw4814 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4814; decide +kernel
    rw [ha]
    exact (canonical4814 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA149 + difference 1 2) (sourceB149 + difference 2 1) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA149 + difference 1 2) (sourceB149 + difference 2 1) sourceC149) = raw4815 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4815; decide +kernel
    rw [ha]
    exact (canonical4815 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA149 + difference 1 3) (sourceB149 + difference 3 1) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA149 + difference 1 3) (sourceB149 + difference 3 1) sourceC149) = raw4816 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4816; decide +kernel
    rw [ha]
    exact (canonical4816 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA149 + difference 1 4) (sourceB149 + difference 4 1) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA149 + difference 1 4) (sourceB149 + difference 4 1) sourceC149) = raw4817 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4817; decide +kernel
    rw [ha]
    exact (canonical4817 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA149 + difference 1 5) (sourceB149 + difference 5 1) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA149 + difference 1 5) (sourceB149 + difference 5 1) sourceC149) = raw4818 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4818; decide +kernel
    rw [ha]
    exact (canonical4818 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA149 + difference 2 0) (sourceB149 + difference 0 2) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA149 + difference 2 0) (sourceB149 + difference 0 2) sourceC149) = raw4819 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4819; decide +kernel
    rw [ha]
    exact (canonical4819 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA149 + difference 2 1) (sourceB149 + difference 1 2) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA149 + difference 2 1) (sourceB149 + difference 1 2) sourceC149) = raw4820 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4820; decide +kernel
    rw [ha]
    exact (canonical4820 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA149 + difference 2 3) (sourceB149 + difference 3 2) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5127) := by
    have ha : (tripleCharges (sourceA149 + difference 2 3) (sourceB149 + difference 3 2) sourceC149) = raw4821 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4821; decide +kernel
    rw [ha]
    exact (canonical4821 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA149 + difference 2 4) (sourceB149 + difference 4 2) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA149 + difference 2 4) (sourceB149 + difference 4 2) sourceC149) = raw4822 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4822; decide +kernel
    rw [ha]
    exact (canonical4822 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA149 + difference 2 5) (sourceB149 + difference 5 2) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA149 + difference 2 5) (sourceB149 + difference 5 2) sourceC149) = raw4823 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4823; decide +kernel
    rw [ha]
    exact (canonical4823 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA149 + difference 3 0) (sourceB149 + difference 0 3) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA149 + difference 3 0) (sourceB149 + difference 0 3) sourceC149) = raw4824 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4824; decide +kernel
    rw [ha]
    exact (canonical4824 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA149 + difference 3 1) (sourceB149 + difference 1 3) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA149 + difference 3 1) (sourceB149 + difference 1 3) sourceC149) = raw4825 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4825; decide +kernel
    rw [ha]
    exact (canonical4825 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA149 + difference 3 2) (sourceB149 + difference 2 3) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5127) := by
    have ha : (tripleCharges (sourceA149 + difference 3 2) (sourceB149 + difference 2 3) sourceC149) = raw4826 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4826; decide +kernel
    rw [ha]
    exact (canonical4826 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA149 + difference 3 4) (sourceB149 + difference 4 3) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA149 + difference 3 4) (sourceB149 + difference 4 3) sourceC149) = raw4827 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4827; decide +kernel
    rw [ha]
    exact (canonical4827 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA149 + difference 3 5) (sourceB149 + difference 5 3) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA149 + difference 3 5) (sourceB149 + difference 5 3) sourceC149) = raw4828 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4828; decide +kernel
    rw [ha]
    exact (canonical4828 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA149 + difference 4 0) (sourceB149 + difference 0 4) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA149 + difference 4 0) (sourceB149 + difference 0 4) sourceC149) = raw4829 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4829; decide +kernel
    rw [ha]
    exact (canonical4829 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA149 + difference 4 1) (sourceB149 + difference 1 4) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5201) := by
    have ha : (tripleCharges (sourceA149 + difference 4 1) (sourceB149 + difference 1 4) sourceC149) = raw4830 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4830; decide +kernel
    rw [ha]
    exact (canonical4830 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA149 + difference 4 2) (sourceB149 + difference 2 4) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA149 + difference 4 2) (sourceB149 + difference 2 4) sourceC149) = raw4831 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4831; decide +kernel
    rw [ha]
    exact (canonical4831 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA149 + difference 4 3) (sourceB149 + difference 3 4) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA149 + difference 4 3) (sourceB149 + difference 3 4) sourceC149) = raw4832 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4832; decide +kernel
    rw [ha]
    exact (canonical4832 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA149 + difference 4 5) (sourceB149 + difference 5 4) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA149 + difference 4 5) (sourceB149 + difference 5 4) sourceC149) = raw4833 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4833; decide +kernel
    rw [ha]
    exact (canonical4833 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA149 + difference 5 0) (sourceB149 + difference 0 5) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA149 + difference 5 0) (sourceB149 + difference 0 5) sourceC149) = raw4834 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4834; decide +kernel
    rw [ha]
    exact (canonical4834 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA149 + difference 5 1) (sourceB149 + difference 1 5) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA149 + difference 5 1) (sourceB149 + difference 1 5) sourceC149) = raw4835 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4835; decide +kernel
    rw [ha]
    exact (canonical4835 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA149 + difference 5 2) (sourceB149 + difference 2 5) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA149 + difference 5 2) (sourceB149 + difference 2 5) sourceC149) = raw4836 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4836; decide +kernel
    rw [ha]
    exact (canonical4836 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA149 + difference 5 3) (sourceB149 + difference 3 5) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA149 + difference 5 3) (sourceB149 + difference 3 5) sourceC149) = raw4837 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4837; decide +kernel
    rw [ha]
    exact (canonical4837 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA149 + difference 5 4) (sourceB149 + difference 4 5) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA149 + difference 5 4) (sourceB149 + difference 4 5) sourceC149) = raw4838 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4838; decide +kernel
    rw [ha]
    exact (canonical4838 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA149 sourceB149 sourceC149
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm149, Integer.Sparse.eval]
  linarith only [hs]

def sourceA150 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB150 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC150 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm150 : Integer.Sparse Master := [(Sum.inr 1217, 4), (Sum.inr 1221, 1), (Sum.inr 1243, 2), (Sum.inr 1269, 2), (Sum.inr 2865, 4), (Sum.inr 2886, 1), (Sum.inr 2914, 2), (Sum.inr 2939, 4), (Sum.inr 3002, 1), (Sum.inr 3089, 4), (Sum.inr 3103, 2), (Sum.inr 3112, 2), (Sum.inr 4037, 1)]

theorem sourceEq150 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm150 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA150 + difference 0 1) (sourceB150 + difference 1 0) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA150 + difference 0 1) (sourceB150 + difference 1 0) sourceC150) = raw4839 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4839; decide +kernel
    rw [ha]
    exact (canonical4839 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA150 + difference 0 2) (sourceB150 + difference 2 0) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA150 + difference 0 2) (sourceB150 + difference 2 0) sourceC150) = raw4840 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4840; decide +kernel
    rw [ha]
    exact (canonical4840 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA150 + difference 0 3) (sourceB150 + difference 3 0) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA150 + difference 0 3) (sourceB150 + difference 3 0) sourceC150) = raw4841 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4841; decide +kernel
    rw [ha]
    exact (canonical4841 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA150 + difference 0 4) (sourceB150 + difference 4 0) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA150 + difference 0 4) (sourceB150 + difference 4 0) sourceC150) = raw4842 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4842; decide +kernel
    rw [ha]
    exact (canonical4842 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA150 + difference 0 5) (sourceB150 + difference 5 0) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4037) := by
    have ha : (tripleCharges (sourceA150 + difference 0 5) (sourceB150 + difference 5 0) sourceC150) = raw4843 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4843; decide +kernel
    rw [ha]
    exact (canonical4843 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA150 + difference 1 0) (sourceB150 + difference 0 1) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1269) := by
    have ha : (tripleCharges (sourceA150 + difference 1 0) (sourceB150 + difference 0 1) sourceC150) = raw4844 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4844; decide +kernel
    rw [ha]
    exact (canonical4844 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA150 + difference 1 2) (sourceB150 + difference 2 1) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2939) := by
    have ha : (tripleCharges (sourceA150 + difference 1 2) (sourceB150 + difference 2 1) sourceC150) = raw4845 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4845; decide +kernel
    rw [ha]
    exact (canonical4845 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA150 + difference 1 3) (sourceB150 + difference 3 1) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2939) := by
    have ha : (tripleCharges (sourceA150 + difference 1 3) (sourceB150 + difference 3 1) sourceC150) = raw4846 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4846; decide +kernel
    rw [ha]
    exact (canonical4846 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA150 + difference 1 4) (sourceB150 + difference 4 1) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3002) := by
    have ha : (tripleCharges (sourceA150 + difference 1 4) (sourceB150 + difference 4 1) sourceC150) = raw4847 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4847; decide +kernel
    rw [ha]
    exact (canonical4847 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA150 + difference 1 5) (sourceB150 + difference 5 1) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA150 + difference 1 5) (sourceB150 + difference 5 1) sourceC150) = raw4848 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4848; decide +kernel
    rw [ha]
    exact (canonical4848 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA150 + difference 2 0) (sourceB150 + difference 0 2) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA150 + difference 2 0) (sourceB150 + difference 0 2) sourceC150) = raw4849 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4849; decide +kernel
    rw [ha]
    exact (canonical4849 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA150 + difference 2 1) (sourceB150 + difference 1 2) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA150 + difference 2 1) (sourceB150 + difference 1 2) sourceC150) = raw4850 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4850; decide +kernel
    rw [ha]
    exact (canonical4850 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA150 + difference 2 3) (sourceB150 + difference 3 2) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2914) := by
    have ha : (tripleCharges (sourceA150 + difference 2 3) (sourceB150 + difference 3 2) sourceC150) = raw4851 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4851; decide +kernel
    rw [ha]
    exact (canonical4851 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA150 + difference 2 4) (sourceB150 + difference 4 2) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2939) := by
    have ha : (tripleCharges (sourceA150 + difference 2 4) (sourceB150 + difference 4 2) sourceC150) = raw4852 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4852; decide +kernel
    rw [ha]
    exact (canonical4852 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA150 + difference 2 5) (sourceB150 + difference 5 2) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA150 + difference 2 5) (sourceB150 + difference 5 2) sourceC150) = raw4853 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4853; decide +kernel
    rw [ha]
    exact (canonical4853 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA150 + difference 3 0) (sourceB150 + difference 0 3) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA150 + difference 3 0) (sourceB150 + difference 0 3) sourceC150) = raw4854 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4854; decide +kernel
    rw [ha]
    exact (canonical4854 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA150 + difference 3 1) (sourceB150 + difference 1 3) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA150 + difference 3 1) (sourceB150 + difference 1 3) sourceC150) = raw4855 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4855; decide +kernel
    rw [ha]
    exact (canonical4855 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA150 + difference 3 2) (sourceB150 + difference 2 3) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2914) := by
    have ha : (tripleCharges (sourceA150 + difference 3 2) (sourceB150 + difference 2 3) sourceC150) = raw4856 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4856; decide +kernel
    rw [ha]
    exact (canonical4856 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA150 + difference 3 4) (sourceB150 + difference 4 3) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2939) := by
    have ha : (tripleCharges (sourceA150 + difference 3 4) (sourceB150 + difference 4 3) sourceC150) = raw4857 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4857; decide +kernel
    rw [ha]
    exact (canonical4857 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA150 + difference 3 5) (sourceB150 + difference 5 3) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA150 + difference 3 5) (sourceB150 + difference 5 3) sourceC150) = raw4858 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4858; decide +kernel
    rw [ha]
    exact (canonical4858 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA150 + difference 4 0) (sourceB150 + difference 0 4) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA150 + difference 4 0) (sourceB150 + difference 0 4) sourceC150) = raw4859 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4859; decide +kernel
    rw [ha]
    exact (canonical4859 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA150 + difference 4 1) (sourceB150 + difference 1 4) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2886) := by
    have ha : (tripleCharges (sourceA150 + difference 4 1) (sourceB150 + difference 1 4) sourceC150) = raw4860 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4860; decide +kernel
    rw [ha]
    exact (canonical4860 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA150 + difference 4 2) (sourceB150 + difference 2 4) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA150 + difference 4 2) (sourceB150 + difference 2 4) sourceC150) = raw4861 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4861; decide +kernel
    rw [ha]
    exact (canonical4861 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA150 + difference 4 3) (sourceB150 + difference 3 4) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA150 + difference 4 3) (sourceB150 + difference 3 4) sourceC150) = raw4862 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4862; decide +kernel
    rw [ha]
    exact (canonical4862 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA150 + difference 4 5) (sourceB150 + difference 5 4) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA150 + difference 4 5) (sourceB150 + difference 5 4) sourceC150) = raw4863 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4863; decide +kernel
    rw [ha]
    exact (canonical4863 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA150 + difference 5 0) (sourceB150 + difference 0 5) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA150 + difference 5 0) (sourceB150 + difference 0 5) sourceC150) = raw4864 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4864; decide +kernel
    rw [ha]
    exact (canonical4864 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA150 + difference 5 1) (sourceB150 + difference 1 5) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA150 + difference 5 1) (sourceB150 + difference 1 5) sourceC150) = raw4865 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4865; decide +kernel
    rw [ha]
    exact (canonical4865 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA150 + difference 5 2) (sourceB150 + difference 2 5) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA150 + difference 5 2) (sourceB150 + difference 2 5) sourceC150) = raw4866 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4866; decide +kernel
    rw [ha]
    exact (canonical4866 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA150 + difference 5 3) (sourceB150 + difference 3 5) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA150 + difference 5 3) (sourceB150 + difference 3 5) sourceC150) = raw4867 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4867; decide +kernel
    rw [ha]
    exact (canonical4867 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA150 + difference 5 4) (sourceB150 + difference 4 5) sourceC150) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1269) := by
    have ha : (tripleCharges (sourceA150 + difference 5 4) (sourceB150 + difference 4 5) sourceC150) = raw4868 := by
      apply Matrix.ext; unfold tripleCharges sourceA150 sourceB150 sourceC150 difference raw4868; decide +kernel
    rw [ha]
    exact (canonical4868 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA150 sourceB150 sourceC150
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm150, Integer.Sparse.eval]
  linarith only [hs]

def sourceA151 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB151 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC151 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm151 : Integer.Sparse Master := [(Sum.inr 3291, 4), (Sum.inr 3298, 1), (Sum.inr 3300, 2), (Sum.inr 3302, 2), (Sum.inr 3468, 4), (Sum.inr 3484, 1), (Sum.inr 3513, 2), (Sum.inr 3530, 4), (Sum.inr 3533, 4), (Sum.inr 3547, 2), (Sum.inr 3579, 1), (Sum.inr 3582, 2), (Sum.inr 3860, 1)]

theorem sourceEq151 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm151 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA151 + difference 0 1) (sourceB151 + difference 1 0) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA151 + difference 0 1) (sourceB151 + difference 1 0) sourceC151) = raw4869 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4869; decide +kernel
    rw [ha]
    exact (canonical4869 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA151 + difference 0 2) (sourceB151 + difference 2 0) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA151 + difference 0 2) (sourceB151 + difference 2 0) sourceC151) = raw4870 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4870; decide +kernel
    rw [ha]
    exact (canonical4870 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA151 + difference 0 3) (sourceB151 + difference 3 0) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA151 + difference 0 3) (sourceB151 + difference 3 0) sourceC151) = raw4871 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4871; decide +kernel
    rw [ha]
    exact (canonical4871 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA151 + difference 0 4) (sourceB151 + difference 4 0) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA151 + difference 0 4) (sourceB151 + difference 4 0) sourceC151) = raw4872 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4872; decide +kernel
    rw [ha]
    exact (canonical4872 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA151 + difference 0 5) (sourceB151 + difference 5 0) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3860) := by
    have ha : (tripleCharges (sourceA151 + difference 0 5) (sourceB151 + difference 5 0) sourceC151) = raw4873 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4873; decide +kernel
    rw [ha]
    exact (canonical4873 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA151 + difference 1 0) (sourceB151 + difference 0 1) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA151 + difference 1 0) (sourceB151 + difference 0 1) sourceC151) = raw4874 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4874; decide +kernel
    rw [ha]
    exact (canonical4874 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA151 + difference 1 2) (sourceB151 + difference 2 1) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA151 + difference 1 2) (sourceB151 + difference 2 1) sourceC151) = raw4875 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4875; decide +kernel
    rw [ha]
    exact (canonical4875 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA151 + difference 1 3) (sourceB151 + difference 3 1) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA151 + difference 1 3) (sourceB151 + difference 3 1) sourceC151) = raw4876 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4876; decide +kernel
    rw [ha]
    exact (canonical4876 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA151 + difference 1 4) (sourceB151 + difference 4 1) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3484) := by
    have ha : (tripleCharges (sourceA151 + difference 1 4) (sourceB151 + difference 4 1) sourceC151) = raw4877 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4877; decide +kernel
    rw [ha]
    exact (canonical4877 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA151 + difference 1 5) (sourceB151 + difference 5 1) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA151 + difference 1 5) (sourceB151 + difference 5 1) sourceC151) = raw4878 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4878; decide +kernel
    rw [ha]
    exact (canonical4878 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA151 + difference 2 0) (sourceB151 + difference 0 2) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA151 + difference 2 0) (sourceB151 + difference 0 2) sourceC151) = raw4879 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4879; decide +kernel
    rw [ha]
    exact (canonical4879 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA151 + difference 2 1) (sourceB151 + difference 1 2) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA151 + difference 2 1) (sourceB151 + difference 1 2) sourceC151) = raw4880 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4880; decide +kernel
    rw [ha]
    exact (canonical4880 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA151 + difference 2 3) (sourceB151 + difference 3 2) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA151 + difference 2 3) (sourceB151 + difference 3 2) sourceC151) = raw4881 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4881; decide +kernel
    rw [ha]
    exact (canonical4881 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA151 + difference 2 4) (sourceB151 + difference 4 2) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA151 + difference 2 4) (sourceB151 + difference 4 2) sourceC151) = raw4882 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4882; decide +kernel
    rw [ha]
    exact (canonical4882 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA151 + difference 2 5) (sourceB151 + difference 5 2) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA151 + difference 2 5) (sourceB151 + difference 5 2) sourceC151) = raw4883 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4883; decide +kernel
    rw [ha]
    exact (canonical4883 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA151 + difference 3 0) (sourceB151 + difference 0 3) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA151 + difference 3 0) (sourceB151 + difference 0 3) sourceC151) = raw4884 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4884; decide +kernel
    rw [ha]
    exact (canonical4884 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA151 + difference 3 1) (sourceB151 + difference 1 3) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA151 + difference 3 1) (sourceB151 + difference 1 3) sourceC151) = raw4885 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4885; decide +kernel
    rw [ha]
    exact (canonical4885 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA151 + difference 3 2) (sourceB151 + difference 2 3) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA151 + difference 3 2) (sourceB151 + difference 2 3) sourceC151) = raw4886 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4886; decide +kernel
    rw [ha]
    exact (canonical4886 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA151 + difference 3 4) (sourceB151 + difference 4 3) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA151 + difference 3 4) (sourceB151 + difference 4 3) sourceC151) = raw4887 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4887; decide +kernel
    rw [ha]
    exact (canonical4887 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA151 + difference 3 5) (sourceB151 + difference 5 3) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA151 + difference 3 5) (sourceB151 + difference 5 3) sourceC151) = raw4888 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4888; decide +kernel
    rw [ha]
    exact (canonical4888 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA151 + difference 4 0) (sourceB151 + difference 0 4) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA151 + difference 4 0) (sourceB151 + difference 0 4) sourceC151) = raw4889 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4889; decide +kernel
    rw [ha]
    exact (canonical4889 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA151 + difference 4 1) (sourceB151 + difference 1 4) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3579) := by
    have ha : (tripleCharges (sourceA151 + difference 4 1) (sourceB151 + difference 1 4) sourceC151) = raw4890 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4890; decide +kernel
    rw [ha]
    exact (canonical4890 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA151 + difference 4 2) (sourceB151 + difference 2 4) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA151 + difference 4 2) (sourceB151 + difference 2 4) sourceC151) = raw4891 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4891; decide +kernel
    rw [ha]
    exact (canonical4891 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA151 + difference 4 3) (sourceB151 + difference 3 4) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA151 + difference 4 3) (sourceB151 + difference 3 4) sourceC151) = raw4892 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4892; decide +kernel
    rw [ha]
    exact (canonical4892 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA151 + difference 4 5) (sourceB151 + difference 5 4) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA151 + difference 4 5) (sourceB151 + difference 5 4) sourceC151) = raw4893 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4893; decide +kernel
    rw [ha]
    exact (canonical4893 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA151 + difference 5 0) (sourceB151 + difference 0 5) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3298) := by
    have ha : (tripleCharges (sourceA151 + difference 5 0) (sourceB151 + difference 0 5) sourceC151) = raw4894 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4894; decide +kernel
    rw [ha]
    exact (canonical4894 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA151 + difference 5 1) (sourceB151 + difference 1 5) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA151 + difference 5 1) (sourceB151 + difference 1 5) sourceC151) = raw4895 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4895; decide +kernel
    rw [ha]
    exact (canonical4895 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA151 + difference 5 2) (sourceB151 + difference 2 5) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA151 + difference 5 2) (sourceB151 + difference 2 5) sourceC151) = raw4896 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4896; decide +kernel
    rw [ha]
    exact (canonical4896 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA151 + difference 5 3) (sourceB151 + difference 3 5) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA151 + difference 5 3) (sourceB151 + difference 3 5) sourceC151) = raw4897 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4897; decide +kernel
    rw [ha]
    exact (canonical4897 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA151 + difference 5 4) (sourceB151 + difference 4 5) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA151 + difference 5 4) (sourceB151 + difference 4 5) sourceC151) = raw4898 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4898; decide +kernel
    rw [ha]
    exact (canonical4898 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA151 sourceB151 sourceC151
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm151, Integer.Sparse.eval]
  linarith only [hs]

def sourceA152 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB152 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC152 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm152 : Integer.Sparse Master := [(Sum.inr 2722, 2), (Sum.inr 2726, 1), (Sum.inr 2742, 1), (Sum.inr 2765, 1), (Sum.inr 3905, 1), (Sum.inr 4092, -1)]

theorem sourceEq152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm152 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA152 + difference 0 0) (sourceB152 + difference 0 0) sourceC152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA152 + difference 0 0) (sourceB152 + difference 0 0) sourceC152) = raw4899 := by
      apply Matrix.ext; unfold tripleCharges sourceA152 sourceB152 sourceC152 difference raw4899; decide +kernel
    rw [ha]
    exact (canonical4899 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA152 + difference 0 1) (sourceB152 + difference 1 0) sourceC152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA152 + difference 0 1) (sourceB152 + difference 1 0) sourceC152) = raw4900 := by
      apply Matrix.ext; unfold tripleCharges sourceA152 sourceB152 sourceC152 difference raw4900; decide +kernel
    rw [ha]
    exact (canonical4900 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA152 + difference 0 2) (sourceB152 + difference 2 0) sourceC152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA152 + difference 0 2) (sourceB152 + difference 2 0) sourceC152) = raw4901 := by
      apply Matrix.ext; unfold tripleCharges sourceA152 sourceB152 sourceC152 difference raw4901; decide +kernel
    rw [ha]
    exact (canonical4901 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA152 + difference 0 3) (sourceB152 + difference 3 0) sourceC152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA152 + difference 0 3) (sourceB152 + difference 3 0) sourceC152) = raw4902 := by
      apply Matrix.ext; unfold tripleCharges sourceA152 sourceB152 sourceC152 difference raw4902; decide +kernel
    rw [ha]
    exact (canonical4902 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA152 + difference 0 4) (sourceB152 + difference 4 0) sourceC152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA152 + difference 0 4) (sourceB152 + difference 4 0) sourceC152) = raw4903 := by
      apply Matrix.ext; unfold tripleCharges sourceA152 sourceB152 sourceC152 difference raw4903; decide +kernel
    rw [ha]
    exact (canonical4903 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA152 + difference 0 5) (sourceB152 + difference 5 0) sourceC152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3905) := by
    have ha : (tripleCharges (sourceA152 + difference 0 5) (sourceB152 + difference 5 0) sourceC152) = raw4904 := by
      apply Matrix.ext; unfold tripleCharges sourceA152 sourceB152 sourceC152 difference raw4904; decide +kernel
    rw [ha]
    exact (canonical4904 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA152 + sourceB152) sourceC152) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA152 + sourceB152) sourceC152) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA152 sourceB152 sourceC152 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA152 sourceB152 sourceC152
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm152, Integer.Sparse.eval]
  linarith only [hs]

def sourceA153 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB153 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC153 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm153 : Integer.Sparse Master := [(Sum.inr 1215, 2), (Sum.inr 1221, 1), (Sum.inr 1242, 1), (Sum.inr 1264, 1), (Sum.inr 2726, 1), (Sum.inr 4092, -1)]

theorem sourceEq153 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm153 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA153 + difference 0 0) (sourceB153 + difference 0 0) sourceC153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA153 + difference 0 0) (sourceB153 + difference 0 0) sourceC153) = raw4899 := by
      apply Matrix.ext; unfold tripleCharges sourceA153 sourceB153 sourceC153 difference raw4899; decide +kernel
    rw [ha]
    exact (canonical4899 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA153 + difference 1 0) (sourceB153 + difference 0 1) sourceC153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA153 + difference 1 0) (sourceB153 + difference 0 1) sourceC153) = raw4906 := by
      apply Matrix.ext; unfold tripleCharges sourceA153 sourceB153 sourceC153 difference raw4906; decide +kernel
    rw [ha]
    exact (canonical4906 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA153 + difference 2 0) (sourceB153 + difference 0 2) sourceC153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA153 + difference 2 0) (sourceB153 + difference 0 2) sourceC153) = raw4907 := by
      apply Matrix.ext; unfold tripleCharges sourceA153 sourceB153 sourceC153 difference raw4907; decide +kernel
    rw [ha]
    exact (canonical4907 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA153 + difference 3 0) (sourceB153 + difference 0 3) sourceC153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA153 + difference 3 0) (sourceB153 + difference 0 3) sourceC153) = raw4908 := by
      apply Matrix.ext; unfold tripleCharges sourceA153 sourceB153 sourceC153 difference raw4908; decide +kernel
    rw [ha]
    exact (canonical4908 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA153 + difference 4 0) (sourceB153 + difference 0 4) sourceC153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1264) := by
    have ha : (tripleCharges (sourceA153 + difference 4 0) (sourceB153 + difference 0 4) sourceC153) = raw4909 := by
      apply Matrix.ext; unfold tripleCharges sourceA153 sourceB153 sourceC153 difference raw4909; decide +kernel
    rw [ha]
    exact (canonical4909 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA153 + difference 5 0) (sourceB153 + difference 0 5) sourceC153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA153 + difference 5 0) (sourceB153 + difference 0 5) sourceC153) = raw4910 := by
      apply Matrix.ext; unfold tripleCharges sourceA153 sourceB153 sourceC153 difference raw4910; decide +kernel
    rw [ha]
    exact (canonical4910 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA153 + sourceB153) sourceC153) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA153 + sourceB153) sourceC153) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA153 sourceB153 sourceC153 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA153 sourceB153 sourceC153
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm153, Integer.Sparse.eval]
  linarith only [hs]

def sourceA154 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB154 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC154 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm154 : Integer.Sparse Master := [(Sum.inr 1242, 1), (Sum.inr 2482, 2), (Sum.inr 2517, 1), (Sum.inr 2726, 1), (Sum.inr 2742, 1), (Sum.inr 4092, -1)]

theorem sourceEq154 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm154 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA154 + difference 1 0) (sourceB154 + difference 0 1) sourceC154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA154 + difference 1 0) (sourceB154 + difference 0 1) sourceC154) = raw4906 := by
      apply Matrix.ext; unfold tripleCharges sourceA154 sourceB154 sourceC154 difference raw4906; decide +kernel
    rw [ha]
    exact (canonical4906 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA154 + difference 1 1) (sourceB154 + difference 1 1) sourceC154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA154 + difference 1 1) (sourceB154 + difference 1 1) sourceC154) = raw4899 := by
      apply Matrix.ext; unfold tripleCharges sourceA154 sourceB154 sourceC154 difference raw4899; decide +kernel
    rw [ha]
    exact (canonical4899 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA154 + difference 1 2) (sourceB154 + difference 2 1) sourceC154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA154 + difference 1 2) (sourceB154 + difference 2 1) sourceC154) = raw4911 := by
      apply Matrix.ext; unfold tripleCharges sourceA154 sourceB154 sourceC154 difference raw4911; decide +kernel
    rw [ha]
    exact (canonical4911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA154 + difference 1 3) (sourceB154 + difference 3 1) sourceC154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA154 + difference 1 3) (sourceB154 + difference 3 1) sourceC154) = raw4912 := by
      apply Matrix.ext; unfold tripleCharges sourceA154 sourceB154 sourceC154 difference raw4912; decide +kernel
    rw [ha]
    exact (canonical4912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA154 + difference 1 4) (sourceB154 + difference 4 1) sourceC154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2517) := by
    have ha : (tripleCharges (sourceA154 + difference 1 4) (sourceB154 + difference 4 1) sourceC154) = raw4913 := by
      apply Matrix.ext; unfold tripleCharges sourceA154 sourceB154 sourceC154 difference raw4913; decide +kernel
    rw [ha]
    exact (canonical4913 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA154 + difference 1 5) (sourceB154 + difference 5 1) sourceC154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA154 + difference 1 5) (sourceB154 + difference 5 1) sourceC154) = raw4914 := by
      apply Matrix.ext; unfold tripleCharges sourceA154 sourceB154 sourceC154 difference raw4914; decide +kernel
    rw [ha]
    exact (canonical4914 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA154 + sourceB154) sourceC154) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA154 + sourceB154) sourceC154) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA154 sourceB154 sourceC154 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA154 sourceB154 sourceC154
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm154, Integer.Sparse.eval]
  linarith only [hs]

def sourceA155 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB155 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC155 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm155 : Integer.Sparse Master := [(Sum.inr 1264, 1), (Sum.inr 2569, 2), (Sum.inr 2635, 1), (Sum.inr 2726, 1), (Sum.inr 2765, 1), (Sum.inr 4092, -1)]

theorem sourceEq155 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm155 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA155 + difference 0 1) (sourceB155 + difference 1 0) sourceC155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA155 + difference 0 1) (sourceB155 + difference 1 0) sourceC155) = raw4900 := by
      apply Matrix.ext; unfold tripleCharges sourceA155 sourceB155 sourceC155 difference raw4900; decide +kernel
    rw [ha]
    exact (canonical4900 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA155 + difference 1 1) (sourceB155 + difference 1 1) sourceC155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA155 + difference 1 1) (sourceB155 + difference 1 1) sourceC155) = raw4899 := by
      apply Matrix.ext; unfold tripleCharges sourceA155 sourceB155 sourceC155 difference raw4899; decide +kernel
    rw [ha]
    exact (canonical4899 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA155 + difference 2 1) (sourceB155 + difference 1 2) sourceC155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2569) := by
    have ha : (tripleCharges (sourceA155 + difference 2 1) (sourceB155 + difference 1 2) sourceC155) = raw4915 := by
      apply Matrix.ext; unfold tripleCharges sourceA155 sourceB155 sourceC155 difference raw4915; decide +kernel
    rw [ha]
    exact (canonical4915 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA155 + difference 3 1) (sourceB155 + difference 1 3) sourceC155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2569) := by
    have ha : (tripleCharges (sourceA155 + difference 3 1) (sourceB155 + difference 1 3) sourceC155) = raw4916 := by
      apply Matrix.ext; unfold tripleCharges sourceA155 sourceB155 sourceC155 difference raw4916; decide +kernel
    rw [ha]
    exact (canonical4916 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA155 + difference 4 1) (sourceB155 + difference 1 4) sourceC155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2635) := by
    have ha : (tripleCharges (sourceA155 + difference 4 1) (sourceB155 + difference 1 4) sourceC155) = raw4917 := by
      apply Matrix.ext; unfold tripleCharges sourceA155 sourceB155 sourceC155 difference raw4917; decide +kernel
    rw [ha]
    exact (canonical4917 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA155 + difference 5 1) (sourceB155 + difference 1 5) sourceC155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1264) := by
    have ha : (tripleCharges (sourceA155 + difference 5 1) (sourceB155 + difference 1 5) sourceC155) = raw4918 := by
      apply Matrix.ext; unfold tripleCharges sourceA155 sourceB155 sourceC155 difference raw4918; decide +kernel
    rw [ha]
    exact (canonical4918 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA155 + sourceB155) sourceC155) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA155 + sourceB155) sourceC155) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA155 sourceB155 sourceC155 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA155 sourceB155 sourceC155
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm155, Integer.Sparse.eval]
  linarith only [hs]

def sourceA156 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB156 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC156 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm156 : Integer.Sparse Master := [(Sum.inr 1215, 1), (Sum.inr 2482, 1), (Sum.inr 2542, 1), (Sum.inr 2569, 1), (Sum.inr 2722, 1), (Sum.inr 2726, 1), (Sum.inr 4092, -1)]

theorem sourceEq156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm156 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA156 + difference 2 0) (sourceB156 + difference 0 2) sourceC156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA156 + difference 2 0) (sourceB156 + difference 0 2) sourceC156) = raw4907 := by
      apply Matrix.ext; unfold tripleCharges sourceA156 sourceB156 sourceC156 difference raw4907; decide +kernel
    rw [ha]
    exact (canonical4907 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA156 + difference 2 1) (sourceB156 + difference 1 2) sourceC156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2569) := by
    have ha : (tripleCharges (sourceA156 + difference 2 1) (sourceB156 + difference 1 2) sourceC156) = raw4915 := by
      apply Matrix.ext; unfold tripleCharges sourceA156 sourceB156 sourceC156 difference raw4915; decide +kernel
    rw [ha]
    exact (canonical4915 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA156 + difference 2 2) (sourceB156 + difference 2 2) sourceC156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA156 + difference 2 2) (sourceB156 + difference 2 2) sourceC156) = raw4899 := by
      apply Matrix.ext; unfold tripleCharges sourceA156 sourceB156 sourceC156 difference raw4899; decide +kernel
    rw [ha]
    exact (canonical4899 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA156 + difference 2 3) (sourceB156 + difference 3 2) sourceC156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2542) := by
    have ha : (tripleCharges (sourceA156 + difference 2 3) (sourceB156 + difference 3 2) sourceC156) = raw4919 := by
      apply Matrix.ext; unfold tripleCharges sourceA156 sourceB156 sourceC156 difference raw4919; decide +kernel
    rw [ha]
    exact (canonical4919 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA156 + difference 2 4) (sourceB156 + difference 4 2) sourceC156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA156 + difference 2 4) (sourceB156 + difference 4 2) sourceC156) = raw4920 := by
      apply Matrix.ext; unfold tripleCharges sourceA156 sourceB156 sourceC156 difference raw4920; decide +kernel
    rw [ha]
    exact (canonical4920 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA156 + difference 2 5) (sourceB156 + difference 5 2) sourceC156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA156 + difference 2 5) (sourceB156 + difference 5 2) sourceC156) = raw4921 := by
      apply Matrix.ext; unfold tripleCharges sourceA156 sourceB156 sourceC156 difference raw4921; decide +kernel
    rw [ha]
    exact (canonical4921 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA156 + sourceB156) sourceC156) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA156 + sourceB156) sourceC156) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA156 sourceB156 sourceC156 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA156 sourceB156 sourceC156
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm156, Integer.Sparse.eval]
  linarith only [hs]

def sourceA157 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB157 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC157 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm157 : Integer.Sparse Master := [(Sum.inr 4401, 4), (Sum.inr 4405, 1), (Sum.inr 4428, 2), (Sum.inr 4460, 2), (Sum.inr 5000, 4), (Sum.inr 5021, 1), (Sum.inr 5047, 2), (Sum.inr 5075, 4), (Sum.inr 5171, 1), (Sum.inr 5259, 4), (Sum.inr 5275, 2), (Sum.inr 5293, 2), (Sum.inr 5491, 1)]

theorem sourceEq157 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm157 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA157 + difference 0 1) (sourceB157 + difference 1 0) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA157 + difference 0 1) (sourceB157 + difference 1 0) sourceC157) = raw2777 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw2777; decide +kernel
    rw [ha]
    exact (canonical2777 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA157 + difference 0 2) (sourceB157 + difference 2 0) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA157 + difference 0 2) (sourceB157 + difference 2 0) sourceC157) = raw2778 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw2778; decide +kernel
    rw [ha]
    exact (canonical2778 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA157 + difference 0 3) (sourceB157 + difference 3 0) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA157 + difference 0 3) (sourceB157 + difference 3 0) sourceC157) = raw2779 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw2779; decide +kernel
    rw [ha]
    exact (canonical2779 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA157 + difference 0 4) (sourceB157 + difference 4 0) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA157 + difference 0 4) (sourceB157 + difference 4 0) sourceC157) = raw2780 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw2780; decide +kernel
    rw [ha]
    exact (canonical2780 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA157 + difference 0 5) (sourceB157 + difference 5 0) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA157 + difference 0 5) (sourceB157 + difference 5 0) sourceC157) = raw4922 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4922; decide +kernel
    rw [ha]
    exact (canonical4922 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA157 + difference 1 0) (sourceB157 + difference 0 1) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA157 + difference 1 0) (sourceB157 + difference 0 1) sourceC157) = raw4923 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4923; decide +kernel
    rw [ha]
    exact (canonical4923 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA157 + difference 1 2) (sourceB157 + difference 2 1) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA157 + difference 1 2) (sourceB157 + difference 2 1) sourceC157) = raw4924 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4924; decide +kernel
    rw [ha]
    exact (canonical4924 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA157 + difference 1 3) (sourceB157 + difference 3 1) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA157 + difference 1 3) (sourceB157 + difference 3 1) sourceC157) = raw4925 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4925; decide +kernel
    rw [ha]
    exact (canonical4925 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA157 + difference 1 4) (sourceB157 + difference 4 1) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5021) := by
    have ha : (tripleCharges (sourceA157 + difference 1 4) (sourceB157 + difference 4 1) sourceC157) = raw4926 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4926; decide +kernel
    rw [ha]
    exact (canonical4926 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA157 + difference 1 5) (sourceB157 + difference 5 1) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA157 + difference 1 5) (sourceB157 + difference 5 1) sourceC157) = raw2756 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw2756; decide +kernel
    rw [ha]
    exact (canonical2756 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA157 + difference 2 0) (sourceB157 + difference 0 2) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA157 + difference 2 0) (sourceB157 + difference 0 2) sourceC157) = raw4927 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4927; decide +kernel
    rw [ha]
    exact (canonical4927 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA157 + difference 2 1) (sourceB157 + difference 1 2) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA157 + difference 2 1) (sourceB157 + difference 1 2) sourceC157) = raw4928 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4928; decide +kernel
    rw [ha]
    exact (canonical4928 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA157 + difference 2 3) (sourceB157 + difference 3 2) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5047) := by
    have ha : (tripleCharges (sourceA157 + difference 2 3) (sourceB157 + difference 3 2) sourceC157) = raw4929 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4929; decide +kernel
    rw [ha]
    exact (canonical4929 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA157 + difference 2 4) (sourceB157 + difference 4 2) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA157 + difference 2 4) (sourceB157 + difference 4 2) sourceC157) = raw4930 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4930; decide +kernel
    rw [ha]
    exact (canonical4930 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA157 + difference 2 5) (sourceB157 + difference 5 2) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA157 + difference 2 5) (sourceB157 + difference 5 2) sourceC157) = raw2761 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw2761; decide +kernel
    rw [ha]
    exact (canonical2761 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA157 + difference 3 0) (sourceB157 + difference 0 3) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA157 + difference 3 0) (sourceB157 + difference 0 3) sourceC157) = raw4931 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4931; decide +kernel
    rw [ha]
    exact (canonical4931 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA157 + difference 3 1) (sourceB157 + difference 1 3) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA157 + difference 3 1) (sourceB157 + difference 1 3) sourceC157) = raw4932 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4932; decide +kernel
    rw [ha]
    exact (canonical4932 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA157 + difference 3 2) (sourceB157 + difference 2 3) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5047) := by
    have ha : (tripleCharges (sourceA157 + difference 3 2) (sourceB157 + difference 2 3) sourceC157) = raw4933 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4933; decide +kernel
    rw [ha]
    exact (canonical4933 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA157 + difference 3 4) (sourceB157 + difference 4 3) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA157 + difference 3 4) (sourceB157 + difference 4 3) sourceC157) = raw4934 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4934; decide +kernel
    rw [ha]
    exact (canonical4934 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA157 + difference 3 5) (sourceB157 + difference 5 3) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA157 + difference 3 5) (sourceB157 + difference 5 3) sourceC157) = raw2766 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw2766; decide +kernel
    rw [ha]
    exact (canonical2766 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA157 + difference 4 0) (sourceB157 + difference 0 4) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA157 + difference 4 0) (sourceB157 + difference 0 4) sourceC157) = raw4935 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4935; decide +kernel
    rw [ha]
    exact (canonical4935 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA157 + difference 4 1) (sourceB157 + difference 1 4) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA157 + difference 4 1) (sourceB157 + difference 1 4) sourceC157) = raw4936 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4936; decide +kernel
    rw [ha]
    exact (canonical4936 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA157 + difference 4 2) (sourceB157 + difference 2 4) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA157 + difference 4 2) (sourceB157 + difference 2 4) sourceC157) = raw4937 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4937; decide +kernel
    rw [ha]
    exact (canonical4937 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA157 + difference 4 3) (sourceB157 + difference 3 4) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA157 + difference 4 3) (sourceB157 + difference 3 4) sourceC157) = raw4938 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4938; decide +kernel
    rw [ha]
    exact (canonical4938 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA157 + difference 4 5) (sourceB157 + difference 5 4) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA157 + difference 4 5) (sourceB157 + difference 5 4) sourceC157) = raw2771 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw2771; decide +kernel
    rw [ha]
    exact (canonical2771 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA157 + difference 5 0) (sourceB157 + difference 0 5) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA157 + difference 5 0) (sourceB157 + difference 0 5) sourceC157) = raw4939 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4939; decide +kernel
    rw [ha]
    exact (canonical4939 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA157 + difference 5 1) (sourceB157 + difference 1 5) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA157 + difference 5 1) (sourceB157 + difference 1 5) sourceC157) = raw4940 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4940; decide +kernel
    rw [ha]
    exact (canonical4940 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA157 + difference 5 2) (sourceB157 + difference 2 5) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA157 + difference 5 2) (sourceB157 + difference 2 5) sourceC157) = raw4941 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4941; decide +kernel
    rw [ha]
    exact (canonical4941 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA157 + difference 5 3) (sourceB157 + difference 3 5) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA157 + difference 5 3) (sourceB157 + difference 3 5) sourceC157) = raw4942 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4942; decide +kernel
    rw [ha]
    exact (canonical4942 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA157 + difference 5 4) (sourceB157 + difference 4 5) sourceC157) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA157 + difference 5 4) (sourceB157 + difference 4 5) sourceC157) = raw4943 := by
      apply Matrix.ext; unfold tripleCharges sourceA157 sourceB157 sourceC157 difference raw4943; decide +kernel
    rw [ha]
    exact (canonical4943 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA157 sourceB157 sourceC157
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm157, Integer.Sparse.eval]
  linarith only [hs]

def sourceA158 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB158 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC158 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm158 : Integer.Sparse Master := [(Sum.inr 982, 4), (Sum.inr 986, 1), (Sum.inr 1009, 2), (Sum.inr 1043, 2), (Sum.inr 2385, 4), (Sum.inr 2407, 1), (Sum.inr 2449, 2), (Sum.inr 2482, 4), (Sum.inr 2598, 1), (Sum.inr 2723, 4), (Sum.inr 2743, 2), (Sum.inr 2767, 2), (Sum.inr 4014, 1)]

theorem sourceEq158 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm158 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA158 + difference 0 1) (sourceB158 + difference 1 0) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA158 + difference 0 1) (sourceB158 + difference 1 0) sourceC158) = raw2807 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw2807; decide +kernel
    rw [ha]
    exact (canonical2807 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA158 + difference 0 2) (sourceB158 + difference 2 0) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA158 + difference 0 2) (sourceB158 + difference 2 0) sourceC158) = raw2808 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw2808; decide +kernel
    rw [ha]
    exact (canonical2808 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA158 + difference 0 3) (sourceB158 + difference 3 0) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA158 + difference 0 3) (sourceB158 + difference 3 0) sourceC158) = raw2809 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw2809; decide +kernel
    rw [ha]
    exact (canonical2809 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA158 + difference 0 4) (sourceB158 + difference 4 0) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA158 + difference 0 4) (sourceB158 + difference 4 0) sourceC158) = raw2810 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw2810; decide +kernel
    rw [ha]
    exact (canonical2810 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA158 + difference 0 5) (sourceB158 + difference 5 0) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4014) := by
    have ha : (tripleCharges (sourceA158 + difference 0 5) (sourceB158 + difference 5 0) sourceC158) = raw4944 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4944; decide +kernel
    rw [ha]
    exact (canonical4944 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA158 + difference 1 0) (sourceB158 + difference 0 1) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA158 + difference 1 0) (sourceB158 + difference 0 1) sourceC158) = raw4945 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4945; decide +kernel
    rw [ha]
    exact (canonical4945 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA158 + difference 1 2) (sourceB158 + difference 2 1) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA158 + difference 1 2) (sourceB158 + difference 2 1) sourceC158) = raw4946 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4946; decide +kernel
    rw [ha]
    exact (canonical4946 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA158 + difference 1 3) (sourceB158 + difference 3 1) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA158 + difference 1 3) (sourceB158 + difference 3 1) sourceC158) = raw4947 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4947; decide +kernel
    rw [ha]
    exact (canonical4947 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA158 + difference 1 4) (sourceB158 + difference 4 1) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2407) := by
    have ha : (tripleCharges (sourceA158 + difference 1 4) (sourceB158 + difference 4 1) sourceC158) = raw4948 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4948; decide +kernel
    rw [ha]
    exact (canonical4948 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA158 + difference 1 5) (sourceB158 + difference 5 1) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA158 + difference 1 5) (sourceB158 + difference 5 1) sourceC158) = raw2786 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw2786; decide +kernel
    rw [ha]
    exact (canonical2786 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA158 + difference 2 0) (sourceB158 + difference 0 2) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA158 + difference 2 0) (sourceB158 + difference 0 2) sourceC158) = raw4949 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4949; decide +kernel
    rw [ha]
    exact (canonical4949 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA158 + difference 2 1) (sourceB158 + difference 1 2) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA158 + difference 2 1) (sourceB158 + difference 1 2) sourceC158) = raw4950 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4950; decide +kernel
    rw [ha]
    exact (canonical4950 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA158 + difference 2 3) (sourceB158 + difference 3 2) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2449) := by
    have ha : (tripleCharges (sourceA158 + difference 2 3) (sourceB158 + difference 3 2) sourceC158) = raw4951 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4951; decide +kernel
    rw [ha]
    exact (canonical4951 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA158 + difference 2 4) (sourceB158 + difference 4 2) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA158 + difference 2 4) (sourceB158 + difference 4 2) sourceC158) = raw4952 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4952; decide +kernel
    rw [ha]
    exact (canonical4952 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA158 + difference 2 5) (sourceB158 + difference 5 2) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA158 + difference 2 5) (sourceB158 + difference 5 2) sourceC158) = raw2791 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw2791; decide +kernel
    rw [ha]
    exact (canonical2791 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA158 + difference 3 0) (sourceB158 + difference 0 3) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA158 + difference 3 0) (sourceB158 + difference 0 3) sourceC158) = raw4953 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4953; decide +kernel
    rw [ha]
    exact (canonical4953 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA158 + difference 3 1) (sourceB158 + difference 1 3) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA158 + difference 3 1) (sourceB158 + difference 1 3) sourceC158) = raw4954 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4954; decide +kernel
    rw [ha]
    exact (canonical4954 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA158 + difference 3 2) (sourceB158 + difference 2 3) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2449) := by
    have ha : (tripleCharges (sourceA158 + difference 3 2) (sourceB158 + difference 2 3) sourceC158) = raw4955 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4955; decide +kernel
    rw [ha]
    exact (canonical4955 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA158 + difference 3 4) (sourceB158 + difference 4 3) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA158 + difference 3 4) (sourceB158 + difference 4 3) sourceC158) = raw4956 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4956; decide +kernel
    rw [ha]
    exact (canonical4956 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA158 + difference 3 5) (sourceB158 + difference 5 3) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA158 + difference 3 5) (sourceB158 + difference 5 3) sourceC158) = raw2796 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw2796; decide +kernel
    rw [ha]
    exact (canonical2796 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA158 + difference 4 0) (sourceB158 + difference 0 4) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA158 + difference 4 0) (sourceB158 + difference 0 4) sourceC158) = raw4957 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4957; decide +kernel
    rw [ha]
    exact (canonical4957 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA158 + difference 4 1) (sourceB158 + difference 1 4) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2598) := by
    have ha : (tripleCharges (sourceA158 + difference 4 1) (sourceB158 + difference 1 4) sourceC158) = raw4958 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4958; decide +kernel
    rw [ha]
    exact (canonical4958 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA158 + difference 4 2) (sourceB158 + difference 2 4) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA158 + difference 4 2) (sourceB158 + difference 2 4) sourceC158) = raw4959 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4959; decide +kernel
    rw [ha]
    exact (canonical4959 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA158 + difference 4 3) (sourceB158 + difference 3 4) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA158 + difference 4 3) (sourceB158 + difference 3 4) sourceC158) = raw4960 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4960; decide +kernel
    rw [ha]
    exact (canonical4960 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA158 + difference 4 5) (sourceB158 + difference 5 4) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA158 + difference 4 5) (sourceB158 + difference 5 4) sourceC158) = raw2801 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw2801; decide +kernel
    rw [ha]
    exact (canonical2801 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA158 + difference 5 0) (sourceB158 + difference 0 5) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 986) := by
    have ha : (tripleCharges (sourceA158 + difference 5 0) (sourceB158 + difference 0 5) sourceC158) = raw4961 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4961; decide +kernel
    rw [ha]
    exact (canonical4961 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA158 + difference 5 1) (sourceB158 + difference 1 5) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA158 + difference 5 1) (sourceB158 + difference 1 5) sourceC158) = raw4962 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4962; decide +kernel
    rw [ha]
    exact (canonical4962 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA158 + difference 5 2) (sourceB158 + difference 2 5) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA158 + difference 5 2) (sourceB158 + difference 2 5) sourceC158) = raw4963 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4963; decide +kernel
    rw [ha]
    exact (canonical4963 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA158 + difference 5 3) (sourceB158 + difference 3 5) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA158 + difference 5 3) (sourceB158 + difference 3 5) sourceC158) = raw4964 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4964; decide +kernel
    rw [ha]
    exact (canonical4964 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA158 + difference 5 4) (sourceB158 + difference 4 5) sourceC158) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA158 + difference 5 4) (sourceB158 + difference 4 5) sourceC158) = raw4965 := by
      apply Matrix.ext; unfold tripleCharges sourceA158 sourceB158 sourceC158 difference raw4965; decide +kernel
    rw [ha]
    exact (canonical4965 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA158 sourceB158 sourceC158
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm158, Integer.Sparse.eval]
  linarith only [hs]

def sourceA159 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB159 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC159 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm159 : Integer.Sparse Master := [(Sum.inr 4832, 4), (Sum.inr 4837, 1), (Sum.inr 4845, 2), (Sum.inr 4897, 2), (Sum.inr 5222, 4), (Sum.inr 5235, 1), (Sum.inr 5239, 2), (Sum.inr 5252, 4), (Sum.inr 5261, 5), (Sum.inr 5268, 2), (Sum.inr 5296, 2), (Sum.inr 5312, 1)]

theorem sourceEq159 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm159 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA159 + difference 0 1) (sourceB159 + difference 1 0) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA159 + difference 0 1) (sourceB159 + difference 1 0) sourceC159) = raw4966 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4966; decide +kernel
    rw [ha]
    exact (canonical4966 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA159 + difference 0 2) (sourceB159 + difference 2 0) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA159 + difference 0 2) (sourceB159 + difference 2 0) sourceC159) = raw4967 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4967; decide +kernel
    rw [ha]
    exact (canonical4967 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA159 + difference 0 3) (sourceB159 + difference 3 0) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA159 + difference 0 3) (sourceB159 + difference 3 0) sourceC159) = raw4968 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4968; decide +kernel
    rw [ha]
    exact (canonical4968 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA159 + difference 0 4) (sourceB159 + difference 4 0) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA159 + difference 0 4) (sourceB159 + difference 4 0) sourceC159) = raw4969 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4969; decide +kernel
    rw [ha]
    exact (canonical4969 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA159 + difference 0 5) (sourceB159 + difference 5 0) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA159 + difference 0 5) (sourceB159 + difference 5 0) sourceC159) = raw4970 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4970; decide +kernel
    rw [ha]
    exact (canonical4970 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA159 + difference 1 0) (sourceB159 + difference 0 1) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA159 + difference 1 0) (sourceB159 + difference 0 1) sourceC159) = raw4971 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4971; decide +kernel
    rw [ha]
    exact (canonical4971 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA159 + difference 1 2) (sourceB159 + difference 2 1) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA159 + difference 1 2) (sourceB159 + difference 2 1) sourceC159) = raw4972 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4972; decide +kernel
    rw [ha]
    exact (canonical4972 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA159 + difference 1 3) (sourceB159 + difference 3 1) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA159 + difference 1 3) (sourceB159 + difference 3 1) sourceC159) = raw4973 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4973; decide +kernel
    rw [ha]
    exact (canonical4973 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA159 + difference 1 4) (sourceB159 + difference 4 1) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5235) := by
    have ha : (tripleCharges (sourceA159 + difference 1 4) (sourceB159 + difference 4 1) sourceC159) = raw4974 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4974; decide +kernel
    rw [ha]
    exact (canonical4974 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA159 + difference 1 5) (sourceB159 + difference 5 1) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA159 + difference 1 5) (sourceB159 + difference 5 1) sourceC159) = raw4975 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4975; decide +kernel
    rw [ha]
    exact (canonical4975 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA159 + difference 2 0) (sourceB159 + difference 0 2) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA159 + difference 2 0) (sourceB159 + difference 0 2) sourceC159) = raw4976 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4976; decide +kernel
    rw [ha]
    exact (canonical4976 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA159 + difference 2 1) (sourceB159 + difference 1 2) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA159 + difference 2 1) (sourceB159 + difference 1 2) sourceC159) = raw4977 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4977; decide +kernel
    rw [ha]
    exact (canonical4977 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA159 + difference 2 3) (sourceB159 + difference 3 2) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5239) := by
    have ha : (tripleCharges (sourceA159 + difference 2 3) (sourceB159 + difference 3 2) sourceC159) = raw4978 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4978; decide +kernel
    rw [ha]
    exact (canonical4978 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA159 + difference 2 4) (sourceB159 + difference 4 2) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA159 + difference 2 4) (sourceB159 + difference 4 2) sourceC159) = raw4979 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4979; decide +kernel
    rw [ha]
    exact (canonical4979 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA159 + difference 2 5) (sourceB159 + difference 5 2) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA159 + difference 2 5) (sourceB159 + difference 5 2) sourceC159) = raw4980 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4980; decide +kernel
    rw [ha]
    exact (canonical4980 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA159 + difference 3 0) (sourceB159 + difference 0 3) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA159 + difference 3 0) (sourceB159 + difference 0 3) sourceC159) = raw4981 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4981; decide +kernel
    rw [ha]
    exact (canonical4981 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA159 + difference 3 1) (sourceB159 + difference 1 3) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA159 + difference 3 1) (sourceB159 + difference 1 3) sourceC159) = raw4982 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4982; decide +kernel
    rw [ha]
    exact (canonical4982 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA159 + difference 3 2) (sourceB159 + difference 2 3) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5239) := by
    have ha : (tripleCharges (sourceA159 + difference 3 2) (sourceB159 + difference 2 3) sourceC159) = raw4983 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4983; decide +kernel
    rw [ha]
    exact (canonical4983 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA159 + difference 3 4) (sourceB159 + difference 4 3) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA159 + difference 3 4) (sourceB159 + difference 4 3) sourceC159) = raw4984 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4984; decide +kernel
    rw [ha]
    exact (canonical4984 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA159 + difference 3 5) (sourceB159 + difference 5 3) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA159 + difference 3 5) (sourceB159 + difference 5 3) sourceC159) = raw4985 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4985; decide +kernel
    rw [ha]
    exact (canonical4985 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA159 + difference 4 0) (sourceB159 + difference 0 4) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA159 + difference 4 0) (sourceB159 + difference 0 4) sourceC159) = raw4986 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4986; decide +kernel
    rw [ha]
    exact (canonical4986 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA159 + difference 4 1) (sourceB159 + difference 1 4) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5312) := by
    have ha : (tripleCharges (sourceA159 + difference 4 1) (sourceB159 + difference 1 4) sourceC159) = raw4356 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4356; decide +kernel
    rw [ha]
    exact (canonical4356 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA159 + difference 4 2) (sourceB159 + difference 2 4) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA159 + difference 4 2) (sourceB159 + difference 2 4) sourceC159) = raw4987 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4987; decide +kernel
    rw [ha]
    exact (canonical4987 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA159 + difference 4 3) (sourceB159 + difference 3 4) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA159 + difference 4 3) (sourceB159 + difference 3 4) sourceC159) = raw4988 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4988; decide +kernel
    rw [ha]
    exact (canonical4988 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA159 + difference 4 5) (sourceB159 + difference 5 4) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA159 + difference 4 5) (sourceB159 + difference 5 4) sourceC159) = raw4349 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4349; decide +kernel
    rw [ha]
    exact (canonical4349 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA159 + difference 5 0) (sourceB159 + difference 0 5) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA159 + difference 5 0) (sourceB159 + difference 0 5) sourceC159) = raw4989 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4989; decide +kernel
    rw [ha]
    exact (canonical4989 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA159 + difference 5 1) (sourceB159 + difference 1 5) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA159 + difference 5 1) (sourceB159 + difference 1 5) sourceC159) = raw4990 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4990; decide +kernel
    rw [ha]
    exact (canonical4990 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA159 + difference 5 2) (sourceB159 + difference 2 5) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA159 + difference 5 2) (sourceB159 + difference 2 5) sourceC159) = raw4991 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4991; decide +kernel
    rw [ha]
    exact (canonical4991 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA159 + difference 5 3) (sourceB159 + difference 3 5) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA159 + difference 5 3) (sourceB159 + difference 3 5) sourceC159) = raw4992 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4992; decide +kernel
    rw [ha]
    exact (canonical4992 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA159 + difference 5 4) (sourceB159 + difference 4 5) sourceC159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA159 + difference 5 4) (sourceB159 + difference 4 5) sourceC159) = raw4993 := by
      apply Matrix.ext; unfold tripleCharges sourceA159 sourceB159 sourceC159 difference raw4993; decide +kernel
    rw [ha]
    exact (canonical4993 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA159 sourceB159 sourceC159
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm159, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
