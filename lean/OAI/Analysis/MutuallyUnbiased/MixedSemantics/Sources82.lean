import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical106
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical112
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical142
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical145
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical151
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical208
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical209
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical210
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical211
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical221
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical222
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical228
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical250
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical251
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical254
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical255
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical258
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical259
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical260
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical266
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical268
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical269
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical270
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical271
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical272
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical274
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical275
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical277
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical278
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical279
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical280
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical282
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical284
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical285
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical286
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical287
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical288
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical289
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical290
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical291

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2624 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2624 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC2624 : Charge := ![1, 2, 0, -2, 0, -1]
def sourceForm2624 : Integer.Sparse Master := [(Sum.inr 4940, 1), (Sum.inr 4944, 1), (Sum.inr 4946, 1), (Sum.inr 4951, 1), (Sum.inr 4964, 1), (Sum.inr 4965, 1), (Sum.inr 4966, 1), (Sum.inr 4977, 1), (Sum.inr 5044, 1), (Sum.inr 5090, 1), (Sum.inr 5102, 1), (Sum.inr 5199, 1), (Sum.inr 5207, 1), (Sum.inr 5335, 1), (Sum.inr 5338, 1), (Sum.inr 5359, 1), (Sum.inr 5361, 1), (Sum.inr 5365, 1), (Sum.inr 5367, 1), (Sum.inr 5368, 1), (Sum.inr 5370, 1), (Sum.inr 5371, 1), (Sum.inr 5395, 1), (Sum.inr 5410, 1), (Sum.inr 5411, 1), (Sum.inr 5413, 1), (Sum.inr 5446, 1), (Sum.inr 5468, 1), (Sum.inr 5473, 1), (Sum.inr 5475, 1)]

theorem sourceEq2624 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2624 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2624 + difference 0 1) (sourceB2624 + difference 1 0) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2624 + difference 0 1) (sourceB2624 + difference 1 0) sourceC2624) = raw36664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36664; decide +kernel
    rw [ha]
    exact (canonical36664 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2624 + difference 0 2) (sourceB2624 + difference 2 0) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA2624 + difference 0 2) (sourceB2624 + difference 2 0) sourceC2624) = raw36665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36665; decide +kernel
    rw [ha]
    exact (canonical36665 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2624 + difference 0 3) (sourceB2624 + difference 3 0) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA2624 + difference 0 3) (sourceB2624 + difference 3 0) sourceC2624) = raw36666 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36666; decide +kernel
    rw [ha]
    exact (canonical36666 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2624 + difference 0 4) (sourceB2624 + difference 4 0) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA2624 + difference 0 4) (sourceB2624 + difference 4 0) sourceC2624) = raw36667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36667; decide +kernel
    rw [ha]
    exact (canonical36667 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2624 + difference 0 5) (sourceB2624 + difference 5 0) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2624 + difference 0 5) (sourceB2624 + difference 5 0) sourceC2624) = raw36668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36668; decide +kernel
    rw [ha]
    exact (canonical36668 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2624 + difference 1 0) (sourceB2624 + difference 0 1) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA2624 + difference 1 0) (sourceB2624 + difference 0 1) sourceC2624) = raw36669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36669; decide +kernel
    rw [ha]
    exact (canonical36669 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2624 + difference 1 2) (sourceB2624 + difference 2 1) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5468) := by
    have ha : (tripleCharges (sourceA2624 + difference 1 2) (sourceB2624 + difference 2 1) sourceC2624) = raw36670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36670; decide +kernel
    rw [ha]
    exact (canonical36670 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2624 + difference 1 3) (sourceB2624 + difference 3 1) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA2624 + difference 1 3) (sourceB2624 + difference 3 1) sourceC2624) = raw36671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36671; decide +kernel
    rw [ha]
    exact (canonical36671 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2624 + difference 1 4) (sourceB2624 + difference 4 1) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5475) := by
    have ha : (tripleCharges (sourceA2624 + difference 1 4) (sourceB2624 + difference 4 1) sourceC2624) = raw36672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36672; decide +kernel
    rw [ha]
    exact (canonical36672 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2624 + difference 1 5) (sourceB2624 + difference 5 1) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2624 + difference 1 5) (sourceB2624 + difference 5 1) sourceC2624) = raw36673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36673; decide +kernel
    rw [ha]
    exact (canonical36673 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2624 + difference 2 0) (sourceB2624 + difference 0 2) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4964) := by
    have ha : (tripleCharges (sourceA2624 + difference 2 0) (sourceB2624 + difference 0 2) sourceC2624) = raw36674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36674; decide +kernel
    rw [ha]
    exact (canonical36674 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2624 + difference 2 1) (sourceB2624 + difference 1 2) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4940) := by
    have ha : (tripleCharges (sourceA2624 + difference 2 1) (sourceB2624 + difference 1 2) sourceC2624) = raw36675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36675; decide +kernel
    rw [ha]
    exact (canonical36675 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2624 + difference 2 3) (sourceB2624 + difference 3 2) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA2624 + difference 2 3) (sourceB2624 + difference 3 2) sourceC2624) = raw36676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36676; decide +kernel
    rw [ha]
    exact (canonical36676 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2624 + difference 2 4) (sourceB2624 + difference 4 2) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2624 + difference 2 4) (sourceB2624 + difference 4 2) sourceC2624) = raw36677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36677; decide +kernel
    rw [ha]
    exact (canonical36677 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2624 + difference 2 5) (sourceB2624 + difference 5 2) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA2624 + difference 2 5) (sourceB2624 + difference 5 2) sourceC2624) = raw36678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36678; decide +kernel
    rw [ha]
    exact (canonical36678 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2624 + difference 3 0) (sourceB2624 + difference 0 3) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2624 + difference 3 0) (sourceB2624 + difference 0 3) sourceC2624) = raw36679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36679; decide +kernel
    rw [ha]
    exact (canonical36679 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2624 + difference 3 1) (sourceB2624 + difference 1 3) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2624 + difference 3 1) (sourceB2624 + difference 1 3) sourceC2624) = raw36680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36680; decide +kernel
    rw [ha]
    exact (canonical36680 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2624 + difference 3 2) (sourceB2624 + difference 2 3) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2624 + difference 3 2) (sourceB2624 + difference 2 3) sourceC2624) = raw36681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36681; decide +kernel
    rw [ha]
    exact (canonical36681 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2624 + difference 3 4) (sourceB2624 + difference 4 3) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2624 + difference 3 4) (sourceB2624 + difference 4 3) sourceC2624) = raw36682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36682; decide +kernel
    rw [ha]
    exact (canonical36682 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2624 + difference 3 5) (sourceB2624 + difference 5 3) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2624 + difference 3 5) (sourceB2624 + difference 5 3) sourceC2624) = raw36683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36683; decide +kernel
    rw [ha]
    exact (canonical36683 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2624 + difference 4 0) (sourceB2624 + difference 0 4) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4966) := by
    have ha : (tripleCharges (sourceA2624 + difference 4 0) (sourceB2624 + difference 0 4) sourceC2624) = raw36684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36684; decide +kernel
    rw [ha]
    exact (canonical36684 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2624 + difference 4 1) (sourceB2624 + difference 1 4) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4951) := by
    have ha : (tripleCharges (sourceA2624 + difference 4 1) (sourceB2624 + difference 1 4) sourceC2624) = raw36685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36685; decide +kernel
    rw [ha]
    exact (canonical36685 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2624 + difference 4 2) (sourceB2624 + difference 2 4) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5338) := by
    have ha : (tripleCharges (sourceA2624 + difference 4 2) (sourceB2624 + difference 2 4) sourceC2624) = raw36686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36686; decide +kernel
    rw [ha]
    exact (canonical36686 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2624 + difference 4 3) (sourceB2624 + difference 3 4) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5361) := by
    have ha : (tripleCharges (sourceA2624 + difference 4 3) (sourceB2624 + difference 3 4) sourceC2624) = raw36687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36687; decide +kernel
    rw [ha]
    exact (canonical36687 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2624 + difference 4 5) (sourceB2624 + difference 5 4) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2624 + difference 4 5) (sourceB2624 + difference 5 4) sourceC2624) = raw36688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36688; decide +kernel
    rw [ha]
    exact (canonical36688 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2624 + difference 5 0) (sourceB2624 + difference 0 5) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4965) := by
    have ha : (tripleCharges (sourceA2624 + difference 5 0) (sourceB2624 + difference 0 5) sourceC2624) = raw36689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36689; decide +kernel
    rw [ha]
    exact (canonical36689 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2624 + difference 5 1) (sourceB2624 + difference 1 5) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA2624 + difference 5 1) (sourceB2624 + difference 1 5) sourceC2624) = raw36690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36690; decide +kernel
    rw [ha]
    exact (canonical36690 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2624 + difference 5 2) (sourceB2624 + difference 2 5) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5044) := by
    have ha : (tripleCharges (sourceA2624 + difference 5 2) (sourceB2624 + difference 2 5) sourceC2624) = raw36691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36691; decide +kernel
    rw [ha]
    exact (canonical36691 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2624 + difference 5 3) (sourceB2624 + difference 3 5) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA2624 + difference 5 3) (sourceB2624 + difference 3 5) sourceC2624) = raw36692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36692; decide +kernel
    rw [ha]
    exact (canonical36692 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2624 + difference 5 4) (sourceB2624 + difference 4 5) sourceC2624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2624 + difference 5 4) (sourceB2624 + difference 4 5) sourceC2624) = raw36693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2624 sourceB2624 sourceC2624 difference raw36693; decide +kernel
    rw [ha]
    exact (canonical36693 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2624 sourceB2624 sourceC2624
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2624, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2625 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2625 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC2625 : Charge := ![1, 2, 0, -2, 0, -1]
def sourceForm2625 : Integer.Sparse Master := [(Sum.inr 3405, 1), (Sum.inr 3412, 1), (Sum.inr 3413, 1), (Sum.inr 3418, 1), (Sum.inr 3471, 1), (Sum.inr 3474, 1), (Sum.inr 3475, 1), (Sum.inr 3480, 1), (Sum.inr 3554, 1), (Sum.inr 3555, 1), (Sum.inr 3578, 1), (Sum.inr 3595, 1), (Sum.inr 3631, 1), (Sum.inr 3753, 1), (Sum.inr 3755, 1), (Sum.inr 3758, 1), (Sum.inr 3759, 1), (Sum.inr 3766, 1), (Sum.inr 3767, 1), (Sum.inr 3771, 1), (Sum.inr 3772, 1), (Sum.inr 3775, 1), (Sum.inr 3794, 1), (Sum.inr 3808, 1), (Sum.inr 3809, 1), (Sum.inr 3817, 1), (Sum.inr 3950, 1), (Sum.inr 3958, 1), (Sum.inr 3959, 1), (Sum.inr 3963, 1)]

theorem sourceEq2625 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2625 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2625 + difference 0 1) (sourceB2625 + difference 1 0) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA2625 + difference 0 1) (sourceB2625 + difference 1 0) sourceC2625) = raw36694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36694; decide +kernel
    rw [ha]
    exact (canonical36694 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2625 + difference 0 2) (sourceB2625 + difference 2 0) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA2625 + difference 0 2) (sourceB2625 + difference 2 0) sourceC2625) = raw36695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36695; decide +kernel
    rw [ha]
    exact (canonical36695 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2625 + difference 0 3) (sourceB2625 + difference 3 0) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA2625 + difference 0 3) (sourceB2625 + difference 3 0) sourceC2625) = raw36696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36696; decide +kernel
    rw [ha]
    exact (canonical36696 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2625 + difference 0 4) (sourceB2625 + difference 4 0) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA2625 + difference 0 4) (sourceB2625 + difference 4 0) sourceC2625) = raw36697 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36697; decide +kernel
    rw [ha]
    exact (canonical36697 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2625 + difference 0 5) (sourceB2625 + difference 5 0) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA2625 + difference 0 5) (sourceB2625 + difference 5 0) sourceC2625) = raw36698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36698; decide +kernel
    rw [ha]
    exact (canonical36698 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2625 + difference 1 0) (sourceB2625 + difference 0 1) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA2625 + difference 1 0) (sourceB2625 + difference 0 1) sourceC2625) = raw36699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36699; decide +kernel
    rw [ha]
    exact (canonical36699 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2625 + difference 1 2) (sourceB2625 + difference 2 1) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3950) := by
    have ha : (tripleCharges (sourceA2625 + difference 1 2) (sourceB2625 + difference 2 1) sourceC2625) = raw36700 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36700; decide +kernel
    rw [ha]
    exact (canonical36700 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2625 + difference 1 3) (sourceB2625 + difference 3 1) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA2625 + difference 1 3) (sourceB2625 + difference 3 1) sourceC2625) = raw36701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36701; decide +kernel
    rw [ha]
    exact (canonical36701 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2625 + difference 1 4) (sourceB2625 + difference 4 1) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA2625 + difference 1 4) (sourceB2625 + difference 4 1) sourceC2625) = raw36702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36702; decide +kernel
    rw [ha]
    exact (canonical36702 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2625 + difference 1 5) (sourceB2625 + difference 5 1) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA2625 + difference 1 5) (sourceB2625 + difference 5 1) sourceC2625) = raw36703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36703; decide +kernel
    rw [ha]
    exact (canonical36703 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2625 + difference 2 0) (sourceB2625 + difference 0 2) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3554) := by
    have ha : (tripleCharges (sourceA2625 + difference 2 0) (sourceB2625 + difference 0 2) sourceC2625) = raw36704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36704; decide +kernel
    rw [ha]
    exact (canonical36704 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2625 + difference 2 1) (sourceB2625 + difference 1 2) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3405) := by
    have ha : (tripleCharges (sourceA2625 + difference 2 1) (sourceB2625 + difference 1 2) sourceC2625) = raw36705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36705; decide +kernel
    rw [ha]
    exact (canonical36705 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2625 + difference 2 3) (sourceB2625 + difference 3 2) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3759) := by
    have ha : (tripleCharges (sourceA2625 + difference 2 3) (sourceB2625 + difference 3 2) sourceC2625) = raw36706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36706; decide +kernel
    rw [ha]
    exact (canonical36706 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2625 + difference 2 4) (sourceB2625 + difference 4 2) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2625 + difference 2 4) (sourceB2625 + difference 4 2) sourceC2625) = raw36707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36707; decide +kernel
    rw [ha]
    exact (canonical36707 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2625 + difference 2 5) (sourceB2625 + difference 5 2) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA2625 + difference 2 5) (sourceB2625 + difference 5 2) sourceC2625) = raw36708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36708; decide +kernel
    rw [ha]
    exact (canonical36708 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2625 + difference 3 0) (sourceB2625 + difference 0 3) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2625 + difference 3 0) (sourceB2625 + difference 0 3) sourceC2625) = raw36709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36709; decide +kernel
    rw [ha]
    exact (canonical36709 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2625 + difference 3 1) (sourceB2625 + difference 1 3) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2625 + difference 3 1) (sourceB2625 + difference 1 3) sourceC2625) = raw36710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36710; decide +kernel
    rw [ha]
    exact (canonical36710 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2625 + difference 3 2) (sourceB2625 + difference 2 3) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3753) := by
    have ha : (tripleCharges (sourceA2625 + difference 3 2) (sourceB2625 + difference 2 3) sourceC2625) = raw36711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36711; decide +kernel
    rw [ha]
    exact (canonical36711 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2625 + difference 3 4) (sourceB2625 + difference 4 3) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3775) := by
    have ha : (tripleCharges (sourceA2625 + difference 3 4) (sourceB2625 + difference 4 3) sourceC2625) = raw36712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36712; decide +kernel
    rw [ha]
    exact (canonical36712 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2625 + difference 3 5) (sourceB2625 + difference 5 3) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2625 + difference 3 5) (sourceB2625 + difference 5 3) sourceC2625) = raw36713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36713; decide +kernel
    rw [ha]
    exact (canonical36713 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2625 + difference 4 0) (sourceB2625 + difference 0 4) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3555) := by
    have ha : (tripleCharges (sourceA2625 + difference 4 0) (sourceB2625 + difference 0 4) sourceC2625) = raw36714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36714; decide +kernel
    rw [ha]
    exact (canonical36714 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2625 + difference 4 1) (sourceB2625 + difference 1 4) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2625 + difference 4 1) (sourceB2625 + difference 1 4) sourceC2625) = raw36715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36715; decide +kernel
    rw [ha]
    exact (canonical36715 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2625 + difference 4 2) (sourceB2625 + difference 2 4) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3755) := by
    have ha : (tripleCharges (sourceA2625 + difference 4 2) (sourceB2625 + difference 2 4) sourceC2625) = raw36716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36716; decide +kernel
    rw [ha]
    exact (canonical36716 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2625 + difference 4 3) (sourceB2625 + difference 3 4) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3772) := by
    have ha : (tripleCharges (sourceA2625 + difference 4 3) (sourceB2625 + difference 3 4) sourceC2625) = raw36717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36717; decide +kernel
    rw [ha]
    exact (canonical36717 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2625 + difference 4 5) (sourceB2625 + difference 5 4) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3771) := by
    have ha : (tripleCharges (sourceA2625 + difference 4 5) (sourceB2625 + difference 5 4) sourceC2625) = raw36718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36718; decide +kernel
    rw [ha]
    exact (canonical36718 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2625 + difference 5 0) (sourceB2625 + difference 0 5) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3475) := by
    have ha : (tripleCharges (sourceA2625 + difference 5 0) (sourceB2625 + difference 0 5) sourceC2625) = raw36719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36719; decide +kernel
    rw [ha]
    exact (canonical36719 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2625 + difference 5 1) (sourceB2625 + difference 1 5) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2625 + difference 5 1) (sourceB2625 + difference 1 5) sourceC2625) = raw36720 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36720; decide +kernel
    rw [ha]
    exact (canonical36720 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2625 + difference 5 2) (sourceB2625 + difference 2 5) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3474) := by
    have ha : (tripleCharges (sourceA2625 + difference 5 2) (sourceB2625 + difference 2 5) sourceC2625) = raw36721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36721; decide +kernel
    rw [ha]
    exact (canonical36721 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2625 + difference 5 3) (sourceB2625 + difference 3 5) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2625 + difference 5 3) (sourceB2625 + difference 3 5) sourceC2625) = raw36722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36722; decide +kernel
    rw [ha]
    exact (canonical36722 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2625 + difference 5 4) (sourceB2625 + difference 4 5) sourceC2625) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA2625 + difference 5 4) (sourceB2625 + difference 4 5) sourceC2625) = raw36723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2625 sourceB2625 sourceC2625 difference raw36723; decide +kernel
    rw [ha]
    exact (canonical36723 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2625 sourceB2625 sourceC2625
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2625, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2626 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2626 : Charge := ![1, 2, 0, -2, 0, -1]
def sourceC2626 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceForm2626 : Integer.Sparse Master := [(Sum.inr 4642, 1), (Sum.inr 4644, 1), (Sum.inr 4645, 1), (Sum.inr 4654, 1), (Sum.inr 4835, 1), (Sum.inr 4912, 1), (Sum.inr 4913, 1), (Sum.inr 4914, 1), (Sum.inr 4923, 1), (Sum.inr 4987, 1), (Sum.inr 4990, 1), (Sum.inr 5003, 1), (Sum.inr 5015, 1), (Sum.inr 5102, 1), (Sum.inr 5141, 1), (Sum.inr 5248, 1), (Sum.inr 5334, 1), (Sum.inr 5346, 1), (Sum.inr 5352, 1), (Sum.inr 5356, 1), (Sum.inr 5365, 1), (Sum.inr 5368, 1), (Sum.inr 5395, 1), (Sum.inr 5428, 1), (Sum.inr 5434, 1), (Sum.inr 5439, 1), (Sum.inr 5469, 1), (Sum.inr 5473, 1), (Sum.inr 5483, 1), (Sum.inr 5485, 1)]

theorem sourceEq2626 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2626 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2626 + difference 0 1) (sourceB2626 + difference 1 0) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2626 + difference 0 1) (sourceB2626 + difference 1 0) sourceC2626) = raw36724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36724; decide +kernel
    rw [ha]
    exact (canonical36724 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2626 + difference 0 2) (sourceB2626 + difference 2 0) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA2626 + difference 0 2) (sourceB2626 + difference 2 0) sourceC2626) = raw36725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36725; decide +kernel
    rw [ha]
    exact (canonical36725 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2626 + difference 0 3) (sourceB2626 + difference 3 0) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2626 + difference 0 3) (sourceB2626 + difference 3 0) sourceC2626) = raw36726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36726; decide +kernel
    rw [ha]
    exact (canonical36726 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2626 + difference 0 4) (sourceB2626 + difference 4 0) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA2626 + difference 0 4) (sourceB2626 + difference 4 0) sourceC2626) = raw36727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36727; decide +kernel
    rw [ha]
    exact (canonical36727 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2626 + difference 0 5) (sourceB2626 + difference 5 0) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2626 + difference 0 5) (sourceB2626 + difference 5 0) sourceC2626) = raw36728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36728; decide +kernel
    rw [ha]
    exact (canonical36728 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2626 + difference 1 0) (sourceB2626 + difference 0 1) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2626 + difference 1 0) (sourceB2626 + difference 0 1) sourceC2626) = raw7876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw7876; decide +kernel
    rw [ha]
    exact (canonical7876 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2626 + difference 1 2) (sourceB2626 + difference 2 1) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA2626 + difference 1 2) (sourceB2626 + difference 2 1) sourceC2626) = raw33270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw33270; decide +kernel
    rw [ha]
    exact (canonical33270 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2626 + difference 1 3) (sourceB2626 + difference 3 1) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2626 + difference 1 3) (sourceB2626 + difference 3 1) sourceC2626) = raw3257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw3257; decide +kernel
    rw [ha]
    exact (canonical3257 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2626 + difference 1 4) (sourceB2626 + difference 4 1) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2626 + difference 1 4) (sourceB2626 + difference 4 1) sourceC2626) = raw33271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw33271; decide +kernel
    rw [ha]
    exact (canonical33271 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2626 + difference 1 5) (sourceB2626 + difference 5 1) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2626 + difference 1 5) (sourceB2626 + difference 5 1) sourceC2626) = raw3247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw3247; decide +kernel
    rw [ha]
    exact (canonical3247 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2626 + difference 2 0) (sourceB2626 + difference 0 2) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4912) := by
    have ha : (tripleCharges (sourceA2626 + difference 2 0) (sourceB2626 + difference 0 2) sourceC2626) = raw33272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw33272; decide +kernel
    rw [ha]
    exact (canonical33272 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2626 + difference 2 1) (sourceB2626 + difference 1 2) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4642) := by
    have ha : (tripleCharges (sourceA2626 + difference 2 1) (sourceB2626 + difference 1 2) sourceC2626) = raw36729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36729; decide +kernel
    rw [ha]
    exact (canonical36729 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2626 + difference 2 3) (sourceB2626 + difference 3 2) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2626 + difference 2 3) (sourceB2626 + difference 3 2) sourceC2626) = raw36730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36730; decide +kernel
    rw [ha]
    exact (canonical36730 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2626 + difference 2 4) (sourceB2626 + difference 4 2) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2626 + difference 2 4) (sourceB2626 + difference 4 2) sourceC2626) = raw36731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36731; decide +kernel
    rw [ha]
    exact (canonical36731 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2626 + difference 2 5) (sourceB2626 + difference 5 2) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA2626 + difference 2 5) (sourceB2626 + difference 5 2) sourceC2626) = raw36732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36732; decide +kernel
    rw [ha]
    exact (canonical36732 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2626 + difference 3 0) (sourceB2626 + difference 0 3) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4914) := by
    have ha : (tripleCharges (sourceA2626 + difference 3 0) (sourceB2626 + difference 0 3) sourceC2626) = raw33275 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw33275; decide +kernel
    rw [ha]
    exact (canonical33275 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2626 + difference 3 1) (sourceB2626 + difference 1 3) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4645) := by
    have ha : (tripleCharges (sourceA2626 + difference 3 1) (sourceB2626 + difference 1 3) sourceC2626) = raw36733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36733; decide +kernel
    rw [ha]
    exact (canonical36733 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2626 + difference 3 2) (sourceB2626 + difference 2 3) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4990) := by
    have ha : (tripleCharges (sourceA2626 + difference 3 2) (sourceB2626 + difference 2 3) sourceC2626) = raw36734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36734; decide +kernel
    rw [ha]
    exact (canonical36734 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2626 + difference 3 4) (sourceB2626 + difference 4 3) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2626 + difference 3 4) (sourceB2626 + difference 4 3) sourceC2626) = raw36735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36735; decide +kernel
    rw [ha]
    exact (canonical36735 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2626 + difference 3 5) (sourceB2626 + difference 5 3) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2626 + difference 3 5) (sourceB2626 + difference 5 3) sourceC2626) = raw36736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36736; decide +kernel
    rw [ha]
    exact (canonical36736 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2626 + difference 4 0) (sourceB2626 + difference 0 4) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4923) := by
    have ha : (tripleCharges (sourceA2626 + difference 4 0) (sourceB2626 + difference 0 4) sourceC2626) = raw33279 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw33279; decide +kernel
    rw [ha]
    exact (canonical33279 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2626 + difference 4 1) (sourceB2626 + difference 1 4) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4654) := by
    have ha : (tripleCharges (sourceA2626 + difference 4 1) (sourceB2626 + difference 1 4) sourceC2626) = raw36737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36737; decide +kernel
    rw [ha]
    exact (canonical36737 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2626 + difference 4 2) (sourceB2626 + difference 2 4) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5334) := by
    have ha : (tripleCharges (sourceA2626 + difference 4 2) (sourceB2626 + difference 2 4) sourceC2626) = raw36738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36738; decide +kernel
    rw [ha]
    exact (canonical36738 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2626 + difference 4 3) (sourceB2626 + difference 3 4) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2626 + difference 4 3) (sourceB2626 + difference 3 4) sourceC2626) = raw36739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36739; decide +kernel
    rw [ha]
    exact (canonical36739 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2626 + difference 4 5) (sourceB2626 + difference 5 4) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2626 + difference 4 5) (sourceB2626 + difference 5 4) sourceC2626) = raw36740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36740; decide +kernel
    rw [ha]
    exact (canonical36740 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2626 + difference 5 0) (sourceB2626 + difference 0 5) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2626 + difference 5 0) (sourceB2626 + difference 0 5) sourceC2626) = raw33282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw33282; decide +kernel
    rw [ha]
    exact (canonical33282 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2626 + difference 5 1) (sourceB2626 + difference 1 5) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4644) := by
    have ha : (tripleCharges (sourceA2626 + difference 5 1) (sourceB2626 + difference 1 5) sourceC2626) = raw36741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36741; decide +kernel
    rw [ha]
    exact (canonical36741 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2626 + difference 5 2) (sourceB2626 + difference 2 5) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4987) := by
    have ha : (tripleCharges (sourceA2626 + difference 5 2) (sourceB2626 + difference 2 5) sourceC2626) = raw36742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36742; decide +kernel
    rw [ha]
    exact (canonical36742 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2626 + difference 5 3) (sourceB2626 + difference 3 5) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2626 + difference 5 3) (sourceB2626 + difference 3 5) sourceC2626) = raw36743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36743; decide +kernel
    rw [ha]
    exact (canonical36743 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2626 + difference 5 4) (sourceB2626 + difference 4 5) sourceC2626) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2626 + difference 5 4) (sourceB2626 + difference 4 5) sourceC2626) = raw36744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2626 sourceB2626 sourceC2626 difference raw36744; decide +kernel
    rw [ha]
    exact (canonical36744 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2626 sourceB2626 sourceC2626
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2626, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2627 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2627 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC2627 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceForm2627 : Integer.Sparse Master := [(Sum.inr 4091, 1), (Sum.inr 4941, 1), (Sum.inr 4948, 1), (Sum.inr 4950, 2), (Sum.inr 4968, 1), (Sum.inr 4970, 1), (Sum.inr 4974, 2), (Sum.inr 5104, 1), (Sum.inr 5117, 1), (Sum.inr 5152, 2), (Sum.inr 5203, 1), (Sum.inr 5337, 2), (Sum.inr 5352, 2), (Sum.inr 5356, 2), (Sum.inr 5366, 1), (Sum.inr 5369, 2), (Sum.inr 5396, 1), (Sum.inr 5410, 2), (Sum.inr 5469, 1), (Sum.inr 5473, 2), (Sum.inr 5474, 1)]

theorem sourceEq2627 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2627 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2627 + difference 0 1) (sourceB2627 + difference 1 0) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2627 + difference 0 1) (sourceB2627 + difference 1 0) sourceC2627) = raw36745 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36745; decide +kernel
    rw [ha]
    exact (canonical36745 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2627 + difference 0 2) (sourceB2627 + difference 2 0) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA2627 + difference 0 2) (sourceB2627 + difference 2 0) sourceC2627) = raw36746 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36746; decide +kernel
    rw [ha]
    exact (canonical36746 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2627 + difference 0 3) (sourceB2627 + difference 3 0) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2627 + difference 0 3) (sourceB2627 + difference 3 0) sourceC2627) = raw36747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36747; decide +kernel
    rw [ha]
    exact (canonical36747 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2627 + difference 0 4) (sourceB2627 + difference 4 0) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2627 + difference 0 4) (sourceB2627 + difference 4 0) sourceC2627) = raw36748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36748; decide +kernel
    rw [ha]
    exact (canonical36748 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2627 + difference 0 5) (sourceB2627 + difference 5 0) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2627 + difference 0 5) (sourceB2627 + difference 5 0) sourceC2627) = raw36749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36749; decide +kernel
    rw [ha]
    exact (canonical36749 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2627 + difference 1 0) (sourceB2627 + difference 0 1) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2627 + difference 1 0) (sourceB2627 + difference 0 1) sourceC2627) = raw36750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36750; decide +kernel
    rw [ha]
    exact (canonical36750 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2627 + difference 1 2) (sourceB2627 + difference 2 1) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA2627 + difference 1 2) (sourceB2627 + difference 2 1) sourceC2627) = raw32568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw32568; decide +kernel
    rw [ha]
    exact (canonical32568 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2627 + difference 1 3) (sourceB2627 + difference 3 1) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2627 + difference 1 3) (sourceB2627 + difference 3 1) sourceC2627) = raw32569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw32569; decide +kernel
    rw [ha]
    exact (canonical32569 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2627 + difference 1 4) (sourceB2627 + difference 4 1) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2627 + difference 1 4) (sourceB2627 + difference 4 1) sourceC2627) = raw32570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw32570; decide +kernel
    rw [ha]
    exact (canonical32570 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2627 + difference 1 5) (sourceB2627 + difference 5 1) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5474) := by
    have ha : (tripleCharges (sourceA2627 + difference 1 5) (sourceB2627 + difference 5 1) sourceC2627) = raw32571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw32571; decide +kernel
    rw [ha]
    exact (canonical32571 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2627 + difference 2 0) (sourceB2627 + difference 0 2) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4968) := by
    have ha : (tripleCharges (sourceA2627 + difference 2 0) (sourceB2627 + difference 0 2) sourceC2627) = raw32578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw32578; decide +kernel
    rw [ha]
    exact (canonical32578 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2627 + difference 2 1) (sourceB2627 + difference 1 2) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2627 + difference 2 1) (sourceB2627 + difference 1 2) sourceC2627) = raw36751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36751; decide +kernel
    rw [ha]
    exact (canonical36751 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2627 + difference 2 3) (sourceB2627 + difference 3 2) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2627 + difference 2 3) (sourceB2627 + difference 3 2) sourceC2627) = raw36752 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36752; decide +kernel
    rw [ha]
    exact (canonical36752 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2627 + difference 2 4) (sourceB2627 + difference 4 2) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2627 + difference 2 4) (sourceB2627 + difference 4 2) sourceC2627) = raw36753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36753; decide +kernel
    rw [ha]
    exact (canonical36753 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2627 + difference 2 5) (sourceB2627 + difference 5 2) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5366) := by
    have ha : (tripleCharges (sourceA2627 + difference 2 5) (sourceB2627 + difference 5 2) sourceC2627) = raw36754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36754; decide +kernel
    rw [ha]
    exact (canonical36754 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2627 + difference 3 0) (sourceB2627 + difference 0 3) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4974) := by
    have ha : (tripleCharges (sourceA2627 + difference 3 0) (sourceB2627 + difference 0 3) sourceC2627) = raw32583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw32583; decide +kernel
    rw [ha]
    exact (canonical32583 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2627 + difference 3 1) (sourceB2627 + difference 1 3) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2627 + difference 3 1) (sourceB2627 + difference 1 3) sourceC2627) = raw36755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36755; decide +kernel
    rw [ha]
    exact (canonical36755 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2627 + difference 3 2) (sourceB2627 + difference 2 3) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5337) := by
    have ha : (tripleCharges (sourceA2627 + difference 3 2) (sourceB2627 + difference 2 3) sourceC2627) = raw36756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36756; decide +kernel
    rw [ha]
    exact (canonical36756 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2627 + difference 3 4) (sourceB2627 + difference 4 3) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2627 + difference 3 4) (sourceB2627 + difference 4 3) sourceC2627) = raw36757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36757; decide +kernel
    rw [ha]
    exact (canonical36757 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2627 + difference 3 5) (sourceB2627 + difference 5 3) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2627 + difference 3 5) (sourceB2627 + difference 5 3) sourceC2627) = raw36758 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36758; decide +kernel
    rw [ha]
    exact (canonical36758 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2627 + difference 4 0) (sourceB2627 + difference 0 4) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4974) := by
    have ha : (tripleCharges (sourceA2627 + difference 4 0) (sourceB2627 + difference 0 4) sourceC2627) = raw32588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw32588; decide +kernel
    rw [ha]
    exact (canonical32588 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2627 + difference 4 1) (sourceB2627 + difference 1 4) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2627 + difference 4 1) (sourceB2627 + difference 1 4) sourceC2627) = raw36759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36759; decide +kernel
    rw [ha]
    exact (canonical36759 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2627 + difference 4 2) (sourceB2627 + difference 2 4) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5337) := by
    have ha : (tripleCharges (sourceA2627 + difference 4 2) (sourceB2627 + difference 2 4) sourceC2627) = raw36760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36760; decide +kernel
    rw [ha]
    exact (canonical36760 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2627 + difference 4 3) (sourceB2627 + difference 3 4) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2627 + difference 4 3) (sourceB2627 + difference 3 4) sourceC2627) = raw36761 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36761; decide +kernel
    rw [ha]
    exact (canonical36761 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2627 + difference 4 5) (sourceB2627 + difference 5 4) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2627 + difference 4 5) (sourceB2627 + difference 5 4) sourceC2627) = raw36762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36762; decide +kernel
    rw [ha]
    exact (canonical36762 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2627 + difference 5 0) (sourceB2627 + difference 0 5) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4970) := by
    have ha : (tripleCharges (sourceA2627 + difference 5 0) (sourceB2627 + difference 0 5) sourceC2627) = raw32593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw32593; decide +kernel
    rw [ha]
    exact (canonical32593 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2627 + difference 5 1) (sourceB2627 + difference 1 5) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4948) := by
    have ha : (tripleCharges (sourceA2627 + difference 5 1) (sourceB2627 + difference 1 5) sourceC2627) = raw36763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36763; decide +kernel
    rw [ha]
    exact (canonical36763 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2627 + difference 5 2) (sourceB2627 + difference 2 5) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5117) := by
    have ha : (tripleCharges (sourceA2627 + difference 5 2) (sourceB2627 + difference 2 5) sourceC2627) = raw36764 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36764; decide +kernel
    rw [ha]
    exact (canonical36764 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2627 + difference 5 3) (sourceB2627 + difference 3 5) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2627 + difference 5 3) (sourceB2627 + difference 3 5) sourceC2627) = raw36765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36765; decide +kernel
    rw [ha]
    exact (canonical36765 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2627 + difference 5 4) (sourceB2627 + difference 4 5) sourceC2627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2627 + difference 5 4) (sourceB2627 + difference 4 5) sourceC2627) = raw36766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2627 sourceB2627 sourceC2627 difference raw36766; decide +kernel
    rw [ha]
    exact (canonical36766 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2627 sourceB2627 sourceC2627
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2627, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2628 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2628 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC2628 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceForm2628 : Integer.Sparse Master := [(Sum.inr 4092, 1), (Sum.inr 4939, 1), (Sum.inr 4943, 1), (Sum.inr 4946, 1), (Sum.inr 4949, 1), (Sum.inr 4971, 1), (Sum.inr 4972, 1), (Sum.inr 4973, 1), (Sum.inr 4977, 1), (Sum.inr 5036, 1), (Sum.inr 5101, 1), (Sum.inr 5111, 1), (Sum.inr 5141, 1), (Sum.inr 5204, 1), (Sum.inr 5335, 1), (Sum.inr 5336, 1), (Sum.inr 5351, 1), (Sum.inr 5355, 1), (Sum.inr 5365, 1), (Sum.inr 5367, 1), (Sum.inr 5368, 1), (Sum.inr 5370, 1), (Sum.inr 5371, 1), (Sum.inr 5394, 1), (Sum.inr 5395, 1), (Sum.inr 5409, 1), (Sum.inr 5410, 1), (Sum.inr 5413, 1), (Sum.inr 5428, 1), (Sum.inr 5473, 1)]

theorem sourceEq2628 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2628 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2628 + difference 0 1) (sourceB2628 + difference 1 0) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2628 + difference 0 1) (sourceB2628 + difference 1 0) sourceC2628) = raw36767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36767; decide +kernel
    rw [ha]
    exact (canonical36767 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2628 + difference 0 2) (sourceB2628 + difference 2 0) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA2628 + difference 0 2) (sourceB2628 + difference 2 0) sourceC2628) = raw36768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36768; decide +kernel
    rw [ha]
    exact (canonical36768 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2628 + difference 0 3) (sourceB2628 + difference 3 0) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2628 + difference 0 3) (sourceB2628 + difference 3 0) sourceC2628) = raw36769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36769; decide +kernel
    rw [ha]
    exact (canonical36769 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2628 + difference 0 4) (sourceB2628 + difference 4 0) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2628 + difference 0 4) (sourceB2628 + difference 4 0) sourceC2628) = raw36770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36770; decide +kernel
    rw [ha]
    exact (canonical36770 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2628 + difference 0 5) (sourceB2628 + difference 5 0) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2628 + difference 0 5) (sourceB2628 + difference 5 0) sourceC2628) = raw36771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36771; decide +kernel
    rw [ha]
    exact (canonical36771 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2628 + difference 1 0) (sourceB2628 + difference 0 1) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2628 + difference 1 0) (sourceB2628 + difference 0 1) sourceC2628) = raw36772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36772; decide +kernel
    rw [ha]
    exact (canonical36772 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2628 + difference 1 2) (sourceB2628 + difference 2 1) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA2628 + difference 1 2) (sourceB2628 + difference 2 1) sourceC2628) = raw32670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw32670; decide +kernel
    rw [ha]
    exact (canonical32670 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2628 + difference 1 3) (sourceB2628 + difference 3 1) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA2628 + difference 1 3) (sourceB2628 + difference 3 1) sourceC2628) = raw32671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw32671; decide +kernel
    rw [ha]
    exact (canonical32671 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2628 + difference 1 4) (sourceB2628 + difference 4 1) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA2628 + difference 1 4) (sourceB2628 + difference 4 1) sourceC2628) = raw32672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw32672; decide +kernel
    rw [ha]
    exact (canonical32672 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2628 + difference 1 5) (sourceB2628 + difference 5 1) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2628 + difference 1 5) (sourceB2628 + difference 5 1) sourceC2628) = raw32673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw32673; decide +kernel
    rw [ha]
    exact (canonical32673 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2628 + difference 2 0) (sourceB2628 + difference 0 2) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4971) := by
    have ha : (tripleCharges (sourceA2628 + difference 2 0) (sourceB2628 + difference 0 2) sourceC2628) = raw32680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw32680; decide +kernel
    rw [ha]
    exact (canonical32680 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2628 + difference 2 1) (sourceB2628 + difference 1 2) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2628 + difference 2 1) (sourceB2628 + difference 1 2) sourceC2628) = raw36773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36773; decide +kernel
    rw [ha]
    exact (canonical36773 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2628 + difference 2 3) (sourceB2628 + difference 3 2) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2628 + difference 2 3) (sourceB2628 + difference 3 2) sourceC2628) = raw36774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36774; decide +kernel
    rw [ha]
    exact (canonical36774 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2628 + difference 2 4) (sourceB2628 + difference 4 2) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2628 + difference 2 4) (sourceB2628 + difference 4 2) sourceC2628) = raw36775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36775; decide +kernel
    rw [ha]
    exact (canonical36775 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2628 + difference 2 5) (sourceB2628 + difference 5 2) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA2628 + difference 2 5) (sourceB2628 + difference 5 2) sourceC2628) = raw36776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36776; decide +kernel
    rw [ha]
    exact (canonical36776 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2628 + difference 3 0) (sourceB2628 + difference 0 3) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2628 + difference 3 0) (sourceB2628 + difference 0 3) sourceC2628) = raw32685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw32685; decide +kernel
    rw [ha]
    exact (canonical32685 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2628 + difference 3 1) (sourceB2628 + difference 1 3) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2628 + difference 3 1) (sourceB2628 + difference 1 3) sourceC2628) = raw36777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36777; decide +kernel
    rw [ha]
    exact (canonical36777 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2628 + difference 3 2) (sourceB2628 + difference 2 3) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2628 + difference 3 2) (sourceB2628 + difference 2 3) sourceC2628) = raw36778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36778; decide +kernel
    rw [ha]
    exact (canonical36778 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2628 + difference 3 4) (sourceB2628 + difference 4 3) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2628 + difference 3 4) (sourceB2628 + difference 4 3) sourceC2628) = raw36779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36779; decide +kernel
    rw [ha]
    exact (canonical36779 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2628 + difference 3 5) (sourceB2628 + difference 5 3) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2628 + difference 3 5) (sourceB2628 + difference 5 3) sourceC2628) = raw36780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36780; decide +kernel
    rw [ha]
    exact (canonical36780 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2628 + difference 4 0) (sourceB2628 + difference 0 4) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2628 + difference 4 0) (sourceB2628 + difference 0 4) sourceC2628) = raw32690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw32690; decide +kernel
    rw [ha]
    exact (canonical32690 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2628 + difference 4 1) (sourceB2628 + difference 1 4) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2628 + difference 4 1) (sourceB2628 + difference 1 4) sourceC2628) = raw36781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36781; decide +kernel
    rw [ha]
    exact (canonical36781 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2628 + difference 4 2) (sourceB2628 + difference 2 4) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5336) := by
    have ha : (tripleCharges (sourceA2628 + difference 4 2) (sourceB2628 + difference 2 4) sourceC2628) = raw36782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36782; decide +kernel
    rw [ha]
    exact (canonical36782 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2628 + difference 4 3) (sourceB2628 + difference 3 4) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2628 + difference 4 3) (sourceB2628 + difference 3 4) sourceC2628) = raw36783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36783; decide +kernel
    rw [ha]
    exact (canonical36783 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2628 + difference 4 5) (sourceB2628 + difference 5 4) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2628 + difference 4 5) (sourceB2628 + difference 5 4) sourceC2628) = raw36784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36784; decide +kernel
    rw [ha]
    exact (canonical36784 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2628 + difference 5 0) (sourceB2628 + difference 0 5) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA2628 + difference 5 0) (sourceB2628 + difference 0 5) sourceC2628) = raw32695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw32695; decide +kernel
    rw [ha]
    exact (canonical32695 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2628 + difference 5 1) (sourceB2628 + difference 1 5) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2628 + difference 5 1) (sourceB2628 + difference 1 5) sourceC2628) = raw36785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36785; decide +kernel
    rw [ha]
    exact (canonical36785 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2628 + difference 5 2) (sourceB2628 + difference 2 5) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2628 + difference 5 2) (sourceB2628 + difference 2 5) sourceC2628) = raw36786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36786; decide +kernel
    rw [ha]
    exact (canonical36786 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2628 + difference 5 3) (sourceB2628 + difference 3 5) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2628 + difference 5 3) (sourceB2628 + difference 3 5) sourceC2628) = raw36787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36787; decide +kernel
    rw [ha]
    exact (canonical36787 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2628 + difference 5 4) (sourceB2628 + difference 4 5) sourceC2628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2628 + difference 5 4) (sourceB2628 + difference 4 5) sourceC2628) = raw36788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2628 sourceB2628 sourceC2628 difference raw36788; decide +kernel
    rw [ha]
    exact (canonical36788 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2628 sourceB2628 sourceC2628
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2628, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2629 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2629 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC2629 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceForm2629 : Integer.Sparse Master := [(Sum.inr 4763, 1), (Sum.inr 4769, 1), (Sum.inr 4770, 1), (Sum.inr 4846, 2), (Sum.inr 4938, 1), (Sum.inr 4945, 2), (Sum.inr 4975, 1), (Sum.inr 4976, 2), (Sum.inr 5099, 1), (Sum.inr 5205, 1), (Sum.inr 5215, 2), (Sum.inr 5238, 2), (Sum.inr 5241, 1), (Sum.inr 5242, 1), (Sum.inr 5248, 2), (Sum.inr 5274, 2), (Sum.inr 5275, 2), (Sum.inr 5277, 1), (Sum.inr 5282, 1), (Sum.inr 5284, 1), (Sum.inr 5287, 2)]

theorem sourceEq2629 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2629 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2629 + difference 0 1) (sourceB2629 + difference 1 0) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2629 + difference 0 1) (sourceB2629 + difference 1 0) sourceC2629) = raw36789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36789; decide +kernel
    rw [ha]
    exact (canonical36789 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2629 + difference 0 2) (sourceB2629 + difference 2 0) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA2629 + difference 0 2) (sourceB2629 + difference 2 0) sourceC2629) = raw36790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36790; decide +kernel
    rw [ha]
    exact (canonical36790 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2629 + difference 0 3) (sourceB2629 + difference 3 0) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2629 + difference 0 3) (sourceB2629 + difference 3 0) sourceC2629) = raw36791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36791; decide +kernel
    rw [ha]
    exact (canonical36791 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2629 + difference 0 4) (sourceB2629 + difference 4 0) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2629 + difference 0 4) (sourceB2629 + difference 4 0) sourceC2629) = raw36792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36792; decide +kernel
    rw [ha]
    exact (canonical36792 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2629 + difference 0 5) (sourceB2629 + difference 5 0) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA2629 + difference 0 5) (sourceB2629 + difference 5 0) sourceC2629) = raw36793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36793; decide +kernel
    rw [ha]
    exact (canonical36793 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2629 + difference 1 0) (sourceB2629 + difference 0 1) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA2629 + difference 1 0) (sourceB2629 + difference 0 1) sourceC2629) = raw28414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw28414; decide +kernel
    rw [ha]
    exact (canonical28414 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2629 + difference 1 2) (sourceB2629 + difference 2 1) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5242) := by
    have ha : (tripleCharges (sourceA2629 + difference 1 2) (sourceB2629 + difference 2 1) sourceC2629) = raw36794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36794; decide +kernel
    rw [ha]
    exact (canonical36794 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2629 + difference 1 3) (sourceB2629 + difference 3 1) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2629 + difference 1 3) (sourceB2629 + difference 3 1) sourceC2629) = raw28399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw28399; decide +kernel
    rw [ha]
    exact (canonical28399 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2629 + difference 1 4) (sourceB2629 + difference 4 1) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2629 + difference 1 4) (sourceB2629 + difference 4 1) sourceC2629) = raw36795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36795; decide +kernel
    rw [ha]
    exact (canonical36795 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2629 + difference 1 5) (sourceB2629 + difference 5 1) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA2629 + difference 1 5) (sourceB2629 + difference 5 1) sourceC2629) = raw36796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36796; decide +kernel
    rw [ha]
    exact (canonical36796 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2629 + difference 2 0) (sourceB2629 + difference 0 2) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4975) := by
    have ha : (tripleCharges (sourceA2629 + difference 2 0) (sourceB2629 + difference 0 2) sourceC2629) = raw36797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36797; decide +kernel
    rw [ha]
    exact (canonical36797 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2629 + difference 2 1) (sourceB2629 + difference 1 2) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4938) := by
    have ha : (tripleCharges (sourceA2629 + difference 2 1) (sourceB2629 + difference 1 2) sourceC2629) = raw36798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36798; decide +kernel
    rw [ha]
    exact (canonical36798 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2629 + difference 2 3) (sourceB2629 + difference 3 2) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2629 + difference 2 3) (sourceB2629 + difference 3 2) sourceC2629) = raw36799 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36799; decide +kernel
    rw [ha]
    exact (canonical36799 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2629 + difference 2 4) (sourceB2629 + difference 4 2) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2629 + difference 2 4) (sourceB2629 + difference 4 2) sourceC2629) = raw36800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36800; decide +kernel
    rw [ha]
    exact (canonical36800 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2629 + difference 2 5) (sourceB2629 + difference 5 2) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5277) := by
    have ha : (tripleCharges (sourceA2629 + difference 2 5) (sourceB2629 + difference 5 2) sourceC2629) = raw36801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36801; decide +kernel
    rw [ha]
    exact (canonical36801 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2629 + difference 3 0) (sourceB2629 + difference 0 3) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4976) := by
    have ha : (tripleCharges (sourceA2629 + difference 3 0) (sourceB2629 + difference 0 3) sourceC2629) = raw36802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36802; decide +kernel
    rw [ha]
    exact (canonical36802 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2629 + difference 3 1) (sourceB2629 + difference 1 3) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2629 + difference 3 1) (sourceB2629 + difference 1 3) sourceC2629) = raw36803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36803; decide +kernel
    rw [ha]
    exact (canonical36803 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2629 + difference 3 2) (sourceB2629 + difference 2 3) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5215) := by
    have ha : (tripleCharges (sourceA2629 + difference 3 2) (sourceB2629 + difference 2 3) sourceC2629) = raw36804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36804; decide +kernel
    rw [ha]
    exact (canonical36804 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2629 + difference 3 4) (sourceB2629 + difference 4 3) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2629 + difference 3 4) (sourceB2629 + difference 4 3) sourceC2629) = raw36805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36805; decide +kernel
    rw [ha]
    exact (canonical36805 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2629 + difference 3 5) (sourceB2629 + difference 5 3) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA2629 + difference 3 5) (sourceB2629 + difference 5 3) sourceC2629) = raw36806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36806; decide +kernel
    rw [ha]
    exact (canonical36806 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2629 + difference 4 0) (sourceB2629 + difference 0 4) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4976) := by
    have ha : (tripleCharges (sourceA2629 + difference 4 0) (sourceB2629 + difference 0 4) sourceC2629) = raw36807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36807; decide +kernel
    rw [ha]
    exact (canonical36807 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2629 + difference 4 1) (sourceB2629 + difference 1 4) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2629 + difference 4 1) (sourceB2629 + difference 1 4) sourceC2629) = raw36808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36808; decide +kernel
    rw [ha]
    exact (canonical36808 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2629 + difference 4 2) (sourceB2629 + difference 2 4) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5215) := by
    have ha : (tripleCharges (sourceA2629 + difference 4 2) (sourceB2629 + difference 2 4) sourceC2629) = raw36809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36809; decide +kernel
    rw [ha]
    exact (canonical36809 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2629 + difference 4 3) (sourceB2629 + difference 3 4) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2629 + difference 4 3) (sourceB2629 + difference 3 4) sourceC2629) = raw36810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36810; decide +kernel
    rw [ha]
    exact (canonical36810 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2629 + difference 4 5) (sourceB2629 + difference 5 4) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA2629 + difference 4 5) (sourceB2629 + difference 5 4) sourceC2629) = raw36811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36811; decide +kernel
    rw [ha]
    exact (canonical36811 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2629 + difference 5 0) (sourceB2629 + difference 0 5) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA2629 + difference 5 0) (sourceB2629 + difference 0 5) sourceC2629) = raw28411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw28411; decide +kernel
    rw [ha]
    exact (canonical28411 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2629 + difference 5 1) (sourceB2629 + difference 1 5) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2629 + difference 5 1) (sourceB2629 + difference 1 5) sourceC2629) = raw36812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36812; decide +kernel
    rw [ha]
    exact (canonical36812 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2629 + difference 5 2) (sourceB2629 + difference 2 5) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2629 + difference 5 2) (sourceB2629 + difference 2 5) sourceC2629) = raw36813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36813; decide +kernel
    rw [ha]
    exact (canonical36813 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2629 + difference 5 3) (sourceB2629 + difference 3 5) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2629 + difference 5 3) (sourceB2629 + difference 3 5) sourceC2629) = raw28395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw28395; decide +kernel
    rw [ha]
    exact (canonical28395 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2629 + difference 5 4) (sourceB2629 + difference 4 5) sourceC2629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2629 + difference 5 4) (sourceB2629 + difference 4 5) sourceC2629) = raw36814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2629 sourceB2629 sourceC2629 difference raw36814; decide +kernel
    rw [ha]
    exact (canonical36814 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2629 sourceB2629 sourceC2629
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2629, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2630 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2630 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC2630 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceForm2630 : Integer.Sparse Master := [(Sum.inr 2174, 1), (Sum.inr 2185, 1), (Sum.inr 2186, 1), (Sum.inr 2229, 2), (Sum.inr 2653, 2), (Sum.inr 2658, 2), (Sum.inr 2659, 2), (Sum.inr 2686, 2), (Sum.inr 2689, 1), (Sum.inr 2690, 1), (Sum.inr 2694, 1), (Sum.inr 2695, 1), (Sum.inr 2704, 1), (Sum.inr 2705, 2), (Sum.inr 2706, 1), (Sum.inr 2742, 2), (Sum.inr 2743, 2), (Sum.inr 3025, 2), (Sum.inr 3059, 1), (Sum.inr 3077, 1), (Sum.inr 3078, 1)]

theorem sourceEq2630 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2630 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2630 + difference 0 1) (sourceB2630 + difference 1 0) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2630 + difference 0 1) (sourceB2630 + difference 1 0) sourceC2630) = raw36815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36815; decide +kernel
    rw [ha]
    exact (canonical36815 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2630 + difference 0 2) (sourceB2630 + difference 2 0) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA2630 + difference 0 2) (sourceB2630 + difference 2 0) sourceC2630) = raw36816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36816; decide +kernel
    rw [ha]
    exact (canonical36816 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2630 + difference 0 3) (sourceB2630 + difference 3 0) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2630 + difference 0 3) (sourceB2630 + difference 3 0) sourceC2630) = raw36817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36817; decide +kernel
    rw [ha]
    exact (canonical36817 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2630 + difference 0 4) (sourceB2630 + difference 4 0) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2630 + difference 0 4) (sourceB2630 + difference 4 0) sourceC2630) = raw36818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36818; decide +kernel
    rw [ha]
    exact (canonical36818 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2630 + difference 0 5) (sourceB2630 + difference 5 0) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA2630 + difference 0 5) (sourceB2630 + difference 5 0) sourceC2630) = raw36819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36819; decide +kernel
    rw [ha]
    exact (canonical36819 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2630 + difference 1 0) (sourceB2630 + difference 0 1) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA2630 + difference 1 0) (sourceB2630 + difference 0 1) sourceC2630) = raw28444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw28444; decide +kernel
    rw [ha]
    exact (canonical28444 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2630 + difference 1 2) (sourceB2630 + difference 2 1) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2695) := by
    have ha : (tripleCharges (sourceA2630 + difference 1 2) (sourceB2630 + difference 2 1) sourceC2630) = raw36820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36820; decide +kernel
    rw [ha]
    exact (canonical36820 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2630 + difference 1 3) (sourceB2630 + difference 3 1) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA2630 + difference 1 3) (sourceB2630 + difference 3 1) sourceC2630) = raw28429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw28429; decide +kernel
    rw [ha]
    exact (canonical28429 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2630 + difference 1 4) (sourceB2630 + difference 4 1) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA2630 + difference 1 4) (sourceB2630 + difference 4 1) sourceC2630) = raw36821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36821; decide +kernel
    rw [ha]
    exact (canonical36821 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2630 + difference 1 5) (sourceB2630 + difference 5 1) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA2630 + difference 1 5) (sourceB2630 + difference 5 1) sourceC2630) = raw36822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36822; decide +kernel
    rw [ha]
    exact (canonical36822 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2630 + difference 2 0) (sourceB2630 + difference 0 2) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2690) := by
    have ha : (tripleCharges (sourceA2630 + difference 2 0) (sourceB2630 + difference 0 2) sourceC2630) = raw36823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36823; decide +kernel
    rw [ha]
    exact (canonical36823 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2630 + difference 2 1) (sourceB2630 + difference 1 2) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2689) := by
    have ha : (tripleCharges (sourceA2630 + difference 2 1) (sourceB2630 + difference 1 2) sourceC2630) = raw36824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36824; decide +kernel
    rw [ha]
    exact (canonical36824 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2630 + difference 2 3) (sourceB2630 + difference 3 2) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2630 + difference 2 3) (sourceB2630 + difference 3 2) sourceC2630) = raw36825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36825; decide +kernel
    rw [ha]
    exact (canonical36825 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2630 + difference 2 4) (sourceB2630 + difference 4 2) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2630 + difference 2 4) (sourceB2630 + difference 4 2) sourceC2630) = raw36826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36826; decide +kernel
    rw [ha]
    exact (canonical36826 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2630 + difference 2 5) (sourceB2630 + difference 5 2) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3059) := by
    have ha : (tripleCharges (sourceA2630 + difference 2 5) (sourceB2630 + difference 5 2) sourceC2630) = raw36827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36827; decide +kernel
    rw [ha]
    exact (canonical36827 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2630 + difference 3 0) (sourceB2630 + difference 0 3) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2659) := by
    have ha : (tripleCharges (sourceA2630 + difference 3 0) (sourceB2630 + difference 0 3) sourceC2630) = raw36828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36828; decide +kernel
    rw [ha]
    exact (canonical36828 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2630 + difference 3 1) (sourceB2630 + difference 1 3) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2630 + difference 3 1) (sourceB2630 + difference 1 3) sourceC2630) = raw36829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36829; decide +kernel
    rw [ha]
    exact (canonical36829 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2630 + difference 3 2) (sourceB2630 + difference 2 3) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2653) := by
    have ha : (tripleCharges (sourceA2630 + difference 3 2) (sourceB2630 + difference 2 3) sourceC2630) = raw36830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36830; decide +kernel
    rw [ha]
    exact (canonical36830 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2630 + difference 3 4) (sourceB2630 + difference 4 3) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA2630 + difference 3 4) (sourceB2630 + difference 4 3) sourceC2630) = raw36831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36831; decide +kernel
    rw [ha]
    exact (canonical36831 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2630 + difference 3 5) (sourceB2630 + difference 5 3) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA2630 + difference 3 5) (sourceB2630 + difference 5 3) sourceC2630) = raw36832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36832; decide +kernel
    rw [ha]
    exact (canonical36832 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2630 + difference 4 0) (sourceB2630 + difference 0 4) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2659) := by
    have ha : (tripleCharges (sourceA2630 + difference 4 0) (sourceB2630 + difference 0 4) sourceC2630) = raw36833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36833; decide +kernel
    rw [ha]
    exact (canonical36833 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2630 + difference 4 1) (sourceB2630 + difference 1 4) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2630 + difference 4 1) (sourceB2630 + difference 1 4) sourceC2630) = raw36834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36834; decide +kernel
    rw [ha]
    exact (canonical36834 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2630 + difference 4 2) (sourceB2630 + difference 2 4) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2653) := by
    have ha : (tripleCharges (sourceA2630 + difference 4 2) (sourceB2630 + difference 2 4) sourceC2630) = raw36835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36835; decide +kernel
    rw [ha]
    exact (canonical36835 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2630 + difference 4 3) (sourceB2630 + difference 3 4) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA2630 + difference 4 3) (sourceB2630 + difference 3 4) sourceC2630) = raw36836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36836; decide +kernel
    rw [ha]
    exact (canonical36836 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2630 + difference 4 5) (sourceB2630 + difference 5 4) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA2630 + difference 4 5) (sourceB2630 + difference 5 4) sourceC2630) = raw36837 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36837; decide +kernel
    rw [ha]
    exact (canonical36837 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2630 + difference 5 0) (sourceB2630 + difference 0 5) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2630 + difference 5 0) (sourceB2630 + difference 0 5) sourceC2630) = raw28441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw28441; decide +kernel
    rw [ha]
    exact (canonical28441 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2630 + difference 5 1) (sourceB2630 + difference 1 5) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2630 + difference 5 1) (sourceB2630 + difference 1 5) sourceC2630) = raw36838 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36838; decide +kernel
    rw [ha]
    exact (canonical36838 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2630 + difference 5 2) (sourceB2630 + difference 2 5) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2174) := by
    have ha : (tripleCharges (sourceA2630 + difference 5 2) (sourceB2630 + difference 2 5) sourceC2630) = raw36839 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36839; decide +kernel
    rw [ha]
    exact (canonical36839 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2630 + difference 5 3) (sourceB2630 + difference 3 5) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2630 + difference 5 3) (sourceB2630 + difference 3 5) sourceC2630) = raw28425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw28425; decide +kernel
    rw [ha]
    exact (canonical28425 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2630 + difference 5 4) (sourceB2630 + difference 4 5) sourceC2630) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2630 + difference 5 4) (sourceB2630 + difference 4 5) sourceC2630) = raw36840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2630 sourceB2630 sourceC2630 difference raw36840; decide +kernel
    rw [ha]
    exact (canonical36840 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2630 sourceB2630 sourceC2630
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2630, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2631 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2631 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceC2631 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceForm2631 : Integer.Sparse Master := [(Sum.inr 4387, 1), (Sum.inr 4388, 1), (Sum.inr 4389, 1), (Sum.inr 4419, 2), (Sum.inr 4639, 1), (Sum.inr 4645, 2), (Sum.inr 4832, 1), (Sum.inr 4909, 1), (Sum.inr 4914, 2), (Sum.inr 4990, 2), (Sum.inr 5015, 2), (Sum.inr 5056, 2), (Sum.inr 5099, 1), (Sum.inr 5241, 1), (Sum.inr 5247, 1), (Sum.inr 5258, 2), (Sum.inr 5271, 2), (Sum.inr 5365, 1), (Sum.inr 5368, 2), (Sum.inr 5439, 1), (Sum.inr 5485, 1)]

theorem sourceEq2631 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2631 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2631 + difference 0 1) (sourceB2631 + difference 1 0) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2631 + difference 0 1) (sourceB2631 + difference 1 0) sourceC2631) = raw36841 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36841; decide +kernel
    rw [ha]
    exact (canonical36841 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2631 + difference 0 2) (sourceB2631 + difference 2 0) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA2631 + difference 0 2) (sourceB2631 + difference 2 0) sourceC2631) = raw36842 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36842; decide +kernel
    rw [ha]
    exact (canonical36842 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2631 + difference 0 3) (sourceB2631 + difference 3 0) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2631 + difference 0 3) (sourceB2631 + difference 3 0) sourceC2631) = raw36843 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36843; decide +kernel
    rw [ha]
    exact (canonical36843 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2631 + difference 0 4) (sourceB2631 + difference 4 0) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2631 + difference 0 4) (sourceB2631 + difference 4 0) sourceC2631) = raw36844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36844; decide +kernel
    rw [ha]
    exact (canonical36844 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2631 + difference 0 5) (sourceB2631 + difference 5 0) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2631 + difference 0 5) (sourceB2631 + difference 5 0) sourceC2631) = raw18664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw18664; decide +kernel
    rw [ha]
    exact (canonical18664 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2631 + difference 1 0) (sourceB2631 + difference 0 1) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2631 + difference 1 0) (sourceB2631 + difference 0 1) sourceC2631) = raw10688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw10688; decide +kernel
    rw [ha]
    exact (canonical10688 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2631 + difference 1 2) (sourceB2631 + difference 2 1) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA2631 + difference 1 2) (sourceB2631 + difference 2 1) sourceC2631) = raw18682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw18682; decide +kernel
    rw [ha]
    exact (canonical18682 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2631 + difference 1 3) (sourceB2631 + difference 3 1) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA2631 + difference 1 3) (sourceB2631 + difference 3 1) sourceC2631) = raw10672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw10672; decide +kernel
    rw [ha]
    exact (canonical10672 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2631 + difference 1 4) (sourceB2631 + difference 4 1) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA2631 + difference 1 4) (sourceB2631 + difference 4 1) sourceC2631) = raw18683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw18683; decide +kernel
    rw [ha]
    exact (canonical18683 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2631 + difference 1 5) (sourceB2631 + difference 5 1) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2631 + difference 1 5) (sourceB2631 + difference 5 1) sourceC2631) = raw12131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw12131; decide +kernel
    rw [ha]
    exact (canonical12131 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2631 + difference 2 0) (sourceB2631 + difference 0 2) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4909) := by
    have ha : (tripleCharges (sourceA2631 + difference 2 0) (sourceB2631 + difference 0 2) sourceC2631) = raw33346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw33346; decide +kernel
    rw [ha]
    exact (canonical33346 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2631 + difference 2 1) (sourceB2631 + difference 1 2) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4639) := by
    have ha : (tripleCharges (sourceA2631 + difference 2 1) (sourceB2631 + difference 1 2) sourceC2631) = raw36845 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36845; decide +kernel
    rw [ha]
    exact (canonical36845 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2631 + difference 2 3) (sourceB2631 + difference 3 2) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2631 + difference 2 3) (sourceB2631 + difference 3 2) sourceC2631) = raw36846 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36846; decide +kernel
    rw [ha]
    exact (canonical36846 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2631 + difference 2 4) (sourceB2631 + difference 4 2) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2631 + difference 2 4) (sourceB2631 + difference 4 2) sourceC2631) = raw36847 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36847; decide +kernel
    rw [ha]
    exact (canonical36847 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2631 + difference 2 5) (sourceB2631 + difference 5 2) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA2631 + difference 2 5) (sourceB2631 + difference 5 2) sourceC2631) = raw18669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw18669; decide +kernel
    rw [ha]
    exact (canonical18669 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2631 + difference 3 0) (sourceB2631 + difference 0 3) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4914) := by
    have ha : (tripleCharges (sourceA2631 + difference 3 0) (sourceB2631 + difference 0 3) sourceC2631) = raw33348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw33348; decide +kernel
    rw [ha]
    exact (canonical33348 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2631 + difference 3 1) (sourceB2631 + difference 1 3) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4645) := by
    have ha : (tripleCharges (sourceA2631 + difference 3 1) (sourceB2631 + difference 1 3) sourceC2631) = raw36848 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36848; decide +kernel
    rw [ha]
    exact (canonical36848 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2631 + difference 3 2) (sourceB2631 + difference 2 3) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4990) := by
    have ha : (tripleCharges (sourceA2631 + difference 3 2) (sourceB2631 + difference 2 3) sourceC2631) = raw36849 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36849; decide +kernel
    rw [ha]
    exact (canonical36849 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2631 + difference 3 4) (sourceB2631 + difference 4 3) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2631 + difference 3 4) (sourceB2631 + difference 4 3) sourceC2631) = raw36850 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36850; decide +kernel
    rw [ha]
    exact (canonical36850 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2631 + difference 3 5) (sourceB2631 + difference 5 3) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2631 + difference 3 5) (sourceB2631 + difference 5 3) sourceC2631) = raw18673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw18673; decide +kernel
    rw [ha]
    exact (canonical18673 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2631 + difference 4 0) (sourceB2631 + difference 0 4) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4914) := by
    have ha : (tripleCharges (sourceA2631 + difference 4 0) (sourceB2631 + difference 0 4) sourceC2631) = raw33351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw33351; decide +kernel
    rw [ha]
    exact (canonical33351 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2631 + difference 4 1) (sourceB2631 + difference 1 4) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4645) := by
    have ha : (tripleCharges (sourceA2631 + difference 4 1) (sourceB2631 + difference 1 4) sourceC2631) = raw36851 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36851; decide +kernel
    rw [ha]
    exact (canonical36851 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2631 + difference 4 2) (sourceB2631 + difference 2 4) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4990) := by
    have ha : (tripleCharges (sourceA2631 + difference 4 2) (sourceB2631 + difference 2 4) sourceC2631) = raw36852 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36852; decide +kernel
    rw [ha]
    exact (canonical36852 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2631 + difference 4 3) (sourceB2631 + difference 3 4) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2631 + difference 4 3) (sourceB2631 + difference 3 4) sourceC2631) = raw36853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36853; decide +kernel
    rw [ha]
    exact (canonical36853 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2631 + difference 4 5) (sourceB2631 + difference 5 4) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2631 + difference 4 5) (sourceB2631 + difference 5 4) sourceC2631) = raw18677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw18677; decide +kernel
    rw [ha]
    exact (canonical18677 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2631 + difference 5 0) (sourceB2631 + difference 0 5) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4389) := by
    have ha : (tripleCharges (sourceA2631 + difference 5 0) (sourceB2631 + difference 0 5) sourceC2631) = raw33353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw33353; decide +kernel
    rw [ha]
    exact (canonical33353 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2631 + difference 5 1) (sourceB2631 + difference 1 5) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4388) := by
    have ha : (tripleCharges (sourceA2631 + difference 5 1) (sourceB2631 + difference 1 5) sourceC2631) = raw36854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36854; decide +kernel
    rw [ha]
    exact (canonical36854 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2631 + difference 5 2) (sourceB2631 + difference 2 5) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4387) := by
    have ha : (tripleCharges (sourceA2631 + difference 5 2) (sourceB2631 + difference 2 5) sourceC2631) = raw36855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36855; decide +kernel
    rw [ha]
    exact (canonical36855 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2631 + difference 5 3) (sourceB2631 + difference 3 5) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA2631 + difference 5 3) (sourceB2631 + difference 3 5) sourceC2631) = raw36856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36856; decide +kernel
    rw [ha]
    exact (canonical36856 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2631 + difference 5 4) (sourceB2631 + difference 4 5) sourceC2631) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA2631 + difference 5 4) (sourceB2631 + difference 4 5) sourceC2631) = raw36857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2631 sourceB2631 sourceC2631 difference raw36857; decide +kernel
    rw [ha]
    exact (canonical36857 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2631 sourceB2631 sourceC2631
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2631, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2632 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2632 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceC2632 : Charge := ![1, 2, 1, -1, -1, -2]
def sourceForm2632 : Integer.Sparse Master := [(Sum.inr 4090, 1), (Sum.inr 4927, 1), (Sum.inr 4928, 2), (Sum.inr 4936, 1), (Sum.inr 4960, 1), (Sum.inr 4961, 2), (Sum.inr 4969, 1), (Sum.inr 5029, 1), (Sum.inr 5050, 2), (Sum.inr 5058, 1), (Sum.inr 5192, 1), (Sum.inr 5332, 2), (Sum.inr 5341, 2), (Sum.inr 5346, 2), (Sum.inr 5349, 2), (Sum.inr 5363, 1), (Sum.inr 5392, 1), (Sum.inr 5394, 2), (Sum.inr 5395, 2), (Sum.inr 5396, 1), (Sum.inr 5469, 1)]

theorem sourceEq2632 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2632 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2632 + difference 0 1) (sourceB2632 + difference 1 0) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5058) := by
    have ha : (tripleCharges (sourceA2632 + difference 0 1) (sourceB2632 + difference 1 0) sourceC2632) = raw36858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36858; decide +kernel
    rw [ha]
    exact (canonical36858 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2632 + difference 0 2) (sourceB2632 + difference 2 0) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2632 + difference 0 2) (sourceB2632 + difference 2 0) sourceC2632) = raw36859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36859; decide +kernel
    rw [ha]
    exact (canonical36859 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2632 + difference 0 3) (sourceB2632 + difference 3 0) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA2632 + difference 0 3) (sourceB2632 + difference 3 0) sourceC2632) = raw36860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36860; decide +kernel
    rw [ha]
    exact (canonical36860 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2632 + difference 0 4) (sourceB2632 + difference 4 0) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA2632 + difference 0 4) (sourceB2632 + difference 4 0) sourceC2632) = raw36861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36861; decide +kernel
    rw [ha]
    exact (canonical36861 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2632 + difference 0 5) (sourceB2632 + difference 5 0) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA2632 + difference 0 5) (sourceB2632 + difference 5 0) sourceC2632) = raw36862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36862; decide +kernel
    rw [ha]
    exact (canonical36862 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2632 + difference 1 0) (sourceB2632 + difference 0 1) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA2632 + difference 1 0) (sourceB2632 + difference 0 1) sourceC2632) = raw36863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36863; decide +kernel
    rw [ha]
    exact (canonical36863 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2632 + difference 1 2) (sourceB2632 + difference 2 1) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5392) := by
    have ha : (tripleCharges (sourceA2632 + difference 1 2) (sourceB2632 + difference 2 1) sourceC2632) = raw36864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36864; decide +kernel
    rw [ha]
    exact (canonical36864 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2632 + difference 1 3) (sourceB2632 + difference 3 1) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA2632 + difference 1 3) (sourceB2632 + difference 3 1) sourceC2632) = raw36865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36865; decide +kernel
    rw [ha]
    exact (canonical36865 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2632 + difference 1 4) (sourceB2632 + difference 4 1) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA2632 + difference 1 4) (sourceB2632 + difference 4 1) sourceC2632) = raw36866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36866; decide +kernel
    rw [ha]
    exact (canonical36866 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2632 + difference 1 5) (sourceB2632 + difference 5 1) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA2632 + difference 1 5) (sourceB2632 + difference 5 1) sourceC2632) = raw36867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36867; decide +kernel
    rw [ha]
    exact (canonical36867 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2632 + difference 2 0) (sourceB2632 + difference 0 2) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4969) := by
    have ha : (tripleCharges (sourceA2632 + difference 2 0) (sourceB2632 + difference 0 2) sourceC2632) = raw36868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36868; decide +kernel
    rw [ha]
    exact (canonical36868 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2632 + difference 2 1) (sourceB2632 + difference 1 2) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2632 + difference 2 1) (sourceB2632 + difference 1 2) sourceC2632) = raw36869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36869; decide +kernel
    rw [ha]
    exact (canonical36869 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2632 + difference 2 3) (sourceB2632 + difference 3 2) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA2632 + difference 2 3) (sourceB2632 + difference 3 2) sourceC2632) = raw36870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36870; decide +kernel
    rw [ha]
    exact (canonical36870 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2632 + difference 2 4) (sourceB2632 + difference 4 2) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA2632 + difference 2 4) (sourceB2632 + difference 4 2) sourceC2632) = raw36871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36871; decide +kernel
    rw [ha]
    exact (canonical36871 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2632 + difference 2 5) (sourceB2632 + difference 5 2) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5363) := by
    have ha : (tripleCharges (sourceA2632 + difference 2 5) (sourceB2632 + difference 5 2) sourceC2632) = raw36872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36872; decide +kernel
    rw [ha]
    exact (canonical36872 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2632 + difference 3 0) (sourceB2632 + difference 0 3) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4961) := by
    have ha : (tripleCharges (sourceA2632 + difference 3 0) (sourceB2632 + difference 0 3) sourceC2632) = raw36873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36873; decide +kernel
    rw [ha]
    exact (canonical36873 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2632 + difference 3 1) (sourceB2632 + difference 1 3) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2632 + difference 3 1) (sourceB2632 + difference 1 3) sourceC2632) = raw36874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36874; decide +kernel
    rw [ha]
    exact (canonical36874 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2632 + difference 3 2) (sourceB2632 + difference 2 3) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5332) := by
    have ha : (tripleCharges (sourceA2632 + difference 3 2) (sourceB2632 + difference 2 3) sourceC2632) = raw36875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36875; decide +kernel
    rw [ha]
    exact (canonical36875 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2632 + difference 3 4) (sourceB2632 + difference 4 3) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA2632 + difference 3 4) (sourceB2632 + difference 4 3) sourceC2632) = raw36876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36876; decide +kernel
    rw [ha]
    exact (canonical36876 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2632 + difference 3 5) (sourceB2632 + difference 5 3) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2632 + difference 3 5) (sourceB2632 + difference 5 3) sourceC2632) = raw36877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36877; decide +kernel
    rw [ha]
    exact (canonical36877 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2632 + difference 4 0) (sourceB2632 + difference 0 4) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4961) := by
    have ha : (tripleCharges (sourceA2632 + difference 4 0) (sourceB2632 + difference 0 4) sourceC2632) = raw36878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36878; decide +kernel
    rw [ha]
    exact (canonical36878 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2632 + difference 4 1) (sourceB2632 + difference 1 4) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2632 + difference 4 1) (sourceB2632 + difference 1 4) sourceC2632) = raw36879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36879; decide +kernel
    rw [ha]
    exact (canonical36879 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2632 + difference 4 2) (sourceB2632 + difference 2 4) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5332) := by
    have ha : (tripleCharges (sourceA2632 + difference 4 2) (sourceB2632 + difference 2 4) sourceC2632) = raw36880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36880; decide +kernel
    rw [ha]
    exact (canonical36880 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2632 + difference 4 3) (sourceB2632 + difference 3 4) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA2632 + difference 4 3) (sourceB2632 + difference 3 4) sourceC2632) = raw36881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36881; decide +kernel
    rw [ha]
    exact (canonical36881 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2632 + difference 4 5) (sourceB2632 + difference 5 4) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2632 + difference 4 5) (sourceB2632 + difference 5 4) sourceC2632) = raw36882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36882; decide +kernel
    rw [ha]
    exact (canonical36882 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2632 + difference 5 0) (sourceB2632 + difference 0 5) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4960) := by
    have ha : (tripleCharges (sourceA2632 + difference 5 0) (sourceB2632 + difference 0 5) sourceC2632) = raw36883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36883; decide +kernel
    rw [ha]
    exact (canonical36883 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2632 + difference 5 1) (sourceB2632 + difference 1 5) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4927) := by
    have ha : (tripleCharges (sourceA2632 + difference 5 1) (sourceB2632 + difference 1 5) sourceC2632) = raw36884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36884; decide +kernel
    rw [ha]
    exact (canonical36884 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2632 + difference 5 2) (sourceB2632 + difference 2 5) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5029) := by
    have ha : (tripleCharges (sourceA2632 + difference 5 2) (sourceB2632 + difference 2 5) sourceC2632) = raw36885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36885; decide +kernel
    rw [ha]
    exact (canonical36885 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2632 + difference 5 3) (sourceB2632 + difference 3 5) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2632 + difference 5 3) (sourceB2632 + difference 3 5) sourceC2632) = raw36886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36886; decide +kernel
    rw [ha]
    exact (canonical36886 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2632 + difference 5 4) (sourceB2632 + difference 4 5) sourceC2632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2632 + difference 5 4) (sourceB2632 + difference 4 5) sourceC2632) = raw36887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2632 sourceB2632 sourceC2632 difference raw36887; decide +kernel
    rw [ha]
    exact (canonical36887 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2632 sourceB2632 sourceC2632
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2632, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2633 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceB2633 : Charge := ![1, 2, 1, -1, -1, -2]
def sourceC2633 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceForm2633 : Integer.Sparse Master := [(Sum.inr 4088, 1), (Sum.inr 4986, 1), (Sum.inr 4987, 2), (Sum.inr 5017, 1), (Sum.inr 5025, 1), (Sum.inr 5030, 1), (Sum.inr 5056, 2), (Sum.inr 5123, 1), (Sum.inr 5314, 2), (Sum.inr 5333, 2), (Sum.inr 5344, 2), (Sum.inr 5345, 1), (Sum.inr 5346, 2), (Sum.inr 5367, 2), (Sum.inr 5369, 1), (Sum.inr 5374, 1), (Sum.inr 5378, 2), (Sum.inr 5380, 1), (Sum.inr 5391, 1), (Sum.inr 5393, 2), (Sum.inr 5460, 1)]

theorem sourceEq2633 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2633 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2633 + difference 0 1) (sourceB2633 + difference 1 0) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2633 + difference 0 1) (sourceB2633 + difference 1 0) sourceC2633) = raw36888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36888; decide +kernel
    rw [ha]
    exact (canonical36888 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2633 + difference 0 2) (sourceB2633 + difference 2 0) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA2633 + difference 0 2) (sourceB2633 + difference 2 0) sourceC2633) = raw36889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36889; decide +kernel
    rw [ha]
    exact (canonical36889 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2633 + difference 0 3) (sourceB2633 + difference 3 0) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2633 + difference 0 3) (sourceB2633 + difference 3 0) sourceC2633) = raw36890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36890; decide +kernel
    rw [ha]
    exact (canonical36890 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2633 + difference 0 4) (sourceB2633 + difference 4 0) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2633 + difference 0 4) (sourceB2633 + difference 4 0) sourceC2633) = raw36355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36355; decide +kernel
    rw [ha]
    exact (canonical36355 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2633 + difference 0 5) (sourceB2633 + difference 5 0) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2633 + difference 0 5) (sourceB2633 + difference 5 0) sourceC2633) = raw36891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36891; decide +kernel
    rw [ha]
    exact (canonical36891 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2633 + difference 1 0) (sourceB2633 + difference 0 1) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5345) := by
    have ha : (tripleCharges (sourceA2633 + difference 1 0) (sourceB2633 + difference 0 1) sourceC2633) = raw36371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36371; decide +kernel
    rw [ha]
    exact (canonical36371 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2633 + difference 1 2) (sourceB2633 + difference 2 1) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5391) := by
    have ha : (tripleCharges (sourceA2633 + difference 1 2) (sourceB2633 + difference 2 1) sourceC2633) = raw36373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36373; decide +kernel
    rw [ha]
    exact (canonical36373 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2633 + difference 1 3) (sourceB2633 + difference 3 1) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2633 + difference 1 3) (sourceB2633 + difference 3 1) sourceC2633) = raw36374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36374; decide +kernel
    rw [ha]
    exact (canonical36374 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2633 + difference 1 4) (sourceB2633 + difference 4 1) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2633 + difference 1 4) (sourceB2633 + difference 4 1) sourceC2633) = raw36892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36892; decide +kernel
    rw [ha]
    exact (canonical36892 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2633 + difference 1 5) (sourceB2633 + difference 5 1) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA2633 + difference 1 5) (sourceB2633 + difference 5 1) sourceC2633) = raw36375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36375; decide +kernel
    rw [ha]
    exact (canonical36375 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2633 + difference 2 0) (sourceB2633 + difference 0 2) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2633 + difference 2 0) (sourceB2633 + difference 0 2) sourceC2633) = raw36893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36893; decide +kernel
    rw [ha]
    exact (canonical36893 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2633 + difference 2 1) (sourceB2633 + difference 1 2) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5017) := by
    have ha : (tripleCharges (sourceA2633 + difference 2 1) (sourceB2633 + difference 1 2) sourceC2633) = raw36894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36894; decide +kernel
    rw [ha]
    exact (canonical36894 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2633 + difference 2 3) (sourceB2633 + difference 3 2) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2633 + difference 2 3) (sourceB2633 + difference 3 2) sourceC2633) = raw36895 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36895; decide +kernel
    rw [ha]
    exact (canonical36895 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2633 + difference 2 4) (sourceB2633 + difference 4 2) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2633 + difference 2 4) (sourceB2633 + difference 4 2) sourceC2633) = raw36363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36363; decide +kernel
    rw [ha]
    exact (canonical36363 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2633 + difference 2 5) (sourceB2633 + difference 5 2) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2633 + difference 2 5) (sourceB2633 + difference 5 2) sourceC2633) = raw36523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36523; decide +kernel
    rw [ha]
    exact (canonical36523 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2633 + difference 3 0) (sourceB2633 + difference 0 3) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5314) := by
    have ha : (tripleCharges (sourceA2633 + difference 3 0) (sourceB2633 + difference 0 3) sourceC2633) = raw36896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36896; decide +kernel
    rw [ha]
    exact (canonical36896 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2633 + difference 3 1) (sourceB2633 + difference 1 3) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4987) := by
    have ha : (tripleCharges (sourceA2633 + difference 3 1) (sourceB2633 + difference 1 3) sourceC2633) = raw36897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36897; decide +kernel
    rw [ha]
    exact (canonical36897 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2633 + difference 3 2) (sourceB2633 + difference 2 3) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5333) := by
    have ha : (tripleCharges (sourceA2633 + difference 3 2) (sourceB2633 + difference 2 3) sourceC2633) = raw36898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36898; decide +kernel
    rw [ha]
    exact (canonical36898 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2633 + difference 3 4) (sourceB2633 + difference 4 3) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA2633 + difference 3 4) (sourceB2633 + difference 4 3) sourceC2633) = raw36367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36367; decide +kernel
    rw [ha]
    exact (canonical36367 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2633 + difference 3 5) (sourceB2633 + difference 5 3) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2633 + difference 3 5) (sourceB2633 + difference 5 3) sourceC2633) = raw36899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36899; decide +kernel
    rw [ha]
    exact (canonical36899 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2633 + difference 4 0) (sourceB2633 + difference 0 4) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5314) := by
    have ha : (tripleCharges (sourceA2633 + difference 4 0) (sourceB2633 + difference 0 4) sourceC2633) = raw36900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36900; decide +kernel
    rw [ha]
    exact (canonical36900 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2633 + difference 4 1) (sourceB2633 + difference 1 4) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4987) := by
    have ha : (tripleCharges (sourceA2633 + difference 4 1) (sourceB2633 + difference 1 4) sourceC2633) = raw36901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36901; decide +kernel
    rw [ha]
    exact (canonical36901 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2633 + difference 4 2) (sourceB2633 + difference 2 4) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5333) := by
    have ha : (tripleCharges (sourceA2633 + difference 4 2) (sourceB2633 + difference 2 4) sourceC2633) = raw36902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36902; decide +kernel
    rw [ha]
    exact (canonical36902 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2633 + difference 4 3) (sourceB2633 + difference 3 4) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA2633 + difference 4 3) (sourceB2633 + difference 3 4) sourceC2633) = raw36903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36903; decide +kernel
    rw [ha]
    exact (canonical36903 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2633 + difference 4 5) (sourceB2633 + difference 5 4) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2633 + difference 4 5) (sourceB2633 + difference 5 4) sourceC2633) = raw36904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36904; decide +kernel
    rw [ha]
    exact (canonical36904 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2633 + difference 5 0) (sourceB2633 + difference 0 5) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5025) := by
    have ha : (tripleCharges (sourceA2633 + difference 5 0) (sourceB2633 + difference 0 5) sourceC2633) = raw36905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36905; decide +kernel
    rw [ha]
    exact (canonical36905 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2633 + difference 5 1) (sourceB2633 + difference 1 5) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4986) := by
    have ha : (tripleCharges (sourceA2633 + difference 5 1) (sourceB2633 + difference 1 5) sourceC2633) = raw36906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36906; decide +kernel
    rw [ha]
    exact (canonical36906 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2633 + difference 5 2) (sourceB2633 + difference 2 5) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5030) := by
    have ha : (tripleCharges (sourceA2633 + difference 5 2) (sourceB2633 + difference 2 5) sourceC2633) = raw36907 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36907; decide +kernel
    rw [ha]
    exact (canonical36907 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2633 + difference 5 3) (sourceB2633 + difference 3 5) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2633 + difference 5 3) (sourceB2633 + difference 3 5) sourceC2633) = raw36908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36908; decide +kernel
    rw [ha]
    exact (canonical36908 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2633 + difference 5 4) (sourceB2633 + difference 4 5) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2633 + difference 5 4) (sourceB2633 + difference 4 5) sourceC2633) = raw36377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36377; decide +kernel
    rw [ha]
    exact (canonical36377 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2633 sourceB2633 sourceC2633
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2633, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2634 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2634 : Charge := ![0, 0, 1, 0, 0, -1]
def sourceC2634 : Charge := ![2, 2, -1, -1, -1, -1]
def sourceForm2634 : Integer.Sparse Master := [(Sum.inr 4087, 1), (Sum.inr 4904, 2), (Sum.inr 4906, 4), (Sum.inr 4916, 2), (Sum.inr 4998, 2), (Sum.inr 5118, 1), (Sum.inr 5142, 2), (Sum.inr 5319, 2), (Sum.inr 5321, 2), (Sum.inr 5325, 4), (Sum.inr 5363, 2), (Sum.inr 5365, 4), (Sum.inr 5366, 2)]

theorem sourceEq2634 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2634 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2634 + difference 0 1) (sourceB2634 + difference 1 0) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA2634 + difference 0 1) (sourceB2634 + difference 1 0) sourceC2634) = raw36909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36909; decide +kernel
    rw [ha]
    exact (canonical36909 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2634 + difference 0 2) (sourceB2634 + difference 2 0) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5363) := by
    have ha : (tripleCharges (sourceA2634 + difference 0 2) (sourceB2634 + difference 2 0) sourceC2634) = raw36910 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36910; decide +kernel
    rw [ha]
    exact (canonical36910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2634 + difference 0 3) (sourceB2634 + difference 3 0) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA2634 + difference 0 3) (sourceB2634 + difference 3 0) sourceC2634) = raw36911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36911; decide +kernel
    rw [ha]
    exact (canonical36911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2634 + difference 0 4) (sourceB2634 + difference 4 0) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA2634 + difference 0 4) (sourceB2634 + difference 4 0) sourceC2634) = raw36912 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36912; decide +kernel
    rw [ha]
    exact (canonical36912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2634 + difference 0 5) (sourceB2634 + difference 5 0) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5366) := by
    have ha : (tripleCharges (sourceA2634 + difference 0 5) (sourceB2634 + difference 5 0) sourceC2634) = raw36913 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36913; decide +kernel
    rw [ha]
    exact (canonical36913 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2634 + difference 1 0) (sourceB2634 + difference 0 1) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA2634 + difference 1 0) (sourceB2634 + difference 0 1) sourceC2634) = raw36914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36914; decide +kernel
    rw [ha]
    exact (canonical36914 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2634 + difference 1 2) (sourceB2634 + difference 2 1) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5363) := by
    have ha : (tripleCharges (sourceA2634 + difference 1 2) (sourceB2634 + difference 2 1) sourceC2634) = raw36915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36915; decide +kernel
    rw [ha]
    exact (canonical36915 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2634 + difference 1 3) (sourceB2634 + difference 3 1) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA2634 + difference 1 3) (sourceB2634 + difference 3 1) sourceC2634) = raw36916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36916; decide +kernel
    rw [ha]
    exact (canonical36916 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2634 + difference 1 4) (sourceB2634 + difference 4 1) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA2634 + difference 1 4) (sourceB2634 + difference 4 1) sourceC2634) = raw36917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36917; decide +kernel
    rw [ha]
    exact (canonical36917 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2634 + difference 1 5) (sourceB2634 + difference 5 1) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5366) := by
    have ha : (tripleCharges (sourceA2634 + difference 1 5) (sourceB2634 + difference 5 1) sourceC2634) = raw36918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36918; decide +kernel
    rw [ha]
    exact (canonical36918 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2634 + difference 2 0) (sourceB2634 + difference 0 2) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4916) := by
    have ha : (tripleCharges (sourceA2634 + difference 2 0) (sourceB2634 + difference 0 2) sourceC2634) = raw36919 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36919; decide +kernel
    rw [ha]
    exact (canonical36919 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2634 + difference 2 1) (sourceB2634 + difference 1 2) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4916) := by
    have ha : (tripleCharges (sourceA2634 + difference 2 1) (sourceB2634 + difference 1 2) sourceC2634) = raw36920 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36920; decide +kernel
    rw [ha]
    exact (canonical36920 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2634 + difference 2 3) (sourceB2634 + difference 3 2) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5325) := by
    have ha : (tripleCharges (sourceA2634 + difference 2 3) (sourceB2634 + difference 3 2) sourceC2634) = raw36921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36921; decide +kernel
    rw [ha]
    exact (canonical36921 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2634 + difference 2 4) (sourceB2634 + difference 4 2) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5325) := by
    have ha : (tripleCharges (sourceA2634 + difference 2 4) (sourceB2634 + difference 4 2) sourceC2634) = raw36922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36922; decide +kernel
    rw [ha]
    exact (canonical36922 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2634 + difference 2 5) (sourceB2634 + difference 5 2) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (tripleCharges (sourceA2634 + difference 2 5) (sourceB2634 + difference 5 2) sourceC2634) = raw36923 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36923; decide +kernel
    rw [ha]
    exact (canonical36923 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2634 + difference 3 0) (sourceB2634 + difference 0 3) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4906) := by
    have ha : (tripleCharges (sourceA2634 + difference 3 0) (sourceB2634 + difference 0 3) sourceC2634) = raw36924 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36924; decide +kernel
    rw [ha]
    exact (canonical36924 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2634 + difference 3 1) (sourceB2634 + difference 1 3) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4906) := by
    have ha : (tripleCharges (sourceA2634 + difference 3 1) (sourceB2634 + difference 1 3) sourceC2634) = raw36925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36925; decide +kernel
    rw [ha]
    exact (canonical36925 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2634 + difference 3 2) (sourceB2634 + difference 2 3) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5319) := by
    have ha : (tripleCharges (sourceA2634 + difference 3 2) (sourceB2634 + difference 2 3) sourceC2634) = raw36926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36926; decide +kernel
    rw [ha]
    exact (canonical36926 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2634 + difference 3 4) (sourceB2634 + difference 4 3) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5321) := by
    have ha : (tripleCharges (sourceA2634 + difference 3 4) (sourceB2634 + difference 4 3) sourceC2634) = raw36927 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36927; decide +kernel
    rw [ha]
    exact (canonical36927 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2634 + difference 3 5) (sourceB2634 + difference 5 3) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5325) := by
    have ha : (tripleCharges (sourceA2634 + difference 3 5) (sourceB2634 + difference 5 3) sourceC2634) = raw36928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36928; decide +kernel
    rw [ha]
    exact (canonical36928 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2634 + difference 4 0) (sourceB2634 + difference 0 4) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4906) := by
    have ha : (tripleCharges (sourceA2634 + difference 4 0) (sourceB2634 + difference 0 4) sourceC2634) = raw36929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36929; decide +kernel
    rw [ha]
    exact (canonical36929 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2634 + difference 4 1) (sourceB2634 + difference 1 4) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4906) := by
    have ha : (tripleCharges (sourceA2634 + difference 4 1) (sourceB2634 + difference 1 4) sourceC2634) = raw36930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36930; decide +kernel
    rw [ha]
    exact (canonical36930 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2634 + difference 4 2) (sourceB2634 + difference 2 4) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5319) := by
    have ha : (tripleCharges (sourceA2634 + difference 4 2) (sourceB2634 + difference 2 4) sourceC2634) = raw36931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36931; decide +kernel
    rw [ha]
    exact (canonical36931 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2634 + difference 4 3) (sourceB2634 + difference 3 4) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5321) := by
    have ha : (tripleCharges (sourceA2634 + difference 4 3) (sourceB2634 + difference 3 4) sourceC2634) = raw36932 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36932; decide +kernel
    rw [ha]
    exact (canonical36932 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2634 + difference 4 5) (sourceB2634 + difference 5 4) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5325) := by
    have ha : (tripleCharges (sourceA2634 + difference 4 5) (sourceB2634 + difference 5 4) sourceC2634) = raw36933 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36933; decide +kernel
    rw [ha]
    exact (canonical36933 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2634 + difference 5 0) (sourceB2634 + difference 0 5) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4904) := by
    have ha : (tripleCharges (sourceA2634 + difference 5 0) (sourceB2634 + difference 0 5) sourceC2634) = raw36934 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36934; decide +kernel
    rw [ha]
    exact (canonical36934 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2634 + difference 5 1) (sourceB2634 + difference 1 5) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4904) := by
    have ha : (tripleCharges (sourceA2634 + difference 5 1) (sourceB2634 + difference 1 5) sourceC2634) = raw36935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36935; decide +kernel
    rw [ha]
    exact (canonical36935 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2634 + difference 5 2) (sourceB2634 + difference 2 5) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5118) := by
    have ha : (tripleCharges (sourceA2634 + difference 5 2) (sourceB2634 + difference 2 5) sourceC2634) = raw36936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36936; decide +kernel
    rw [ha]
    exact (canonical36936 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2634 + difference 5 3) (sourceB2634 + difference 3 5) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5142) := by
    have ha : (tripleCharges (sourceA2634 + difference 5 3) (sourceB2634 + difference 3 5) sourceC2634) = raw36937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36937; decide +kernel
    rw [ha]
    exact (canonical36937 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2634 + difference 5 4) (sourceB2634 + difference 4 5) sourceC2634) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5142) := by
    have ha : (tripleCharges (sourceA2634 + difference 5 4) (sourceB2634 + difference 4 5) sourceC2634) = raw36938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2634 sourceB2634 sourceC2634 difference raw36938; decide +kernel
    rw [ha]
    exact (canonical36938 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2634 sourceB2634 sourceC2634
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2634, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2635 : Charge := ![0, 0, 1, 0, 0, -1]
def sourceB2635 : Charge := ![2, 2, -1, -1, -1, -1]
def sourceC2635 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceForm2635 : Integer.Sparse Master := [(Sum.inr 4088, 1), (Sum.inr 4911, 2), (Sum.inr 4912, 4), (Sum.inr 4917, 2), (Sum.inr 5013, 2), (Sum.inr 5323, 2), (Sum.inr 5324, 2), (Sum.inr 5326, 4), (Sum.inr 5328, 1), (Sum.inr 5331, 2), (Sum.inr 5352, 4), (Sum.inr 5354, 2), (Sum.inr 5369, 2)]

theorem sourceEq2635 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2635 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2635 + difference 0 1) (sourceB2635 + difference 1 0) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5013) := by
    have ha : (tripleCharges (sourceA2635 + difference 0 1) (sourceB2635 + difference 1 0) sourceC2635) = raw36522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36522; decide +kernel
    rw [ha]
    exact (canonical36522 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2635 + difference 0 2) (sourceB2635 + difference 2 0) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2635 + difference 0 2) (sourceB2635 + difference 2 0) sourceC2635) = raw36523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36523; decide +kernel
    rw [ha]
    exact (canonical36523 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2635 + difference 0 3) (sourceB2635 + difference 3 0) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2635 + difference 0 3) (sourceB2635 + difference 3 0) sourceC2635) = raw36524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36524; decide +kernel
    rw [ha]
    exact (canonical36524 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2635 + difference 0 4) (sourceB2635 + difference 4 0) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2635 + difference 0 4) (sourceB2635 + difference 4 0) sourceC2635) = raw36939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36939; decide +kernel
    rw [ha]
    exact (canonical36939 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2635 + difference 0 5) (sourceB2635 + difference 5 0) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2635 + difference 0 5) (sourceB2635 + difference 5 0) sourceC2635) = raw36525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36525; decide +kernel
    rw [ha]
    exact (canonical36525 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2635 + difference 1 0) (sourceB2635 + difference 0 1) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5013) := by
    have ha : (tripleCharges (sourceA2635 + difference 1 0) (sourceB2635 + difference 0 1) sourceC2635) = raw36940 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36940; decide +kernel
    rw [ha]
    exact (canonical36940 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2635 + difference 1 2) (sourceB2635 + difference 2 1) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2635 + difference 1 2) (sourceB2635 + difference 2 1) sourceC2635) = raw35628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw35628; decide +kernel
    rw [ha]
    exact (canonical35628 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2635 + difference 1 3) (sourceB2635 + difference 3 1) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2635 + difference 1 3) (sourceB2635 + difference 3 1) sourceC2635) = raw35624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw35624; decide +kernel
    rw [ha]
    exact (canonical35624 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2635 + difference 1 4) (sourceB2635 + difference 4 1) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2635 + difference 1 4) (sourceB2635 + difference 4 1) sourceC2635) = raw35835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw35835; decide +kernel
    rw [ha]
    exact (canonical35835 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2635 + difference 1 5) (sourceB2635 + difference 5 1) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2635 + difference 1 5) (sourceB2635 + difference 5 1) sourceC2635) = raw35930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw35930; decide +kernel
    rw [ha]
    exact (canonical35930 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2635 + difference 2 0) (sourceB2635 + difference 0 2) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4917) := by
    have ha : (tripleCharges (sourceA2635 + difference 2 0) (sourceB2635 + difference 0 2) sourceC2635) = raw36941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36941; decide +kernel
    rw [ha]
    exact (canonical36941 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2635 + difference 2 1) (sourceB2635 + difference 1 2) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4917) := by
    have ha : (tripleCharges (sourceA2635 + difference 2 1) (sourceB2635 + difference 1 2) sourceC2635) = raw36942 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36942; decide +kernel
    rw [ha]
    exact (canonical36942 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2635 + difference 2 3) (sourceB2635 + difference 3 2) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5326) := by
    have ha : (tripleCharges (sourceA2635 + difference 2 3) (sourceB2635 + difference 3 2) sourceC2635) = raw36943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36943; decide +kernel
    rw [ha]
    exact (canonical36943 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2635 + difference 2 4) (sourceB2635 + difference 4 2) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5326) := by
    have ha : (tripleCharges (sourceA2635 + difference 2 4) (sourceB2635 + difference 4 2) sourceC2635) = raw36511 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36511; decide +kernel
    rw [ha]
    exact (canonical36511 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2635 + difference 2 5) (sourceB2635 + difference 5 2) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5328) := by
    have ha : (tripleCharges (sourceA2635 + difference 2 5) (sourceB2635 + difference 5 2) sourceC2635) = raw36944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36944; decide +kernel
    rw [ha]
    exact (canonical36944 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2635 + difference 3 0) (sourceB2635 + difference 0 3) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4912) := by
    have ha : (tripleCharges (sourceA2635 + difference 3 0) (sourceB2635 + difference 0 3) sourceC2635) = raw36945 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36945; decide +kernel
    rw [ha]
    exact (canonical36945 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2635 + difference 3 1) (sourceB2635 + difference 1 3) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4912) := by
    have ha : (tripleCharges (sourceA2635 + difference 3 1) (sourceB2635 + difference 1 3) sourceC2635) = raw36946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36946; decide +kernel
    rw [ha]
    exact (canonical36946 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2635 + difference 3 2) (sourceB2635 + difference 2 3) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5331) := by
    have ha : (tripleCharges (sourceA2635 + difference 3 2) (sourceB2635 + difference 2 3) sourceC2635) = raw36947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36947; decide +kernel
    rw [ha]
    exact (canonical36947 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2635 + difference 3 4) (sourceB2635 + difference 4 3) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5324) := by
    have ha : (tripleCharges (sourceA2635 + difference 3 4) (sourceB2635 + difference 4 3) sourceC2635) = raw36516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36516; decide +kernel
    rw [ha]
    exact (canonical36516 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2635 + difference 3 5) (sourceB2635 + difference 5 3) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5326) := by
    have ha : (tripleCharges (sourceA2635 + difference 3 5) (sourceB2635 + difference 5 3) sourceC2635) = raw36948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36948; decide +kernel
    rw [ha]
    exact (canonical36948 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2635 + difference 4 0) (sourceB2635 + difference 0 4) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4912) := by
    have ha : (tripleCharges (sourceA2635 + difference 4 0) (sourceB2635 + difference 0 4) sourceC2635) = raw36949 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36949; decide +kernel
    rw [ha]
    exact (canonical36949 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2635 + difference 4 1) (sourceB2635 + difference 1 4) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4912) := by
    have ha : (tripleCharges (sourceA2635 + difference 4 1) (sourceB2635 + difference 1 4) sourceC2635) = raw36950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36950; decide +kernel
    rw [ha]
    exact (canonical36950 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2635 + difference 4 2) (sourceB2635 + difference 2 4) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5331) := by
    have ha : (tripleCharges (sourceA2635 + difference 4 2) (sourceB2635 + difference 2 4) sourceC2635) = raw36951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36951; decide +kernel
    rw [ha]
    exact (canonical36951 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2635 + difference 4 3) (sourceB2635 + difference 3 4) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5324) := by
    have ha : (tripleCharges (sourceA2635 + difference 4 3) (sourceB2635 + difference 3 4) sourceC2635) = raw36952 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36952; decide +kernel
    rw [ha]
    exact (canonical36952 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2635 + difference 4 5) (sourceB2635 + difference 5 4) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5326) := by
    have ha : (tripleCharges (sourceA2635 + difference 4 5) (sourceB2635 + difference 5 4) sourceC2635) = raw36953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36953; decide +kernel
    rw [ha]
    exact (canonical36953 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2635 + difference 5 0) (sourceB2635 + difference 0 5) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4911) := by
    have ha : (tripleCharges (sourceA2635 + difference 5 0) (sourceB2635 + difference 0 5) sourceC2635) = raw36954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36954; decide +kernel
    rw [ha]
    exact (canonical36954 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2635 + difference 5 1) (sourceB2635 + difference 1 5) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4911) := by
    have ha : (tripleCharges (sourceA2635 + difference 5 1) (sourceB2635 + difference 1 5) sourceC2635) = raw36955 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36955; decide +kernel
    rw [ha]
    exact (canonical36955 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2635 + difference 5 2) (sourceB2635 + difference 2 5) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2635 + difference 5 2) (sourceB2635 + difference 2 5) sourceC2635) = raw36893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36893; decide +kernel
    rw [ha]
    exact (canonical36893 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2635 + difference 5 3) (sourceB2635 + difference 3 5) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5323) := by
    have ha : (tripleCharges (sourceA2635 + difference 5 3) (sourceB2635 + difference 3 5) sourceC2635) = raw36956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36956; decide +kernel
    rw [ha]
    exact (canonical36956 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2635 + difference 5 4) (sourceB2635 + difference 4 5) sourceC2635) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5323) := by
    have ha : (tripleCharges (sourceA2635 + difference 5 4) (sourceB2635 + difference 4 5) sourceC2635) = raw36526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2635 sourceB2635 sourceC2635 difference raw36526; decide +kernel
    rw [ha]
    exact (canonical36526 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2635 sourceB2635 sourceC2635
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2635, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2636 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2636 : Charge := ![0, 0, 1, 0, -1, 0]
def sourceC2636 : Charge := ![2, 2, -1, -1, 0, -2]
def sourceForm2636 : Integer.Sparse Master := [(Sum.inr 4088, 1), (Sum.inr 4902, 2), (Sum.inr 4903, 2), (Sum.inr 4905, 2), (Sum.inr 4911, 2), (Sum.inr 4996, 2), (Sum.inr 5032, 1), (Sum.inr 5063, 1), (Sum.inr 5126, 1), (Sum.inr 5317, 1), (Sum.inr 5318, 1), (Sum.inr 5320, 1), (Sum.inr 5323, 1), (Sum.inr 5324, 1), (Sum.inr 5325, 1), (Sum.inr 5326, 1), (Sum.inr 5327, 1), (Sum.inr 5349, 2), (Sum.inr 5351, 2), (Sum.inr 5352, 2), (Sum.inr 5367, 2)]

theorem sourceEq2636 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2636 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2636 + difference 0 1) (sourceB2636 + difference 1 0) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA2636 + difference 0 1) (sourceB2636 + difference 1 0) sourceC2636) = raw36957 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36957; decide +kernel
    rw [ha]
    exact (canonical36957 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2636 + difference 0 2) (sourceB2636 + difference 2 0) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA2636 + difference 0 2) (sourceB2636 + difference 2 0) sourceC2636) = raw36958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36958; decide +kernel
    rw [ha]
    exact (canonical36958 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2636 + difference 0 3) (sourceB2636 + difference 3 0) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2636 + difference 0 3) (sourceB2636 + difference 3 0) sourceC2636) = raw36959 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36959; decide +kernel
    rw [ha]
    exact (canonical36959 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2636 + difference 0 4) (sourceB2636 + difference 4 0) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2636 + difference 0 4) (sourceB2636 + difference 4 0) sourceC2636) = raw36960 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36960; decide +kernel
    rw [ha]
    exact (canonical36960 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2636 + difference 0 5) (sourceB2636 + difference 5 0) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2636 + difference 0 5) (sourceB2636 + difference 5 0) sourceC2636) = raw36961 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36961; decide +kernel
    rw [ha]
    exact (canonical36961 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2636 + difference 1 0) (sourceB2636 + difference 0 1) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA2636 + difference 1 0) (sourceB2636 + difference 0 1) sourceC2636) = raw36962 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36962; decide +kernel
    rw [ha]
    exact (canonical36962 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2636 + difference 1 2) (sourceB2636 + difference 2 1) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA2636 + difference 1 2) (sourceB2636 + difference 2 1) sourceC2636) = raw36963 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36963; decide +kernel
    rw [ha]
    exact (canonical36963 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2636 + difference 1 3) (sourceB2636 + difference 3 1) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2636 + difference 1 3) (sourceB2636 + difference 3 1) sourceC2636) = raw36964 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36964; decide +kernel
    rw [ha]
    exact (canonical36964 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2636 + difference 1 4) (sourceB2636 + difference 4 1) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2636 + difference 1 4) (sourceB2636 + difference 4 1) sourceC2636) = raw36965 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36965; decide +kernel
    rw [ha]
    exact (canonical36965 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2636 + difference 1 5) (sourceB2636 + difference 5 1) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2636 + difference 1 5) (sourceB2636 + difference 5 1) sourceC2636) = raw36966 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36966; decide +kernel
    rw [ha]
    exact (canonical36966 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2636 + difference 2 0) (sourceB2636 + difference 0 2) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4911) := by
    have ha : (tripleCharges (sourceA2636 + difference 2 0) (sourceB2636 + difference 0 2) sourceC2636) = raw36967 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36967; decide +kernel
    rw [ha]
    exact (canonical36967 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2636 + difference 2 1) (sourceB2636 + difference 1 2) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4911) := by
    have ha : (tripleCharges (sourceA2636 + difference 2 1) (sourceB2636 + difference 1 2) sourceC2636) = raw36968 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36968; decide +kernel
    rw [ha]
    exact (canonical36968 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2636 + difference 2 3) (sourceB2636 + difference 3 2) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5323) := by
    have ha : (tripleCharges (sourceA2636 + difference 2 3) (sourceB2636 + difference 3 2) sourceC2636) = raw36969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36969; decide +kernel
    rw [ha]
    exact (canonical36969 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2636 + difference 2 4) (sourceB2636 + difference 4 2) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2636 + difference 2 4) (sourceB2636 + difference 4 2) sourceC2636) = raw36970 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36970; decide +kernel
    rw [ha]
    exact (canonical36970 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2636 + difference 2 5) (sourceB2636 + difference 5 2) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5325) := by
    have ha : (tripleCharges (sourceA2636 + difference 2 5) (sourceB2636 + difference 5 2) sourceC2636) = raw36971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36971; decide +kernel
    rw [ha]
    exact (canonical36971 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2636 + difference 3 0) (sourceB2636 + difference 0 3) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4903) := by
    have ha : (tripleCharges (sourceA2636 + difference 3 0) (sourceB2636 + difference 0 3) sourceC2636) = raw36972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36972; decide +kernel
    rw [ha]
    exact (canonical36972 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2636 + difference 3 1) (sourceB2636 + difference 1 3) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4903) := by
    have ha : (tripleCharges (sourceA2636 + difference 3 1) (sourceB2636 + difference 1 3) sourceC2636) = raw36973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36973; decide +kernel
    rw [ha]
    exact (canonical36973 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2636 + difference 3 2) (sourceB2636 + difference 2 3) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5317) := by
    have ha : (tripleCharges (sourceA2636 + difference 3 2) (sourceB2636 + difference 2 3) sourceC2636) = raw36974 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36974; decide +kernel
    rw [ha]
    exact (canonical36974 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2636 + difference 3 4) (sourceB2636 + difference 4 3) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5327) := by
    have ha : (tripleCharges (sourceA2636 + difference 3 4) (sourceB2636 + difference 4 3) sourceC2636) = raw36975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36975; decide +kernel
    rw [ha]
    exact (canonical36975 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2636 + difference 3 5) (sourceB2636 + difference 5 3) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5324) := by
    have ha : (tripleCharges (sourceA2636 + difference 3 5) (sourceB2636 + difference 5 3) sourceC2636) = raw36976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36976; decide +kernel
    rw [ha]
    exact (canonical36976 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2636 + difference 4 0) (sourceB2636 + difference 0 4) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4905) := by
    have ha : (tripleCharges (sourceA2636 + difference 4 0) (sourceB2636 + difference 0 4) sourceC2636) = raw36977 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36977; decide +kernel
    rw [ha]
    exact (canonical36977 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2636 + difference 4 1) (sourceB2636 + difference 1 4) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4905) := by
    have ha : (tripleCharges (sourceA2636 + difference 4 1) (sourceB2636 + difference 1 4) sourceC2636) = raw36978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36978; decide +kernel
    rw [ha]
    exact (canonical36978 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2636 + difference 4 2) (sourceB2636 + difference 2 4) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5318) := by
    have ha : (tripleCharges (sourceA2636 + difference 4 2) (sourceB2636 + difference 2 4) sourceC2636) = raw36979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36979; decide +kernel
    rw [ha]
    exact (canonical36979 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2636 + difference 4 3) (sourceB2636 + difference 3 4) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5320) := by
    have ha : (tripleCharges (sourceA2636 + difference 4 3) (sourceB2636 + difference 3 4) sourceC2636) = raw36980 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36980; decide +kernel
    rw [ha]
    exact (canonical36980 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2636 + difference 4 5) (sourceB2636 + difference 5 4) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5326) := by
    have ha : (tripleCharges (sourceA2636 + difference 4 5) (sourceB2636 + difference 5 4) sourceC2636) = raw36981 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36981; decide +kernel
    rw [ha]
    exact (canonical36981 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2636 + difference 5 0) (sourceB2636 + difference 0 5) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4902) := by
    have ha : (tripleCharges (sourceA2636 + difference 5 0) (sourceB2636 + difference 0 5) sourceC2636) = raw36982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36982; decide +kernel
    rw [ha]
    exact (canonical36982 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2636 + difference 5 1) (sourceB2636 + difference 1 5) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4902) := by
    have ha : (tripleCharges (sourceA2636 + difference 5 1) (sourceB2636 + difference 1 5) sourceC2636) = raw36983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36983; decide +kernel
    rw [ha]
    exact (canonical36983 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2636 + difference 5 2) (sourceB2636 + difference 2 5) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5032) := by
    have ha : (tripleCharges (sourceA2636 + difference 5 2) (sourceB2636 + difference 2 5) sourceC2636) = raw36984 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36984; decide +kernel
    rw [ha]
    exact (canonical36984 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2636 + difference 5 3) (sourceB2636 + difference 3 5) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5126) := by
    have ha : (tripleCharges (sourceA2636 + difference 5 3) (sourceB2636 + difference 3 5) sourceC2636) = raw36985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36985; decide +kernel
    rw [ha]
    exact (canonical36985 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2636 + difference 5 4) (sourceB2636 + difference 4 5) sourceC2636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5063) := by
    have ha : (tripleCharges (sourceA2636 + difference 5 4) (sourceB2636 + difference 4 5) sourceC2636) = raw36986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2636 sourceB2636 sourceC2636 difference raw36986; decide +kernel
    rw [ha]
    exact (canonical36986 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2636 sourceB2636 sourceC2636
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2636, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2637 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2637 : Charge := ![0, 0, 0, 1, 0, -1]
def sourceC2637 : Charge := ![2, 2, 0, -2, -1, -1]
def sourceForm2637 : Integer.Sparse Master := [(Sum.inr 4088, 1), (Sum.inr 4912, 2), (Sum.inr 4919, 2), (Sum.inr 4921, 2), (Sum.inr 4923, 2), (Sum.inr 5018, 2), (Sum.inr 5120, 1), (Sum.inr 5156, 1), (Sum.inr 5193, 1), (Sum.inr 5314, 1), (Sum.inr 5316, 1), (Sum.inr 5324, 1), (Sum.inr 5325, 1), (Sum.inr 5326, 1), (Sum.inr 5327, 1), (Sum.inr 5330, 1), (Sum.inr 5331, 1), (Sum.inr 5346, 2), (Sum.inr 5368, 2), (Sum.inr 5369, 2), (Sum.inr 5370, 2)]

theorem sourceEq2637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2637 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2637 + difference 0 1) (sourceB2637 + difference 1 0) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA2637 + difference 0 1) (sourceB2637 + difference 1 0) sourceC2637) = raw36987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw36987; decide +kernel
    rw [ha]
    exact (canonical36987 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2637 + difference 0 2) (sourceB2637 + difference 2 0) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2637 + difference 0 2) (sourceB2637 + difference 2 0) sourceC2637) = raw36988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw36988; decide +kernel
    rw [ha]
    exact (canonical36988 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2637 + difference 0 3) (sourceB2637 + difference 3 0) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2637 + difference 0 3) (sourceB2637 + difference 3 0) sourceC2637) = raw36989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw36989; decide +kernel
    rw [ha]
    exact (canonical36989 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2637 + difference 0 4) (sourceB2637 + difference 4 0) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2637 + difference 0 4) (sourceB2637 + difference 4 0) sourceC2637) = raw36990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw36990; decide +kernel
    rw [ha]
    exact (canonical36990 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2637 + difference 0 5) (sourceB2637 + difference 5 0) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2637 + difference 0 5) (sourceB2637 + difference 5 0) sourceC2637) = raw36991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw36991; decide +kernel
    rw [ha]
    exact (canonical36991 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2637 + difference 1 0) (sourceB2637 + difference 0 1) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA2637 + difference 1 0) (sourceB2637 + difference 0 1) sourceC2637) = raw36992 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw36992; decide +kernel
    rw [ha]
    exact (canonical36992 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2637 + difference 1 2) (sourceB2637 + difference 2 1) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2637 + difference 1 2) (sourceB2637 + difference 2 1) sourceC2637) = raw36993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw36993; decide +kernel
    rw [ha]
    exact (canonical36993 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2637 + difference 1 3) (sourceB2637 + difference 3 1) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2637 + difference 1 3) (sourceB2637 + difference 3 1) sourceC2637) = raw36994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw36994; decide +kernel
    rw [ha]
    exact (canonical36994 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2637 + difference 1 4) (sourceB2637 + difference 4 1) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2637 + difference 1 4) (sourceB2637 + difference 4 1) sourceC2637) = raw36995 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw36995; decide +kernel
    rw [ha]
    exact (canonical36995 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2637 + difference 1 5) (sourceB2637 + difference 5 1) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2637 + difference 1 5) (sourceB2637 + difference 5 1) sourceC2637) = raw36996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw36996; decide +kernel
    rw [ha]
    exact (canonical36996 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2637 + difference 2 0) (sourceB2637 + difference 0 2) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4912) := by
    have ha : (tripleCharges (sourceA2637 + difference 2 0) (sourceB2637 + difference 0 2) sourceC2637) = raw36997 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw36997; decide +kernel
    rw [ha]
    exact (canonical36997 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2637 + difference 2 1) (sourceB2637 + difference 1 2) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4912) := by
    have ha : (tripleCharges (sourceA2637 + difference 2 1) (sourceB2637 + difference 1 2) sourceC2637) = raw36998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw36998; decide +kernel
    rw [ha]
    exact (canonical36998 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2637 + difference 2 3) (sourceB2637 + difference 3 2) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5326) := by
    have ha : (tripleCharges (sourceA2637 + difference 2 3) (sourceB2637 + difference 3 2) sourceC2637) = raw36999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw36999; decide +kernel
    rw [ha]
    exact (canonical36999 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2637 + difference 2 4) (sourceB2637 + difference 4 2) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5324) := by
    have ha : (tripleCharges (sourceA2637 + difference 2 4) (sourceB2637 + difference 4 2) sourceC2637) = raw37000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37000; decide +kernel
    rw [ha]
    exact (canonical37000 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2637 + difference 2 5) (sourceB2637 + difference 5 2) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5325) := by
    have ha : (tripleCharges (sourceA2637 + difference 2 5) (sourceB2637 + difference 5 2) sourceC2637) = raw37001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37001; decide +kernel
    rw [ha]
    exact (canonical37001 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2637 + difference 3 0) (sourceB2637 + difference 0 3) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4921) := by
    have ha : (tripleCharges (sourceA2637 + difference 3 0) (sourceB2637 + difference 0 3) sourceC2637) = raw37002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37002; decide +kernel
    rw [ha]
    exact (canonical37002 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2637 + difference 3 1) (sourceB2637 + difference 1 3) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4921) := by
    have ha : (tripleCharges (sourceA2637 + difference 3 1) (sourceB2637 + difference 1 3) sourceC2637) = raw37003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37003; decide +kernel
    rw [ha]
    exact (canonical37003 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2637 + difference 3 2) (sourceB2637 + difference 2 3) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5314) := by
    have ha : (tripleCharges (sourceA2637 + difference 3 2) (sourceB2637 + difference 2 3) sourceC2637) = raw37004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37004; decide +kernel
    rw [ha]
    exact (canonical37004 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2637 + difference 3 4) (sourceB2637 + difference 4 3) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5327) := by
    have ha : (tripleCharges (sourceA2637 + difference 3 4) (sourceB2637 + difference 4 3) sourceC2637) = raw37005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37005; decide +kernel
    rw [ha]
    exact (canonical37005 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2637 + difference 3 5) (sourceB2637 + difference 5 3) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2637 + difference 3 5) (sourceB2637 + difference 5 3) sourceC2637) = raw37006 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37006; decide +kernel
    rw [ha]
    exact (canonical37006 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2637 + difference 4 0) (sourceB2637 + difference 0 4) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4923) := by
    have ha : (tripleCharges (sourceA2637 + difference 4 0) (sourceB2637 + difference 0 4) sourceC2637) = raw37007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37007; decide +kernel
    rw [ha]
    exact (canonical37007 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2637 + difference 4 1) (sourceB2637 + difference 1 4) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4923) := by
    have ha : (tripleCharges (sourceA2637 + difference 4 1) (sourceB2637 + difference 1 4) sourceC2637) = raw37008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37008; decide +kernel
    rw [ha]
    exact (canonical37008 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2637 + difference 4 2) (sourceB2637 + difference 2 4) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5316) := by
    have ha : (tripleCharges (sourceA2637 + difference 4 2) (sourceB2637 + difference 2 4) sourceC2637) = raw37009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37009; decide +kernel
    rw [ha]
    exact (canonical37009 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2637 + difference 4 3) (sourceB2637 + difference 3 4) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5330) := by
    have ha : (tripleCharges (sourceA2637 + difference 4 3) (sourceB2637 + difference 3 4) sourceC2637) = raw37010 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37010; decide +kernel
    rw [ha]
    exact (canonical37010 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2637 + difference 4 5) (sourceB2637 + difference 5 4) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5331) := by
    have ha : (tripleCharges (sourceA2637 + difference 4 5) (sourceB2637 + difference 5 4) sourceC2637) = raw37011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37011; decide +kernel
    rw [ha]
    exact (canonical37011 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2637 + difference 5 0) (sourceB2637 + difference 0 5) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4919) := by
    have ha : (tripleCharges (sourceA2637 + difference 5 0) (sourceB2637 + difference 0 5) sourceC2637) = raw37012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37012; decide +kernel
    rw [ha]
    exact (canonical37012 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2637 + difference 5 1) (sourceB2637 + difference 1 5) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4919) := by
    have ha : (tripleCharges (sourceA2637 + difference 5 1) (sourceB2637 + difference 1 5) sourceC2637) = raw37013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37013; decide +kernel
    rw [ha]
    exact (canonical37013 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2637 + difference 5 2) (sourceB2637 + difference 2 5) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5120) := by
    have ha : (tripleCharges (sourceA2637 + difference 5 2) (sourceB2637 + difference 2 5) sourceC2637) = raw37014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37014; decide +kernel
    rw [ha]
    exact (canonical37014 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2637 + difference 5 3) (sourceB2637 + difference 3 5) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5156) := by
    have ha : (tripleCharges (sourceA2637 + difference 5 3) (sourceB2637 + difference 3 5) sourceC2637) = raw37015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37015; decide +kernel
    rw [ha]
    exact (canonical37015 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2637 + difference 5 4) (sourceB2637 + difference 4 5) sourceC2637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5193) := by
    have ha : (tripleCharges (sourceA2637 + difference 5 4) (sourceB2637 + difference 4 5) sourceC2637) = raw37016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2637 sourceB2637 sourceC2637 difference raw37016; decide +kernel
    rw [ha]
    exact (canonical37016 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2637 sourceB2637 sourceC2637
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2637, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2638 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2638 : Charge := ![2, 2, 0, -1, -1, -2]
def sourceC2638 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm2638 : Integer.Sparse Master := [(Sum.inr 4073, 2), (Sum.inr 4074, 2), (Sum.inr 4075, 4), (Sum.inr 4078, 1), (Sum.inr 4080, 2), (Sum.inr 4082, 2), (Sum.inr 4086, 2), (Sum.inr 4087, 1), (Sum.inr 4088, 4), (Sum.inr 4089, 2), (Sum.inr 4090, 2), (Sum.inr 4091, 2), (Sum.inr 4092, 4)]

theorem sourceEq2638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2638 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2638 + difference 0 1) (sourceB2638 + difference 1 0) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2638 + difference 0 1) (sourceB2638 + difference 1 0) sourceC2638) = raw37017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37017; decide +kernel
    rw [ha]
    exact (canonical37017 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2638 + difference 0 2) (sourceB2638 + difference 2 0) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2638 + difference 0 2) (sourceB2638 + difference 2 0) sourceC2638) = raw19404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw19404; decide +kernel
    rw [ha]
    exact (canonical19404 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2638 + difference 0 3) (sourceB2638 + difference 3 0) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2638 + difference 0 3) (sourceB2638 + difference 3 0) sourceC2638) = raw3448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw3448; decide +kernel
    rw [ha]
    exact (canonical3448 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2638 + difference 0 4) (sourceB2638 + difference 4 0) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2638 + difference 0 4) (sourceB2638 + difference 4 0) sourceC2638) = raw37018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37018; decide +kernel
    rw [ha]
    exact (canonical37018 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2638 + difference 0 5) (sourceB2638 + difference 5 0) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2638 + difference 0 5) (sourceB2638 + difference 5 0) sourceC2638) = raw3440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw3440; decide +kernel
    rw [ha]
    exact (canonical3440 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2638 + difference 1 0) (sourceB2638 + difference 0 1) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2638 + difference 1 0) (sourceB2638 + difference 0 1) sourceC2638) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2638 + difference 1 2) (sourceB2638 + difference 2 1) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2638 + difference 1 2) (sourceB2638 + difference 2 1) sourceC2638) = raw18338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw18338; decide +kernel
    rw [ha]
    exact (canonical18338 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2638 + difference 1 3) (sourceB2638 + difference 3 1) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2638 + difference 1 3) (sourceB2638 + difference 3 1) sourceC2638) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2638 + difference 1 4) (sourceB2638 + difference 4 1) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2638 + difference 1 4) (sourceB2638 + difference 4 1) sourceC2638) = raw2925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw2925; decide +kernel
    rw [ha]
    exact (canonical2925 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2638 + difference 1 5) (sourceB2638 + difference 5 1) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2638 + difference 1 5) (sourceB2638 + difference 5 1) sourceC2638) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2638 + difference 2 0) (sourceB2638 + difference 0 2) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2638 + difference 2 0) (sourceB2638 + difference 0 2) sourceC2638) = raw34405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw34405; decide +kernel
    rw [ha]
    exact (canonical34405 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2638 + difference 2 1) (sourceB2638 + difference 1 2) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2638 + difference 2 1) (sourceB2638 + difference 1 2) sourceC2638) = raw37019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37019; decide +kernel
    rw [ha]
    exact (canonical37019 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2638 + difference 2 3) (sourceB2638 + difference 3 2) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2638 + difference 2 3) (sourceB2638 + difference 3 2) sourceC2638) = raw18335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw18335; decide +kernel
    rw [ha]
    exact (canonical18335 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2638 + difference 2 4) (sourceB2638 + difference 4 2) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2638 + difference 2 4) (sourceB2638 + difference 4 2) sourceC2638) = raw37020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37020; decide +kernel
    rw [ha]
    exact (canonical37020 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2638 + difference 2 5) (sourceB2638 + difference 5 2) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (tripleCharges (sourceA2638 + difference 2 5) (sourceB2638 + difference 5 2) sourceC2638) = raw19360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw19360; decide +kernel
    rw [ha]
    exact (canonical19360 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2638 + difference 3 0) (sourceB2638 + difference 0 3) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2638 + difference 3 0) (sourceB2638 + difference 0 3) sourceC2638) = raw34407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw34407; decide +kernel
    rw [ha]
    exact (canonical34407 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2638 + difference 3 1) (sourceB2638 + difference 1 3) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2638 + difference 3 1) (sourceB2638 + difference 1 3) sourceC2638) = raw37021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37021; decide +kernel
    rw [ha]
    exact (canonical37021 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2638 + difference 3 2) (sourceB2638 + difference 2 3) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2638 + difference 3 2) (sourceB2638 + difference 2 3) sourceC2638) = raw37022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37022; decide +kernel
    rw [ha]
    exact (canonical37022 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2638 + difference 3 4) (sourceB2638 + difference 4 3) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (tripleCharges (sourceA2638 + difference 3 4) (sourceB2638 + difference 4 3) sourceC2638) = raw37023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37023; decide +kernel
    rw [ha]
    exact (canonical37023 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2638 + difference 3 5) (sourceB2638 + difference 5 3) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2638 + difference 3 5) (sourceB2638 + difference 5 3) sourceC2638) = raw19363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw19363; decide +kernel
    rw [ha]
    exact (canonical19363 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2638 + difference 4 0) (sourceB2638 + difference 0 4) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2638 + difference 4 0) (sourceB2638 + difference 0 4) sourceC2638) = raw31880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw31880; decide +kernel
    rw [ha]
    exact (canonical31880 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2638 + difference 4 1) (sourceB2638 + difference 1 4) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2638 + difference 4 1) (sourceB2638 + difference 1 4) sourceC2638) = raw35540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw35540; decide +kernel
    rw [ha]
    exact (canonical35540 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2638 + difference 4 2) (sourceB2638 + difference 2 4) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2638 + difference 4 2) (sourceB2638 + difference 2 4) sourceC2638) = raw35541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw35541; decide +kernel
    rw [ha]
    exact (canonical35541 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2638 + difference 4 3) (sourceB2638 + difference 3 4) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (tripleCharges (sourceA2638 + difference 4 3) (sourceB2638 + difference 3 4) sourceC2638) = raw18339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw18339; decide +kernel
    rw [ha]
    exact (canonical18339 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2638 + difference 4 5) (sourceB2638 + difference 5 4) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2638 + difference 4 5) (sourceB2638 + difference 5 4) sourceC2638) = raw19367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw19367; decide +kernel
    rw [ha]
    exact (canonical19367 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2638 + difference 5 0) (sourceB2638 + difference 0 5) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2638 + difference 5 0) (sourceB2638 + difference 0 5) sourceC2638) = raw29297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw29297; decide +kernel
    rw [ha]
    exact (canonical29297 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2638 + difference 5 1) (sourceB2638 + difference 1 5) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2638 + difference 5 1) (sourceB2638 + difference 1 5) sourceC2638) = raw37024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37024; decide +kernel
    rw [ha]
    exact (canonical37024 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2638 + difference 5 2) (sourceB2638 + difference 2 5) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2638 + difference 5 2) (sourceB2638 + difference 2 5) sourceC2638) = raw37025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37025; decide +kernel
    rw [ha]
    exact (canonical37025 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2638 + difference 5 3) (sourceB2638 + difference 3 5) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2638 + difference 5 3) (sourceB2638 + difference 3 5) sourceC2638) = raw18342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw18342; decide +kernel
    rw [ha]
    exact (canonical18342 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2638 + difference 5 4) (sourceB2638 + difference 4 5) sourceC2638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2638 + difference 5 4) (sourceB2638 + difference 4 5) sourceC2638) = raw37026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2638 sourceB2638 sourceC2638 difference raw37026; decide +kernel
    rw [ha]
    exact (canonical37026 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2638 sourceB2638 sourceC2638
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2638, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2639 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2639 : Charge := ![0, 2, -1, -1, -1, 1]
def sourceC2639 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm2639 : Integer.Sparse Master := [(Sum.inr 4672, 3), (Sum.inr 4685, 1), (Sum.inr 4859, 1), (Sum.inr 4967, 1), (Sum.inr 4969, 3), (Sum.inr 5166, 1), (Sum.inr 5374, 3), (Sum.inr 5383, 1), (Sum.inr 5384, 6), (Sum.inr 5387, 3), (Sum.inr 5437, 1), (Sum.inr 5439, 3), (Sum.inr 5448, 3)]

theorem sourceEq2639 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2639 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2639 + difference 0 1) (sourceB2639 + difference 1 0) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4859) := by
    have ha : (tripleCharges (sourceA2639 + difference 0 1) (sourceB2639 + difference 1 0) sourceC2639) = raw37027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37027; decide +kernel
    rw [ha]
    exact (canonical37027 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2639 + difference 0 2) (sourceB2639 + difference 2 0) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA2639 + difference 0 2) (sourceB2639 + difference 2 0) sourceC2639) = raw18345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18345; decide +kernel
    rw [ha]
    exact (canonical18345 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2639 + difference 0 3) (sourceB2639 + difference 3 0) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA2639 + difference 0 3) (sourceB2639 + difference 3 0) sourceC2639) = raw37028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37028; decide +kernel
    rw [ha]
    exact (canonical37028 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2639 + difference 0 4) (sourceB2639 + difference 4 0) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA2639 + difference 0 4) (sourceB2639 + difference 4 0) sourceC2639) = raw37029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37029; decide +kernel
    rw [ha]
    exact (canonical37029 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2639 + difference 0 5) (sourceB2639 + difference 5 0) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA2639 + difference 0 5) (sourceB2639 + difference 5 0) sourceC2639) = raw37030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37030; decide +kernel
    rw [ha]
    exact (canonical37030 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2639 + difference 1 0) (sourceB2639 + difference 0 1) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5166) := by
    have ha : (tripleCharges (sourceA2639 + difference 1 0) (sourceB2639 + difference 0 1) sourceC2639) = raw12089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw12089; decide +kernel
    rw [ha]
    exact (canonical12089 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2639 + difference 1 2) (sourceB2639 + difference 2 1) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2639 + difference 1 2) (sourceB2639 + difference 2 1) sourceC2639) = raw12080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw12080; decide +kernel
    rw [ha]
    exact (canonical12080 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2639 + difference 1 3) (sourceB2639 + difference 3 1) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2639 + difference 1 3) (sourceB2639 + difference 3 1) sourceC2639) = raw18302 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18302; decide +kernel
    rw [ha]
    exact (canonical18302 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2639 + difference 1 4) (sourceB2639 + difference 4 1) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2639 + difference 1 4) (sourceB2639 + difference 4 1) sourceC2639) = raw18350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18350; decide +kernel
    rw [ha]
    exact (canonical18350 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2639 + difference 1 5) (sourceB2639 + difference 5 1) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA2639 + difference 1 5) (sourceB2639 + difference 5 1) sourceC2639) = raw18351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18351; decide +kernel
    rw [ha]
    exact (canonical18351 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2639 + difference 2 0) (sourceB2639 + difference 0 2) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4969) := by
    have ha : (tripleCharges (sourceA2639 + difference 2 0) (sourceB2639 + difference 0 2) sourceC2639) = raw34417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw34417; decide +kernel
    rw [ha]
    exact (canonical34417 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2639 + difference 2 1) (sourceB2639 + difference 1 2) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4672) := by
    have ha : (tripleCharges (sourceA2639 + difference 2 1) (sourceB2639 + difference 1 2) sourceC2639) = raw37031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37031; decide +kernel
    rw [ha]
    exact (canonical37031 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2639 + difference 2 3) (sourceB2639 + difference 3 2) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2639 + difference 2 3) (sourceB2639 + difference 3 2) sourceC2639) = raw37032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37032; decide +kernel
    rw [ha]
    exact (canonical37032 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2639 + difference 2 4) (sourceB2639 + difference 4 2) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2639 + difference 2 4) (sourceB2639 + difference 4 2) sourceC2639) = raw37033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37033; decide +kernel
    rw [ha]
    exact (canonical37033 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2639 + difference 2 5) (sourceB2639 + difference 5 2) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA2639 + difference 2 5) (sourceB2639 + difference 5 2) sourceC2639) = raw37034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37034; decide +kernel
    rw [ha]
    exact (canonical37034 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2639 + difference 3 0) (sourceB2639 + difference 0 3) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4969) := by
    have ha : (tripleCharges (sourceA2639 + difference 3 0) (sourceB2639 + difference 0 3) sourceC2639) = raw34421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw34421; decide +kernel
    rw [ha]
    exact (canonical34421 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2639 + difference 3 1) (sourceB2639 + difference 1 3) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4672) := by
    have ha : (tripleCharges (sourceA2639 + difference 3 1) (sourceB2639 + difference 1 3) sourceC2639) = raw37035 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37035; decide +kernel
    rw [ha]
    exact (canonical37035 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2639 + difference 3 2) (sourceB2639 + difference 2 3) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2639 + difference 3 2) (sourceB2639 + difference 2 3) sourceC2639) = raw18352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18352; decide +kernel
    rw [ha]
    exact (canonical18352 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2639 + difference 3 4) (sourceB2639 + difference 4 3) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2639 + difference 3 4) (sourceB2639 + difference 4 3) sourceC2639) = raw37036 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37036; decide +kernel
    rw [ha]
    exact (canonical37036 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2639 + difference 3 5) (sourceB2639 + difference 5 3) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA2639 + difference 3 5) (sourceB2639 + difference 5 3) sourceC2639) = raw37037 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37037; decide +kernel
    rw [ha]
    exact (canonical37037 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2639 + difference 4 0) (sourceB2639 + difference 0 4) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4969) := by
    have ha : (tripleCharges (sourceA2639 + difference 4 0) (sourceB2639 + difference 0 4) sourceC2639) = raw34424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw34424; decide +kernel
    rw [ha]
    exact (canonical34424 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2639 + difference 4 1) (sourceB2639 + difference 1 4) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4672) := by
    have ha : (tripleCharges (sourceA2639 + difference 4 1) (sourceB2639 + difference 1 4) sourceC2639) = raw37038 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37038; decide +kernel
    rw [ha]
    exact (canonical37038 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2639 + difference 4 2) (sourceB2639 + difference 2 4) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2639 + difference 4 2) (sourceB2639 + difference 2 4) sourceC2639) = raw18356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18356; decide +kernel
    rw [ha]
    exact (canonical18356 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2639 + difference 4 3) (sourceB2639 + difference 3 4) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2639 + difference 4 3) (sourceB2639 + difference 3 4) sourceC2639) = raw34788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw34788; decide +kernel
    rw [ha]
    exact (canonical34788 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2639 + difference 4 5) (sourceB2639 + difference 5 4) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA2639 + difference 4 5) (sourceB2639 + difference 5 4) sourceC2639) = raw37039 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37039; decide +kernel
    rw [ha]
    exact (canonical37039 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2639 + difference 5 0) (sourceB2639 + difference 0 5) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4967) := by
    have ha : (tripleCharges (sourceA2639 + difference 5 0) (sourceB2639 + difference 0 5) sourceC2639) = raw32031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw32031; decide +kernel
    rw [ha]
    exact (canonical32031 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2639 + difference 5 1) (sourceB2639 + difference 1 5) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4685) := by
    have ha : (tripleCharges (sourceA2639 + difference 5 1) (sourceB2639 + difference 1 5) sourceC2639) = raw35551 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw35551; decide +kernel
    rw [ha]
    exact (canonical35551 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2639 + difference 5 2) (sourceB2639 + difference 2 5) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2639 + difference 5 2) (sourceB2639 + difference 2 5) sourceC2639) = raw18303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18303; decide +kernel
    rw [ha]
    exact (canonical18303 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2639 + difference 5 3) (sourceB2639 + difference 3 5) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2639 + difference 5 3) (sourceB2639 + difference 3 5) sourceC2639) = raw18299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18299; decide +kernel
    rw [ha]
    exact (canonical18299 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2639 + difference 5 4) (sourceB2639 + difference 4 5) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2639 + difference 5 4) (sourceB2639 + difference 4 5) sourceC2639) = raw35552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw35552; decide +kernel
    rw [ha]
    exact (canonical35552 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2639 sourceB2639 sourceC2639
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2639, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2640 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2640 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2640 : Charge := ![0, 2, -1, -1, -1, 1]
def sourceForm2640 : Integer.Sparse Master := [(Sum.inr 4675, 1), (Sum.inr 4677, 3), (Sum.inr 4863, 1), (Sum.inr 4964, 3), (Sum.inr 4975, 1), (Sum.inr 5162, 1), (Sum.inr 5243, 3), (Sum.inr 5379, 6), (Sum.inr 5380, 3), (Sum.inr 5427, 1), (Sum.inr 5429, 3), (Sum.inr 5431, 3), (Sum.inr 5447, 1)]

theorem sourceEq2640 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2640 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2640 + difference 0 1) (sourceB2640 + difference 1 0) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA2640 + difference 0 1) (sourceB2640 + difference 1 0) sourceC2640) = raw37040 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37040; decide +kernel
    rw [ha]
    exact (canonical37040 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2640 + difference 0 2) (sourceB2640 + difference 2 0) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA2640 + difference 0 2) (sourceB2640 + difference 2 0) sourceC2640) = raw37041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37041; decide +kernel
    rw [ha]
    exact (canonical37041 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2640 + difference 0 3) (sourceB2640 + difference 3 0) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA2640 + difference 0 3) (sourceB2640 + difference 3 0) sourceC2640) = raw37042 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37042; decide +kernel
    rw [ha]
    exact (canonical37042 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2640 + difference 0 4) (sourceB2640 + difference 4 0) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA2640 + difference 0 4) (sourceB2640 + difference 4 0) sourceC2640) = raw37043 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37043; decide +kernel
    rw [ha]
    exact (canonical37043 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2640 + difference 0 5) (sourceB2640 + difference 5 0) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5427) := by
    have ha : (tripleCharges (sourceA2640 + difference 0 5) (sourceB2640 + difference 5 0) sourceC2640) = raw37044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37044; decide +kernel
    rw [ha]
    exact (canonical37044 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2640 + difference 1 0) (sourceB2640 + difference 0 1) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4863) := by
    have ha : (tripleCharges (sourceA2640 + difference 1 0) (sourceB2640 + difference 0 1) sourceC2640) = raw37045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37045; decide +kernel
    rw [ha]
    exact (canonical37045 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2640 + difference 1 2) (sourceB2640 + difference 2 1) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA2640 + difference 1 2) (sourceB2640 + difference 2 1) sourceC2640) = raw37046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37046; decide +kernel
    rw [ha]
    exact (canonical37046 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2640 + difference 1 3) (sourceB2640 + difference 3 1) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA2640 + difference 1 3) (sourceB2640 + difference 3 1) sourceC2640) = raw37047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37047; decide +kernel
    rw [ha]
    exact (canonical37047 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2640 + difference 1 4) (sourceB2640 + difference 4 1) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA2640 + difference 1 4) (sourceB2640 + difference 4 1) sourceC2640) = raw37048 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37048; decide +kernel
    rw [ha]
    exact (canonical37048 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2640 + difference 1 5) (sourceB2640 + difference 5 1) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA2640 + difference 1 5) (sourceB2640 + difference 5 1) sourceC2640) = raw37049 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37049; decide +kernel
    rw [ha]
    exact (canonical37049 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2640 + difference 2 0) (sourceB2640 + difference 0 2) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4677) := by
    have ha : (tripleCharges (sourceA2640 + difference 2 0) (sourceB2640 + difference 0 2) sourceC2640) = raw37050 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37050; decide +kernel
    rw [ha]
    exact (canonical37050 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2640 + difference 2 1) (sourceB2640 + difference 1 2) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4964) := by
    have ha : (tripleCharges (sourceA2640 + difference 2 1) (sourceB2640 + difference 1 2) sourceC2640) = raw37051 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37051; decide +kernel
    rw [ha]
    exact (canonical37051 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2640 + difference 2 3) (sourceB2640 + difference 3 2) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2640 + difference 2 3) (sourceB2640 + difference 3 2) sourceC2640) = raw37052 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37052; decide +kernel
    rw [ha]
    exact (canonical37052 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2640 + difference 2 4) (sourceB2640 + difference 4 2) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2640 + difference 2 4) (sourceB2640 + difference 4 2) sourceC2640) = raw37053 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37053; decide +kernel
    rw [ha]
    exact (canonical37053 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2640 + difference 2 5) (sourceB2640 + difference 5 2) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2640 + difference 2 5) (sourceB2640 + difference 5 2) sourceC2640) = raw37054 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37054; decide +kernel
    rw [ha]
    exact (canonical37054 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2640 + difference 3 0) (sourceB2640 + difference 0 3) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4677) := by
    have ha : (tripleCharges (sourceA2640 + difference 3 0) (sourceB2640 + difference 0 3) sourceC2640) = raw37055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37055; decide +kernel
    rw [ha]
    exact (canonical37055 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2640 + difference 3 1) (sourceB2640 + difference 1 3) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4964) := by
    have ha : (tripleCharges (sourceA2640 + difference 3 1) (sourceB2640 + difference 1 3) sourceC2640) = raw37056 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37056; decide +kernel
    rw [ha]
    exact (canonical37056 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2640 + difference 3 2) (sourceB2640 + difference 2 3) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2640 + difference 3 2) (sourceB2640 + difference 2 3) sourceC2640) = raw37057 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37057; decide +kernel
    rw [ha]
    exact (canonical37057 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2640 + difference 3 4) (sourceB2640 + difference 4 3) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2640 + difference 3 4) (sourceB2640 + difference 4 3) sourceC2640) = raw37058 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37058; decide +kernel
    rw [ha]
    exact (canonical37058 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2640 + difference 3 5) (sourceB2640 + difference 5 3) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2640 + difference 3 5) (sourceB2640 + difference 5 3) sourceC2640) = raw37059 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37059; decide +kernel
    rw [ha]
    exact (canonical37059 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2640 + difference 4 0) (sourceB2640 + difference 0 4) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4677) := by
    have ha : (tripleCharges (sourceA2640 + difference 4 0) (sourceB2640 + difference 0 4) sourceC2640) = raw37060 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37060; decide +kernel
    rw [ha]
    exact (canonical37060 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2640 + difference 4 1) (sourceB2640 + difference 1 4) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4964) := by
    have ha : (tripleCharges (sourceA2640 + difference 4 1) (sourceB2640 + difference 1 4) sourceC2640) = raw37061 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37061; decide +kernel
    rw [ha]
    exact (canonical37061 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2640 + difference 4 2) (sourceB2640 + difference 2 4) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2640 + difference 4 2) (sourceB2640 + difference 2 4) sourceC2640) = raw37062 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37062; decide +kernel
    rw [ha]
    exact (canonical37062 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2640 + difference 4 3) (sourceB2640 + difference 3 4) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2640 + difference 4 3) (sourceB2640 + difference 3 4) sourceC2640) = raw37063 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37063; decide +kernel
    rw [ha]
    exact (canonical37063 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2640 + difference 4 5) (sourceB2640 + difference 5 4) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2640 + difference 4 5) (sourceB2640 + difference 5 4) sourceC2640) = raw37064 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37064; decide +kernel
    rw [ha]
    exact (canonical37064 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2640 + difference 5 0) (sourceB2640 + difference 0 5) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4675) := by
    have ha : (tripleCharges (sourceA2640 + difference 5 0) (sourceB2640 + difference 0 5) sourceC2640) = raw37065 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37065; decide +kernel
    rw [ha]
    exact (canonical37065 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2640 + difference 5 1) (sourceB2640 + difference 1 5) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4975) := by
    have ha : (tripleCharges (sourceA2640 + difference 5 1) (sourceB2640 + difference 1 5) sourceC2640) = raw37066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37066; decide +kernel
    rw [ha]
    exact (canonical37066 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2640 + difference 5 2) (sourceB2640 + difference 2 5) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5243) := by
    have ha : (tripleCharges (sourceA2640 + difference 5 2) (sourceB2640 + difference 2 5) sourceC2640) = raw37067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37067; decide +kernel
    rw [ha]
    exact (canonical37067 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2640 + difference 5 3) (sourceB2640 + difference 3 5) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5243) := by
    have ha : (tripleCharges (sourceA2640 + difference 5 3) (sourceB2640 + difference 3 5) sourceC2640) = raw37068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37068; decide +kernel
    rw [ha]
    exact (canonical37068 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2640 + difference 5 4) (sourceB2640 + difference 4 5) sourceC2640) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5243) := by
    have ha : (tripleCharges (sourceA2640 + difference 5 4) (sourceB2640 + difference 4 5) sourceC2640) = raw37069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2640 sourceB2640 sourceC2640 difference raw37069; decide +kernel
    rw [ha]
    exact (canonical37069 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2640 sourceB2640 sourceC2640
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2640, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2641 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2641 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2641 : Charge := ![0, 2, -1, -1, -1, 1]
def sourceForm2641 : Integer.Sparse Master := [(Sum.inr 2139, 1), (Sum.inr 2142, 3), (Sum.inr 2232, 1), (Sum.inr 2690, 1), (Sum.inr 2697, 3), (Sum.inr 3554, 3), (Sum.inr 3563, 1), (Sum.inr 3832, 6), (Sum.inr 3836, 3), (Sum.inr 3844, 1), (Sum.inr 3846, 3), (Sum.inr 3875, 3), (Sum.inr 3909, 1)]

theorem sourceEq2641 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2641 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2641 + difference 0 1) (sourceB2641 + difference 1 0) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3563) := by
    have ha : (tripleCharges (sourceA2641 + difference 0 1) (sourceB2641 + difference 1 0) sourceC2641) = raw37070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37070; decide +kernel
    rw [ha]
    exact (canonical37070 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2641 + difference 0 2) (sourceB2641 + difference 2 0) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA2641 + difference 0 2) (sourceB2641 + difference 2 0) sourceC2641) = raw37071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37071; decide +kernel
    rw [ha]
    exact (canonical37071 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2641 + difference 0 3) (sourceB2641 + difference 3 0) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA2641 + difference 0 3) (sourceB2641 + difference 3 0) sourceC2641) = raw37072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37072; decide +kernel
    rw [ha]
    exact (canonical37072 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2641 + difference 0 4) (sourceB2641 + difference 4 0) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA2641 + difference 0 4) (sourceB2641 + difference 4 0) sourceC2641) = raw37073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37073; decide +kernel
    rw [ha]
    exact (canonical37073 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2641 + difference 0 5) (sourceB2641 + difference 5 0) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3844) := by
    have ha : (tripleCharges (sourceA2641 + difference 0 5) (sourceB2641 + difference 5 0) sourceC2641) = raw37074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37074; decide +kernel
    rw [ha]
    exact (canonical37074 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2641 + difference 1 0) (sourceB2641 + difference 0 1) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2232) := by
    have ha : (tripleCharges (sourceA2641 + difference 1 0) (sourceB2641 + difference 0 1) sourceC2641) = raw37075 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37075; decide +kernel
    rw [ha]
    exact (canonical37075 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2641 + difference 1 2) (sourceB2641 + difference 2 1) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA2641 + difference 1 2) (sourceB2641 + difference 2 1) sourceC2641) = raw37076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37076; decide +kernel
    rw [ha]
    exact (canonical37076 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2641 + difference 1 3) (sourceB2641 + difference 3 1) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA2641 + difference 1 3) (sourceB2641 + difference 3 1) sourceC2641) = raw37077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37077; decide +kernel
    rw [ha]
    exact (canonical37077 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2641 + difference 1 4) (sourceB2641 + difference 4 1) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA2641 + difference 1 4) (sourceB2641 + difference 4 1) sourceC2641) = raw37078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37078; decide +kernel
    rw [ha]
    exact (canonical37078 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2641 + difference 1 5) (sourceB2641 + difference 5 1) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA2641 + difference 1 5) (sourceB2641 + difference 5 1) sourceC2641) = raw37079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37079; decide +kernel
    rw [ha]
    exact (canonical37079 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2641 + difference 2 0) (sourceB2641 + difference 0 2) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2142) := by
    have ha : (tripleCharges (sourceA2641 + difference 2 0) (sourceB2641 + difference 0 2) sourceC2641) = raw37080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37080; decide +kernel
    rw [ha]
    exact (canonical37080 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2641 + difference 2 1) (sourceB2641 + difference 1 2) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3554) := by
    have ha : (tripleCharges (sourceA2641 + difference 2 1) (sourceB2641 + difference 1 2) sourceC2641) = raw37081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37081; decide +kernel
    rw [ha]
    exact (canonical37081 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2641 + difference 2 3) (sourceB2641 + difference 3 2) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2641 + difference 2 3) (sourceB2641 + difference 3 2) sourceC2641) = raw37082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37082; decide +kernel
    rw [ha]
    exact (canonical37082 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2641 + difference 2 4) (sourceB2641 + difference 4 2) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2641 + difference 2 4) (sourceB2641 + difference 4 2) sourceC2641) = raw37083 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37083; decide +kernel
    rw [ha]
    exact (canonical37083 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2641 + difference 2 5) (sourceB2641 + difference 5 2) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3836) := by
    have ha : (tripleCharges (sourceA2641 + difference 2 5) (sourceB2641 + difference 5 2) sourceC2641) = raw37084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37084; decide +kernel
    rw [ha]
    exact (canonical37084 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2641 + difference 3 0) (sourceB2641 + difference 0 3) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2142) := by
    have ha : (tripleCharges (sourceA2641 + difference 3 0) (sourceB2641 + difference 0 3) sourceC2641) = raw37085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37085; decide +kernel
    rw [ha]
    exact (canonical37085 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2641 + difference 3 1) (sourceB2641 + difference 1 3) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3554) := by
    have ha : (tripleCharges (sourceA2641 + difference 3 1) (sourceB2641 + difference 1 3) sourceC2641) = raw37086 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37086; decide +kernel
    rw [ha]
    exact (canonical37086 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2641 + difference 3 2) (sourceB2641 + difference 2 3) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2641 + difference 3 2) (sourceB2641 + difference 2 3) sourceC2641) = raw37087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37087; decide +kernel
    rw [ha]
    exact (canonical37087 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2641 + difference 3 4) (sourceB2641 + difference 4 3) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2641 + difference 3 4) (sourceB2641 + difference 4 3) sourceC2641) = raw37088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37088; decide +kernel
    rw [ha]
    exact (canonical37088 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2641 + difference 3 5) (sourceB2641 + difference 5 3) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3836) := by
    have ha : (tripleCharges (sourceA2641 + difference 3 5) (sourceB2641 + difference 5 3) sourceC2641) = raw37089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37089; decide +kernel
    rw [ha]
    exact (canonical37089 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2641 + difference 4 0) (sourceB2641 + difference 0 4) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2142) := by
    have ha : (tripleCharges (sourceA2641 + difference 4 0) (sourceB2641 + difference 0 4) sourceC2641) = raw37090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37090; decide +kernel
    rw [ha]
    exact (canonical37090 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2641 + difference 4 1) (sourceB2641 + difference 1 4) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3554) := by
    have ha : (tripleCharges (sourceA2641 + difference 4 1) (sourceB2641 + difference 1 4) sourceC2641) = raw37091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37091; decide +kernel
    rw [ha]
    exact (canonical37091 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2641 + difference 4 2) (sourceB2641 + difference 2 4) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2641 + difference 4 2) (sourceB2641 + difference 2 4) sourceC2641) = raw37092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37092; decide +kernel
    rw [ha]
    exact (canonical37092 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2641 + difference 4 3) (sourceB2641 + difference 3 4) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2641 + difference 4 3) (sourceB2641 + difference 3 4) sourceC2641) = raw37093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37093; decide +kernel
    rw [ha]
    exact (canonical37093 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2641 + difference 4 5) (sourceB2641 + difference 5 4) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3836) := by
    have ha : (tripleCharges (sourceA2641 + difference 4 5) (sourceB2641 + difference 5 4) sourceC2641) = raw37094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37094; decide +kernel
    rw [ha]
    exact (canonical37094 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2641 + difference 5 0) (sourceB2641 + difference 0 5) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2139) := by
    have ha : (tripleCharges (sourceA2641 + difference 5 0) (sourceB2641 + difference 0 5) sourceC2641) = raw37095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37095; decide +kernel
    rw [ha]
    exact (canonical37095 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2641 + difference 5 1) (sourceB2641 + difference 1 5) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2690) := by
    have ha : (tripleCharges (sourceA2641 + difference 5 1) (sourceB2641 + difference 1 5) sourceC2641) = raw37096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37096; decide +kernel
    rw [ha]
    exact (canonical37096 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2641 + difference 5 2) (sourceB2641 + difference 2 5) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA2641 + difference 5 2) (sourceB2641 + difference 2 5) sourceC2641) = raw37097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37097; decide +kernel
    rw [ha]
    exact (canonical37097 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2641 + difference 5 3) (sourceB2641 + difference 3 5) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA2641 + difference 5 3) (sourceB2641 + difference 3 5) sourceC2641) = raw37098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37098; decide +kernel
    rw [ha]
    exact (canonical37098 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2641 + difference 5 4) (sourceB2641 + difference 4 5) sourceC2641) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA2641 + difference 5 4) (sourceB2641 + difference 4 5) sourceC2641) = raw37099 := by
      apply Matrix.ext; unfold tripleCharges sourceA2641 sourceB2641 sourceC2641 difference raw37099; decide +kernel
    rw [ha]
    exact (canonical37099 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2641 sourceB2641 sourceC2641
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2641, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2642 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2642 : Charge := ![0, 2, -1, -1, 0, 0]
def sourceC2642 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm2642 : Integer.Sparse Master := [(Sum.inr 4676, 2), (Sum.inr 4679, 2), (Sum.inr 4864, 1), (Sum.inr 4968, 2), (Sum.inr 4971, 2), (Sum.inr 5167, 1), (Sum.inr 5378, 4), (Sum.inr 5380, 2), (Sum.inr 5387, 2), (Sum.inr 5388, 4), (Sum.inr 5431, 2), (Sum.inr 5433, 2), (Sum.inr 5440, 2), (Sum.inr 5450, 2)]

theorem sourceEq2642 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2642 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2642 + difference 0 1) (sourceB2642 + difference 1 0) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA2642 + difference 0 1) (sourceB2642 + difference 1 0) sourceC2642) = raw37100 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw37100; decide +kernel
    rw [ha]
    exact (canonical37100 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2642 + difference 0 2) (sourceB2642 + difference 2 0) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2642 + difference 0 2) (sourceB2642 + difference 2 0) sourceC2642) = raw35605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw35605; decide +kernel
    rw [ha]
    exact (canonical35605 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2642 + difference 0 3) (sourceB2642 + difference 3 0) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2642 + difference 0 3) (sourceB2642 + difference 3 0) sourceC2642) = raw37101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw37101; decide +kernel
    rw [ha]
    exact (canonical37101 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2642 + difference 0 4) (sourceB2642 + difference 4 0) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA2642 + difference 0 4) (sourceB2642 + difference 4 0) sourceC2642) = raw37102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw37102; decide +kernel
    rw [ha]
    exact (canonical37102 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2642 + difference 0 5) (sourceB2642 + difference 5 0) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA2642 + difference 0 5) (sourceB2642 + difference 5 0) sourceC2642) = raw37103 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw37103; decide +kernel
    rw [ha]
    exact (canonical37103 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2642 + difference 1 0) (sourceB2642 + difference 0 1) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2642 + difference 1 0) (sourceB2642 + difference 0 1) sourceC2642) = raw26640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw26640; decide +kernel
    rw [ha]
    exact (canonical26640 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2642 + difference 1 2) (sourceB2642 + difference 2 1) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA2642 + difference 1 2) (sourceB2642 + difference 2 1) sourceC2642) = raw32069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw32069; decide +kernel
    rw [ha]
    exact (canonical32069 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2642 + difference 1 3) (sourceB2642 + difference 3 1) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA2642 + difference 1 3) (sourceB2642 + difference 3 1) sourceC2642) = raw34427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw34427; decide +kernel
    rw [ha]
    exact (canonical34427 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2642 + difference 1 4) (sourceB2642 + difference 4 1) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2642 + difference 1 4) (sourceB2642 + difference 4 1) sourceC2642) = raw34428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw34428; decide +kernel
    rw [ha]
    exact (canonical34428 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2642 + difference 1 5) (sourceB2642 + difference 5 1) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2642 + difference 1 5) (sourceB2642 + difference 5 1) sourceC2642) = raw34429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw34429; decide +kernel
    rw [ha]
    exact (canonical34429 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2642 + difference 2 0) (sourceB2642 + difference 0 2) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4971) := by
    have ha : (tripleCharges (sourceA2642 + difference 2 0) (sourceB2642 + difference 0 2) sourceC2642) = raw34430 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw34430; decide +kernel
    rw [ha]
    exact (canonical34430 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2642 + difference 2 1) (sourceB2642 + difference 1 2) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4676) := by
    have ha : (tripleCharges (sourceA2642 + difference 2 1) (sourceB2642 + difference 1 2) sourceC2642) = raw37104 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw37104; decide +kernel
    rw [ha]
    exact (canonical37104 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2642 + difference 2 3) (sourceB2642 + difference 3 2) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2642 + difference 2 3) (sourceB2642 + difference 3 2) sourceC2642) = raw37105 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw37105; decide +kernel
    rw [ha]
    exact (canonical37105 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2642 + difference 2 4) (sourceB2642 + difference 4 2) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2642 + difference 2 4) (sourceB2642 + difference 4 2) sourceC2642) = raw37106 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw37106; decide +kernel
    rw [ha]
    exact (canonical37106 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2642 + difference 2 5) (sourceB2642 + difference 5 2) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2642 + difference 2 5) (sourceB2642 + difference 5 2) sourceC2642) = raw37107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw37107; decide +kernel
    rw [ha]
    exact (canonical37107 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2642 + difference 3 0) (sourceB2642 + difference 0 3) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4971) := by
    have ha : (tripleCharges (sourceA2642 + difference 3 0) (sourceB2642 + difference 0 3) sourceC2642) = raw34434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw34434; decide +kernel
    rw [ha]
    exact (canonical34434 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2642 + difference 3 1) (sourceB2642 + difference 1 3) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4676) := by
    have ha : (tripleCharges (sourceA2642 + difference 3 1) (sourceB2642 + difference 1 3) sourceC2642) = raw37108 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw37108; decide +kernel
    rw [ha]
    exact (canonical37108 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2642 + difference 3 2) (sourceB2642 + difference 2 3) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2642 + difference 3 2) (sourceB2642 + difference 2 3) sourceC2642) = raw35611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw35611; decide +kernel
    rw [ha]
    exact (canonical35611 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2642 + difference 3 4) (sourceB2642 + difference 4 3) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2642 + difference 3 4) (sourceB2642 + difference 4 3) sourceC2642) = raw37109 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw37109; decide +kernel
    rw [ha]
    exact (canonical37109 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2642 + difference 3 5) (sourceB2642 + difference 5 3) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2642 + difference 3 5) (sourceB2642 + difference 5 3) sourceC2642) = raw37110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw37110; decide +kernel
    rw [ha]
    exact (canonical37110 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2642 + difference 4 0) (sourceB2642 + difference 0 4) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4968) := by
    have ha : (tripleCharges (sourceA2642 + difference 4 0) (sourceB2642 + difference 0 4) sourceC2642) = raw34437 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw34437; decide +kernel
    rw [ha]
    exact (canonical34437 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2642 + difference 4 1) (sourceB2642 + difference 1 4) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2642 + difference 4 1) (sourceB2642 + difference 1 4) sourceC2642) = raw37111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw37111; decide +kernel
    rw [ha]
    exact (canonical37111 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2642 + difference 4 2) (sourceB2642 + difference 2 4) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2642 + difference 4 2) (sourceB2642 + difference 2 4) sourceC2642) = raw34858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw34858; decide +kernel
    rw [ha]
    exact (canonical34858 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2642 + difference 4 3) (sourceB2642 + difference 3 4) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2642 + difference 4 3) (sourceB2642 + difference 3 4) sourceC2642) = raw34855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw34855; decide +kernel
    rw [ha]
    exact (canonical34855 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2642 + difference 4 5) (sourceB2642 + difference 5 4) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2642 + difference 4 5) (sourceB2642 + difference 5 4) sourceC2642) = raw37112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw37112; decide +kernel
    rw [ha]
    exact (canonical37112 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2642 + difference 5 0) (sourceB2642 + difference 0 5) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4968) := by
    have ha : (tripleCharges (sourceA2642 + difference 5 0) (sourceB2642 + difference 0 5) sourceC2642) = raw32070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw32070; decide +kernel
    rw [ha]
    exact (canonical32070 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2642 + difference 5 1) (sourceB2642 + difference 1 5) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2642 + difference 5 1) (sourceB2642 + difference 1 5) sourceC2642) = raw35606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw35606; decide +kernel
    rw [ha]
    exact (canonical35606 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2642 + difference 5 2) (sourceB2642 + difference 2 5) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2642 + difference 5 2) (sourceB2642 + difference 2 5) sourceC2642) = raw32066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw32066; decide +kernel
    rw [ha]
    exact (canonical32066 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2642 + difference 5 3) (sourceB2642 + difference 3 5) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2642 + difference 5 3) (sourceB2642 + difference 3 5) sourceC2642) = raw34854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw34854; decide +kernel
    rw [ha]
    exact (canonical34854 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2642 + difference 5 4) (sourceB2642 + difference 4 5) sourceC2642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2642 + difference 5 4) (sourceB2642 + difference 4 5) sourceC2642) = raw35607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2642 sourceB2642 sourceC2642 difference raw35607; decide +kernel
    rw [ha]
    exact (canonical35607 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2642 sourceB2642 sourceC2642
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2642, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2643 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2643 : Charge := ![0, 3, -1, -1, -1, 0]
def sourceC2643 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceForm2643 : Integer.Sparse Master := [(Sum.inr 4376, 3), (Sum.inr 4379, 1), (Sum.inr 4451, 1), (Sum.inr 4980, 1), (Sum.inr 4981, 3), (Sum.inr 5123, 3), (Sum.inr 5162, 1), (Sum.inr 5202, 1), (Sum.inr 5228, 6), (Sum.inr 5237, 3), (Sum.inr 5290, 3), (Sum.inr 5447, 1), (Sum.inr 5450, 3)]

theorem sourceEq2643 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2643 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2643 + difference 0 1) (sourceB2643 + difference 1 0) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA2643 + difference 0 1) (sourceB2643 + difference 1 0) sourceC2643) = raw37113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw37113; decide +kernel
    rw [ha]
    exact (canonical37113 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2643 + difference 0 2) (sourceB2643 + difference 2 0) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA2643 + difference 0 2) (sourceB2643 + difference 2 0) sourceC2643) = raw35935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw35935; decide +kernel
    rw [ha]
    exact (canonical35935 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2643 + difference 0 3) (sourceB2643 + difference 3 0) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA2643 + difference 0 3) (sourceB2643 + difference 3 0) sourceC2643) = raw37114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw37114; decide +kernel
    rw [ha]
    exact (canonical37114 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2643 + difference 0 4) (sourceB2643 + difference 4 0) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA2643 + difference 0 4) (sourceB2643 + difference 4 0) sourceC2643) = raw37115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw37115; decide +kernel
    rw [ha]
    exact (canonical37115 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2643 + difference 0 5) (sourceB2643 + difference 5 0) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA2643 + difference 0 5) (sourceB2643 + difference 5 0) sourceC2643) = raw37116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw37116; decide +kernel
    rw [ha]
    exact (canonical37116 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2643 + difference 1 0) (sourceB2643 + difference 0 1) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA2643 + difference 1 0) (sourceB2643 + difference 0 1) sourceC2643) = raw26792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw26792; decide +kernel
    rw [ha]
    exact (canonical26792 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2643 + difference 1 2) (sourceB2643 + difference 2 1) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2643 + difference 1 2) (sourceB2643 + difference 2 1) sourceC2643) = raw16238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw16238; decide +kernel
    rw [ha]
    exact (canonical16238 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2643 + difference 1 3) (sourceB2643 + difference 3 1) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2643 + difference 1 3) (sourceB2643 + difference 3 1) sourceC2643) = raw16233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw16233; decide +kernel
    rw [ha]
    exact (canonical16233 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2643 + difference 1 4) (sourceB2643 + difference 4 1) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2643 + difference 1 4) (sourceB2643 + difference 4 1) sourceC2643) = raw34466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw34466; decide +kernel
    rw [ha]
    exact (canonical34466 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2643 + difference 1 5) (sourceB2643 + difference 5 1) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA2643 + difference 1 5) (sourceB2643 + difference 5 1) sourceC2643) = raw34467 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw34467; decide +kernel
    rw [ha]
    exact (canonical34467 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2643 + difference 2 0) (sourceB2643 + difference 0 2) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4981) := by
    have ha : (tripleCharges (sourceA2643 + difference 2 0) (sourceB2643 + difference 0 2) sourceC2643) = raw34469 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw34469; decide +kernel
    rw [ha]
    exact (canonical34469 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2643 + difference 2 1) (sourceB2643 + difference 1 2) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4376) := by
    have ha : (tripleCharges (sourceA2643 + difference 2 1) (sourceB2643 + difference 1 2) sourceC2643) = raw37117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw37117; decide +kernel
    rw [ha]
    exact (canonical37117 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2643 + difference 2 3) (sourceB2643 + difference 3 2) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2643 + difference 2 3) (sourceB2643 + difference 3 2) sourceC2643) = raw37118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw37118; decide +kernel
    rw [ha]
    exact (canonical37118 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2643 + difference 2 4) (sourceB2643 + difference 4 2) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2643 + difference 2 4) (sourceB2643 + difference 4 2) sourceC2643) = raw37119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw37119; decide +kernel
    rw [ha]
    exact (canonical37119 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2643 + difference 2 5) (sourceB2643 + difference 5 2) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2643 + difference 2 5) (sourceB2643 + difference 5 2) sourceC2643) = raw37120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw37120; decide +kernel
    rw [ha]
    exact (canonical37120 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2643 + difference 3 0) (sourceB2643 + difference 0 3) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4981) := by
    have ha : (tripleCharges (sourceA2643 + difference 3 0) (sourceB2643 + difference 0 3) sourceC2643) = raw34473 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw34473; decide +kernel
    rw [ha]
    exact (canonical34473 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2643 + difference 3 1) (sourceB2643 + difference 1 3) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4376) := by
    have ha : (tripleCharges (sourceA2643 + difference 3 1) (sourceB2643 + difference 1 3) sourceC2643) = raw37121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw37121; decide +kernel
    rw [ha]
    exact (canonical37121 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2643 + difference 3 2) (sourceB2643 + difference 2 3) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2643 + difference 3 2) (sourceB2643 + difference 2 3) sourceC2643) = raw35941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw35941; decide +kernel
    rw [ha]
    exact (canonical35941 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2643 + difference 3 4) (sourceB2643 + difference 4 3) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2643 + difference 3 4) (sourceB2643 + difference 4 3) sourceC2643) = raw37122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw37122; decide +kernel
    rw [ha]
    exact (canonical37122 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2643 + difference 3 5) (sourceB2643 + difference 5 3) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2643 + difference 3 5) (sourceB2643 + difference 5 3) sourceC2643) = raw37123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw37123; decide +kernel
    rw [ha]
    exact (canonical37123 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2643 + difference 4 0) (sourceB2643 + difference 0 4) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4981) := by
    have ha : (tripleCharges (sourceA2643 + difference 4 0) (sourceB2643 + difference 0 4) sourceC2643) = raw34476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw34476; decide +kernel
    rw [ha]
    exact (canonical34476 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2643 + difference 4 1) (sourceB2643 + difference 1 4) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4376) := by
    have ha : (tripleCharges (sourceA2643 + difference 4 1) (sourceB2643 + difference 1 4) sourceC2643) = raw37124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw37124; decide +kernel
    rw [ha]
    exact (canonical37124 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2643 + difference 4 2) (sourceB2643 + difference 2 4) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2643 + difference 4 2) (sourceB2643 + difference 2 4) sourceC2643) = raw35090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw35090; decide +kernel
    rw [ha]
    exact (canonical35090 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2643 + difference 4 3) (sourceB2643 + difference 3 4) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2643 + difference 4 3) (sourceB2643 + difference 3 4) sourceC2643) = raw35087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw35087; decide +kernel
    rw [ha]
    exact (canonical35087 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2643 + difference 4 5) (sourceB2643 + difference 5 4) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2643 + difference 4 5) (sourceB2643 + difference 5 4) sourceC2643) = raw37125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw37125; decide +kernel
    rw [ha]
    exact (canonical37125 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2643 + difference 5 0) (sourceB2643 + difference 0 5) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4980) := by
    have ha : (tripleCharges (sourceA2643 + difference 5 0) (sourceB2643 + difference 0 5) sourceC2643) = raw32551 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw32551; decide +kernel
    rw [ha]
    exact (canonical32551 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2643 + difference 5 1) (sourceB2643 + difference 1 5) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4379) := by
    have ha : (tripleCharges (sourceA2643 + difference 5 1) (sourceB2643 + difference 1 5) sourceC2643) = raw35936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw35936; decide +kernel
    rw [ha]
    exact (canonical35936 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2643 + difference 5 2) (sourceB2643 + difference 2 5) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2643 + difference 5 2) (sourceB2643 + difference 2 5) sourceC2643) = raw16235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw16235; decide +kernel
    rw [ha]
    exact (canonical16235 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2643 + difference 5 3) (sourceB2643 + difference 3 5) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2643 + difference 5 3) (sourceB2643 + difference 3 5) sourceC2643) = raw16230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw16230; decide +kernel
    rw [ha]
    exact (canonical16230 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2643 + difference 5 4) (sourceB2643 + difference 4 5) sourceC2643) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2643 + difference 5 4) (sourceB2643 + difference 4 5) sourceC2643) = raw35937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2643 sourceB2643 sourceC2643 difference raw35937; decide +kernel
    rw [ha]
    exact (canonical35937 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2643 sourceB2643 sourceC2643
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2643, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2644 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2644 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2644 : Charge := ![0, 3, -1, -1, -1, 0]
def sourceForm2644 : Integer.Sparse Master := [(Sum.inr 4679, 3), (Sum.inr 4685, 1), (Sum.inr 4695, 1), (Sum.inr 4696, 3), (Sum.inr 4833, 1), (Sum.inr 4878, 1), (Sum.inr 5226, 6), (Sum.inr 5231, 3), (Sum.inr 5237, 3), (Sum.inr 5257, 3), (Sum.inr 5265, 3), (Sum.inr 5273, 1), (Sum.inr 5301, 1)]

theorem sourceEq2644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2644 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2644 + difference 0 1) (sourceB2644 + difference 1 0) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA2644 + difference 0 1) (sourceB2644 + difference 1 0) sourceC2644) = raw37126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37126; decide +kernel
    rw [ha]
    exact (canonical37126 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2644 + difference 0 2) (sourceB2644 + difference 2 0) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA2644 + difference 0 2) (sourceB2644 + difference 2 0) sourceC2644) = raw37127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37127; decide +kernel
    rw [ha]
    exact (canonical37127 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2644 + difference 0 3) (sourceB2644 + difference 3 0) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA2644 + difference 0 3) (sourceB2644 + difference 3 0) sourceC2644) = raw37128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37128; decide +kernel
    rw [ha]
    exact (canonical37128 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2644 + difference 0 4) (sourceB2644 + difference 4 0) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA2644 + difference 0 4) (sourceB2644 + difference 4 0) sourceC2644) = raw37129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37129; decide +kernel
    rw [ha]
    exact (canonical37129 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2644 + difference 0 5) (sourceB2644 + difference 5 0) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA2644 + difference 0 5) (sourceB2644 + difference 5 0) sourceC2644) = raw37130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37130; decide +kernel
    rw [ha]
    exact (canonical37130 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2644 + difference 1 0) (sourceB2644 + difference 0 1) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4878) := by
    have ha : (tripleCharges (sourceA2644 + difference 1 0) (sourceB2644 + difference 0 1) sourceC2644) = raw37131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37131; decide +kernel
    rw [ha]
    exact (canonical37131 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2644 + difference 1 2) (sourceB2644 + difference 2 1) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA2644 + difference 1 2) (sourceB2644 + difference 2 1) sourceC2644) = raw37132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37132; decide +kernel
    rw [ha]
    exact (canonical37132 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2644 + difference 1 3) (sourceB2644 + difference 3 1) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA2644 + difference 1 3) (sourceB2644 + difference 3 1) sourceC2644) = raw37133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37133; decide +kernel
    rw [ha]
    exact (canonical37133 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2644 + difference 1 4) (sourceB2644 + difference 4 1) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA2644 + difference 1 4) (sourceB2644 + difference 4 1) sourceC2644) = raw37134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37134; decide +kernel
    rw [ha]
    exact (canonical37134 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2644 + difference 1 5) (sourceB2644 + difference 5 1) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA2644 + difference 1 5) (sourceB2644 + difference 5 1) sourceC2644) = raw37135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37135; decide +kernel
    rw [ha]
    exact (canonical37135 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2644 + difference 2 0) (sourceB2644 + difference 0 2) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4696) := by
    have ha : (tripleCharges (sourceA2644 + difference 2 0) (sourceB2644 + difference 0 2) sourceC2644) = raw37136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37136; decide +kernel
    rw [ha]
    exact (canonical37136 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2644 + difference 2 1) (sourceB2644 + difference 1 2) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2644 + difference 2 1) (sourceB2644 + difference 1 2) sourceC2644) = raw37137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37137; decide +kernel
    rw [ha]
    exact (canonical37137 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2644 + difference 2 3) (sourceB2644 + difference 3 2) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2644 + difference 2 3) (sourceB2644 + difference 3 2) sourceC2644) = raw37138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37138; decide +kernel
    rw [ha]
    exact (canonical37138 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2644 + difference 2 4) (sourceB2644 + difference 4 2) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2644 + difference 2 4) (sourceB2644 + difference 4 2) sourceC2644) = raw37139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37139; decide +kernel
    rw [ha]
    exact (canonical37139 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2644 + difference 2 5) (sourceB2644 + difference 5 2) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2644 + difference 2 5) (sourceB2644 + difference 5 2) sourceC2644) = raw37140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37140; decide +kernel
    rw [ha]
    exact (canonical37140 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2644 + difference 3 0) (sourceB2644 + difference 0 3) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4696) := by
    have ha : (tripleCharges (sourceA2644 + difference 3 0) (sourceB2644 + difference 0 3) sourceC2644) = raw37141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37141; decide +kernel
    rw [ha]
    exact (canonical37141 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2644 + difference 3 1) (sourceB2644 + difference 1 3) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2644 + difference 3 1) (sourceB2644 + difference 1 3) sourceC2644) = raw37142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37142; decide +kernel
    rw [ha]
    exact (canonical37142 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2644 + difference 3 2) (sourceB2644 + difference 2 3) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2644 + difference 3 2) (sourceB2644 + difference 2 3) sourceC2644) = raw37143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37143; decide +kernel
    rw [ha]
    exact (canonical37143 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2644 + difference 3 4) (sourceB2644 + difference 4 3) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2644 + difference 3 4) (sourceB2644 + difference 4 3) sourceC2644) = raw37144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37144; decide +kernel
    rw [ha]
    exact (canonical37144 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2644 + difference 3 5) (sourceB2644 + difference 5 3) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2644 + difference 3 5) (sourceB2644 + difference 5 3) sourceC2644) = raw37145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37145; decide +kernel
    rw [ha]
    exact (canonical37145 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2644 + difference 4 0) (sourceB2644 + difference 0 4) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4696) := by
    have ha : (tripleCharges (sourceA2644 + difference 4 0) (sourceB2644 + difference 0 4) sourceC2644) = raw37146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37146; decide +kernel
    rw [ha]
    exact (canonical37146 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2644 + difference 4 1) (sourceB2644 + difference 1 4) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2644 + difference 4 1) (sourceB2644 + difference 1 4) sourceC2644) = raw37147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37147; decide +kernel
    rw [ha]
    exact (canonical37147 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2644 + difference 4 2) (sourceB2644 + difference 2 4) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2644 + difference 4 2) (sourceB2644 + difference 2 4) sourceC2644) = raw37148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37148; decide +kernel
    rw [ha]
    exact (canonical37148 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2644 + difference 4 3) (sourceB2644 + difference 3 4) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2644 + difference 4 3) (sourceB2644 + difference 3 4) sourceC2644) = raw37149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37149; decide +kernel
    rw [ha]
    exact (canonical37149 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2644 + difference 4 5) (sourceB2644 + difference 5 4) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2644 + difference 4 5) (sourceB2644 + difference 5 4) sourceC2644) = raw37150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37150; decide +kernel
    rw [ha]
    exact (canonical37150 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2644 + difference 5 0) (sourceB2644 + difference 0 5) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4695) := by
    have ha : (tripleCharges (sourceA2644 + difference 5 0) (sourceB2644 + difference 0 5) sourceC2644) = raw37151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37151; decide +kernel
    rw [ha]
    exact (canonical37151 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2644 + difference 5 1) (sourceB2644 + difference 1 5) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4685) := by
    have ha : (tripleCharges (sourceA2644 + difference 5 1) (sourceB2644 + difference 1 5) sourceC2644) = raw37152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37152; decide +kernel
    rw [ha]
    exact (canonical37152 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2644 + difference 5 2) (sourceB2644 + difference 2 5) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA2644 + difference 5 2) (sourceB2644 + difference 2 5) sourceC2644) = raw37153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37153; decide +kernel
    rw [ha]
    exact (canonical37153 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2644 + difference 5 3) (sourceB2644 + difference 3 5) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA2644 + difference 5 3) (sourceB2644 + difference 3 5) sourceC2644) = raw37154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37154; decide +kernel
    rw [ha]
    exact (canonical37154 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2644 + difference 5 4) (sourceB2644 + difference 4 5) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA2644 + difference 5 4) (sourceB2644 + difference 4 5) sourceC2644) = raw37155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37155; decide +kernel
    rw [ha]
    exact (canonical37155 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2644 sourceB2644 sourceC2644
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2644, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2645 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2645 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2645 : Charge := ![0, 3, -1, -1, -1, 0]
def sourceForm2645 : Integer.Sparse Master := [(Sum.inr 2150, 3), (Sum.inr 2156, 1), (Sum.inr 2204, 1), (Sum.inr 2231, 1), (Sum.inr 2234, 1), (Sum.inr 2238, 3), (Sum.inr 2669, 6), (Sum.inr 2676, 3), (Sum.inr 2684, 3), (Sum.inr 2721, 3), (Sum.inr 2741, 1), (Sum.inr 3037, 3), (Sum.inr 3053, 1)]

theorem sourceEq2645 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2645 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2645 + difference 0 1) (sourceB2645 + difference 1 0) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2204) := by
    have ha : (tripleCharges (sourceA2645 + difference 0 1) (sourceB2645 + difference 1 0) sourceC2645) = raw37156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37156; decide +kernel
    rw [ha]
    exact (canonical37156 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2645 + difference 0 2) (sourceB2645 + difference 2 0) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA2645 + difference 0 2) (sourceB2645 + difference 2 0) sourceC2645) = raw37157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37157; decide +kernel
    rw [ha]
    exact (canonical37157 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2645 + difference 0 3) (sourceB2645 + difference 3 0) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA2645 + difference 0 3) (sourceB2645 + difference 3 0) sourceC2645) = raw37158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37158; decide +kernel
    rw [ha]
    exact (canonical37158 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2645 + difference 0 4) (sourceB2645 + difference 4 0) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA2645 + difference 0 4) (sourceB2645 + difference 4 0) sourceC2645) = raw37159 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37159; decide +kernel
    rw [ha]
    exact (canonical37159 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2645 + difference 0 5) (sourceB2645 + difference 5 0) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA2645 + difference 0 5) (sourceB2645 + difference 5 0) sourceC2645) = raw37160 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37160; decide +kernel
    rw [ha]
    exact (canonical37160 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2645 + difference 1 0) (sourceB2645 + difference 0 1) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA2645 + difference 1 0) (sourceB2645 + difference 0 1) sourceC2645) = raw37161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37161; decide +kernel
    rw [ha]
    exact (canonical37161 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2645 + difference 1 2) (sourceB2645 + difference 2 1) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA2645 + difference 1 2) (sourceB2645 + difference 2 1) sourceC2645) = raw37162 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37162; decide +kernel
    rw [ha]
    exact (canonical37162 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2645 + difference 1 3) (sourceB2645 + difference 3 1) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA2645 + difference 1 3) (sourceB2645 + difference 3 1) sourceC2645) = raw37163 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37163; decide +kernel
    rw [ha]
    exact (canonical37163 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2645 + difference 1 4) (sourceB2645 + difference 4 1) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA2645 + difference 1 4) (sourceB2645 + difference 4 1) sourceC2645) = raw37164 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37164; decide +kernel
    rw [ha]
    exact (canonical37164 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2645 + difference 1 5) (sourceB2645 + difference 5 1) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA2645 + difference 1 5) (sourceB2645 + difference 5 1) sourceC2645) = raw37165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37165; decide +kernel
    rw [ha]
    exact (canonical37165 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2645 + difference 2 0) (sourceB2645 + difference 0 2) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2238) := by
    have ha : (tripleCharges (sourceA2645 + difference 2 0) (sourceB2645 + difference 0 2) sourceC2645) = raw37166 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37166; decide +kernel
    rw [ha]
    exact (canonical37166 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2645 + difference 2 1) (sourceB2645 + difference 1 2) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2150) := by
    have ha : (tripleCharges (sourceA2645 + difference 2 1) (sourceB2645 + difference 1 2) sourceC2645) = raw37167 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37167; decide +kernel
    rw [ha]
    exact (canonical37167 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2645 + difference 2 3) (sourceB2645 + difference 3 2) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2645 + difference 2 3) (sourceB2645 + difference 3 2) sourceC2645) = raw37168 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37168; decide +kernel
    rw [ha]
    exact (canonical37168 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2645 + difference 2 4) (sourceB2645 + difference 4 2) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2645 + difference 2 4) (sourceB2645 + difference 4 2) sourceC2645) = raw37169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37169; decide +kernel
    rw [ha]
    exact (canonical37169 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2645 + difference 2 5) (sourceB2645 + difference 5 2) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA2645 + difference 2 5) (sourceB2645 + difference 5 2) sourceC2645) = raw37170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37170; decide +kernel
    rw [ha]
    exact (canonical37170 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2645 + difference 3 0) (sourceB2645 + difference 0 3) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2238) := by
    have ha : (tripleCharges (sourceA2645 + difference 3 0) (sourceB2645 + difference 0 3) sourceC2645) = raw37171 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37171; decide +kernel
    rw [ha]
    exact (canonical37171 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2645 + difference 3 1) (sourceB2645 + difference 1 3) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2150) := by
    have ha : (tripleCharges (sourceA2645 + difference 3 1) (sourceB2645 + difference 1 3) sourceC2645) = raw37172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37172; decide +kernel
    rw [ha]
    exact (canonical37172 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2645 + difference 3 2) (sourceB2645 + difference 2 3) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2645 + difference 3 2) (sourceB2645 + difference 2 3) sourceC2645) = raw37173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37173; decide +kernel
    rw [ha]
    exact (canonical37173 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2645 + difference 3 4) (sourceB2645 + difference 4 3) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2645 + difference 3 4) (sourceB2645 + difference 4 3) sourceC2645) = raw37174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37174; decide +kernel
    rw [ha]
    exact (canonical37174 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2645 + difference 3 5) (sourceB2645 + difference 5 3) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA2645 + difference 3 5) (sourceB2645 + difference 5 3) sourceC2645) = raw37175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37175; decide +kernel
    rw [ha]
    exact (canonical37175 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2645 + difference 4 0) (sourceB2645 + difference 0 4) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2238) := by
    have ha : (tripleCharges (sourceA2645 + difference 4 0) (sourceB2645 + difference 0 4) sourceC2645) = raw37176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37176; decide +kernel
    rw [ha]
    exact (canonical37176 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2645 + difference 4 1) (sourceB2645 + difference 1 4) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2150) := by
    have ha : (tripleCharges (sourceA2645 + difference 4 1) (sourceB2645 + difference 1 4) sourceC2645) = raw37177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37177; decide +kernel
    rw [ha]
    exact (canonical37177 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2645 + difference 4 2) (sourceB2645 + difference 2 4) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2645 + difference 4 2) (sourceB2645 + difference 2 4) sourceC2645) = raw37178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37178; decide +kernel
    rw [ha]
    exact (canonical37178 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2645 + difference 4 3) (sourceB2645 + difference 3 4) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2645 + difference 4 3) (sourceB2645 + difference 3 4) sourceC2645) = raw37179 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37179; decide +kernel
    rw [ha]
    exact (canonical37179 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2645 + difference 4 5) (sourceB2645 + difference 5 4) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA2645 + difference 4 5) (sourceB2645 + difference 5 4) sourceC2645) = raw37180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37180; decide +kernel
    rw [ha]
    exact (canonical37180 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2645 + difference 5 0) (sourceB2645 + difference 0 5) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2231) := by
    have ha : (tripleCharges (sourceA2645 + difference 5 0) (sourceB2645 + difference 0 5) sourceC2645) = raw37181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37181; decide +kernel
    rw [ha]
    exact (canonical37181 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2645 + difference 5 1) (sourceB2645 + difference 1 5) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2156) := by
    have ha : (tripleCharges (sourceA2645 + difference 5 1) (sourceB2645 + difference 1 5) sourceC2645) = raw37182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37182; decide +kernel
    rw [ha]
    exact (canonical37182 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2645 + difference 5 2) (sourceB2645 + difference 2 5) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA2645 + difference 5 2) (sourceB2645 + difference 2 5) sourceC2645) = raw37183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37183; decide +kernel
    rw [ha]
    exact (canonical37183 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2645 + difference 5 3) (sourceB2645 + difference 3 5) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA2645 + difference 5 3) (sourceB2645 + difference 3 5) sourceC2645) = raw37184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37184; decide +kernel
    rw [ha]
    exact (canonical37184 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2645 + difference 5 4) (sourceB2645 + difference 4 5) sourceC2645) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA2645 + difference 5 4) (sourceB2645 + difference 4 5) sourceC2645) = raw37185 := by
      apply Matrix.ext; unfold tripleCharges sourceA2645 sourceB2645 sourceC2645 difference raw37185; decide +kernel
    rw [ha]
    exact (canonical37185 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2645 sourceB2645 sourceC2645
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2645, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2646 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2646 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC2646 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm2646 : Integer.Sparse Master := [(Sum.inr 4936, 6), (Sum.inr 4947, 2), (Sum.inr 5162, 2), (Sum.inr 5391, 3), (Sum.inr 5404, 6), (Sum.inr 5418, 3), (Sum.inr 5447, 2), (Sum.inr 5485, 6)]

theorem sourceEq2646 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2646 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2646 + difference 0 1) (sourceB2646 + difference 1 0) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA2646 + difference 0 1) (sourceB2646 + difference 1 0) sourceC2646) = raw37186 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw37186; decide +kernel
    rw [ha]
    exact (canonical37186 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2646 + difference 0 2) (sourceB2646 + difference 2 0) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2646 + difference 0 2) (sourceB2646 + difference 2 0) sourceC2646) = raw18650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw18650; decide +kernel
    rw [ha]
    exact (canonical18650 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2646 + difference 0 3) (sourceB2646 + difference 3 0) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2646 + difference 0 3) (sourceB2646 + difference 3 0) sourceC2646) = raw37187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw37187; decide +kernel
    rw [ha]
    exact (canonical37187 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2646 + difference 0 4) (sourceB2646 + difference 4 0) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2646 + difference 0 4) (sourceB2646 + difference 4 0) sourceC2646) = raw37188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw37188; decide +kernel
    rw [ha]
    exact (canonical37188 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2646 + difference 0 5) (sourceB2646 + difference 5 0) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA2646 + difference 0 5) (sourceB2646 + difference 5 0) sourceC2646) = raw37189 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw37189; decide +kernel
    rw [ha]
    exact (canonical37189 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2646 + difference 1 0) (sourceB2646 + difference 0 1) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA2646 + difference 1 0) (sourceB2646 + difference 0 1) sourceC2646) = raw13579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw13579; decide +kernel
    rw [ha]
    exact (canonical13579 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2646 + difference 1 2) (sourceB2646 + difference 2 1) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2646 + difference 1 2) (sourceB2646 + difference 2 1) sourceC2646) = raw3045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw3045; decide +kernel
    rw [ha]
    exact (canonical3045 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2646 + difference 1 3) (sourceB2646 + difference 3 1) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2646 + difference 1 3) (sourceB2646 + difference 3 1) sourceC2646) = raw3040 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw3040; decide +kernel
    rw [ha]
    exact (canonical3040 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2646 + difference 1 4) (sourceB2646 + difference 4 1) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2646 + difference 1 4) (sourceB2646 + difference 4 1) sourceC2646) = raw18655 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw18655; decide +kernel
    rw [ha]
    exact (canonical18655 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2646 + difference 1 5) (sourceB2646 + difference 5 1) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA2646 + difference 1 5) (sourceB2646 + difference 5 1) sourceC2646) = raw18656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw18656; decide +kernel
    rw [ha]
    exact (canonical18656 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2646 + difference 2 0) (sourceB2646 + difference 0 2) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2646 + difference 2 0) (sourceB2646 + difference 0 2) sourceC2646) = raw34519 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw34519; decide +kernel
    rw [ha]
    exact (canonical34519 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2646 + difference 2 1) (sourceB2646 + difference 1 2) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2646 + difference 2 1) (sourceB2646 + difference 1 2) sourceC2646) = raw37190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw37190; decide +kernel
    rw [ha]
    exact (canonical37190 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2646 + difference 2 3) (sourceB2646 + difference 3 2) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2646 + difference 2 3) (sourceB2646 + difference 3 2) sourceC2646) = raw37191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw37191; decide +kernel
    rw [ha]
    exact (canonical37191 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2646 + difference 2 4) (sourceB2646 + difference 4 2) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2646 + difference 2 4) (sourceB2646 + difference 4 2) sourceC2646) = raw37192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw37192; decide +kernel
    rw [ha]
    exact (canonical37192 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2646 + difference 2 5) (sourceB2646 + difference 5 2) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5391) := by
    have ha : (tripleCharges (sourceA2646 + difference 2 5) (sourceB2646 + difference 5 2) sourceC2646) = raw37193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw37193; decide +kernel
    rw [ha]
    exact (canonical37193 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2646 + difference 3 0) (sourceB2646 + difference 0 3) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2646 + difference 3 0) (sourceB2646 + difference 0 3) sourceC2646) = raw34524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw34524; decide +kernel
    rw [ha]
    exact (canonical34524 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2646 + difference 3 1) (sourceB2646 + difference 1 3) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2646 + difference 3 1) (sourceB2646 + difference 1 3) sourceC2646) = raw37194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw37194; decide +kernel
    rw [ha]
    exact (canonical37194 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2646 + difference 3 2) (sourceB2646 + difference 2 3) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2646 + difference 3 2) (sourceB2646 + difference 2 3) sourceC2646) = raw18657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw18657; decide +kernel
    rw [ha]
    exact (canonical18657 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2646 + difference 3 4) (sourceB2646 + difference 4 3) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2646 + difference 3 4) (sourceB2646 + difference 4 3) sourceC2646) = raw37195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw37195; decide +kernel
    rw [ha]
    exact (canonical37195 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2646 + difference 3 5) (sourceB2646 + difference 5 3) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5391) := by
    have ha : (tripleCharges (sourceA2646 + difference 3 5) (sourceB2646 + difference 5 3) sourceC2646) = raw37196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw37196; decide +kernel
    rw [ha]
    exact (canonical37196 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2646 + difference 4 0) (sourceB2646 + difference 0 4) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2646 + difference 4 0) (sourceB2646 + difference 0 4) sourceC2646) = raw34528 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw34528; decide +kernel
    rw [ha]
    exact (canonical34528 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2646 + difference 4 1) (sourceB2646 + difference 1 4) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2646 + difference 4 1) (sourceB2646 + difference 1 4) sourceC2646) = raw37197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw37197; decide +kernel
    rw [ha]
    exact (canonical37197 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2646 + difference 4 2) (sourceB2646 + difference 2 4) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2646 + difference 4 2) (sourceB2646 + difference 2 4) sourceC2646) = raw18661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw18661; decide +kernel
    rw [ha]
    exact (canonical18661 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2646 + difference 4 3) (sourceB2646 + difference 3 4) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2646 + difference 4 3) (sourceB2646 + difference 3 4) sourceC2646) = raw37198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw37198; decide +kernel
    rw [ha]
    exact (canonical37198 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2646 + difference 4 5) (sourceB2646 + difference 5 4) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5391) := by
    have ha : (tripleCharges (sourceA2646 + difference 4 5) (sourceB2646 + difference 5 4) sourceC2646) = raw37199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw37199; decide +kernel
    rw [ha]
    exact (canonical37199 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2646 + difference 5 0) (sourceB2646 + difference 0 5) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4947) := by
    have ha : (tripleCharges (sourceA2646 + difference 5 0) (sourceB2646 + difference 0 5) sourceC2646) = raw32201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw32201; decide +kernel
    rw [ha]
    exact (canonical32201 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2646 + difference 5 1) (sourceB2646 + difference 1 5) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4947) := by
    have ha : (tripleCharges (sourceA2646 + difference 5 1) (sourceB2646 + difference 1 5) sourceC2646) = raw36101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw36101; decide +kernel
    rw [ha]
    exact (canonical36101 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2646 + difference 5 2) (sourceB2646 + difference 2 5) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2646 + difference 5 2) (sourceB2646 + difference 2 5) sourceC2646) = raw17691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw17691; decide +kernel
    rw [ha]
    exact (canonical17691 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2646 + difference 5 3) (sourceB2646 + difference 3 5) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2646 + difference 5 3) (sourceB2646 + difference 3 5) sourceC2646) = raw17688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw17688; decide +kernel
    rw [ha]
    exact (canonical17688 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2646 + difference 5 4) (sourceB2646 + difference 4 5) sourceC2646) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2646 + difference 5 4) (sourceB2646 + difference 4 5) sourceC2646) = raw36102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2646 sourceB2646 sourceC2646 difference raw36102; decide +kernel
    rw [ha]
    exact (canonical36102 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2646 sourceB2646 sourceC2646
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2646, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2647 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2647 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC2647 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm2647 : Integer.Sparse Master := [(Sum.inr 4939, 4), (Sum.inr 4941, 4), (Sum.inr 5167, 2), (Sum.inr 5393, 4), (Sum.inr 5418, 2), (Sum.inr 5460, 2), (Sum.inr 5465, 4), (Sum.inr 5482, 4), (Sum.inr 5486, 4)]

theorem sourceEq2647 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2647 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2647 + difference 0 1) (sourceB2647 + difference 1 0) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2647 + difference 0 1) (sourceB2647 + difference 1 0) sourceC2647) = raw37200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37200; decide +kernel
    rw [ha]
    exact (canonical37200 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2647 + difference 0 2) (sourceB2647 + difference 2 0) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2647 + difference 0 2) (sourceB2647 + difference 2 0) sourceC2647) = raw36130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw36130; decide +kernel
    rw [ha]
    exact (canonical36130 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2647 + difference 0 3) (sourceB2647 + difference 3 0) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2647 + difference 0 3) (sourceB2647 + difference 3 0) sourceC2647) = raw37201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37201; decide +kernel
    rw [ha]
    exact (canonical37201 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2647 + difference 0 4) (sourceB2647 + difference 4 0) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2647 + difference 0 4) (sourceB2647 + difference 4 0) sourceC2647) = raw37202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37202; decide +kernel
    rw [ha]
    exact (canonical37202 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2647 + difference 0 5) (sourceB2647 + difference 5 0) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2647 + difference 0 5) (sourceB2647 + difference 5 0) sourceC2647) = raw37203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37203; decide +kernel
    rw [ha]
    exact (canonical37203 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2647 + difference 1 0) (sourceB2647 + difference 0 1) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2647 + difference 1 0) (sourceB2647 + difference 0 1) sourceC2647) = raw26972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw26972; decide +kernel
    rw [ha]
    exact (canonical26972 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2647 + difference 1 2) (sourceB2647 + difference 2 1) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2647 + difference 1 2) (sourceB2647 + difference 2 1) sourceC2647) = raw17674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw17674; decide +kernel
    rw [ha]
    exact (canonical17674 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2647 + difference 1 3) (sourceB2647 + difference 3 1) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2647 + difference 1 3) (sourceB2647 + difference 3 1) sourceC2647) = raw17670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw17670; decide +kernel
    rw [ha]
    exact (canonical17670 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2647 + difference 1 4) (sourceB2647 + difference 4 1) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2647 + difference 1 4) (sourceB2647 + difference 4 1) sourceC2647) = raw37204 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37204; decide +kernel
    rw [ha]
    exact (canonical37204 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2647 + difference 1 5) (sourceB2647 + difference 5 1) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2647 + difference 1 5) (sourceB2647 + difference 5 1) sourceC2647) = raw37205 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37205; decide +kernel
    rw [ha]
    exact (canonical37205 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2647 + difference 2 0) (sourceB2647 + difference 0 2) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2647 + difference 2 0) (sourceB2647 + difference 0 2) sourceC2647) = raw37206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37206; decide +kernel
    rw [ha]
    exact (canonical37206 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2647 + difference 2 1) (sourceB2647 + difference 1 2) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2647 + difference 2 1) (sourceB2647 + difference 1 2) sourceC2647) = raw37207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37207; decide +kernel
    rw [ha]
    exact (canonical37207 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2647 + difference 2 3) (sourceB2647 + difference 3 2) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2647 + difference 2 3) (sourceB2647 + difference 3 2) sourceC2647) = raw37208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37208; decide +kernel
    rw [ha]
    exact (canonical37208 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2647 + difference 2 4) (sourceB2647 + difference 4 2) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2647 + difference 2 4) (sourceB2647 + difference 4 2) sourceC2647) = raw37209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37209; decide +kernel
    rw [ha]
    exact (canonical37209 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2647 + difference 2 5) (sourceB2647 + difference 5 2) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2647 + difference 2 5) (sourceB2647 + difference 5 2) sourceC2647) = raw37210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37210; decide +kernel
    rw [ha]
    exact (canonical37210 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2647 + difference 3 0) (sourceB2647 + difference 0 3) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2647 + difference 3 0) (sourceB2647 + difference 0 3) sourceC2647) = raw37211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37211; decide +kernel
    rw [ha]
    exact (canonical37211 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2647 + difference 3 1) (sourceB2647 + difference 1 3) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2647 + difference 3 1) (sourceB2647 + difference 1 3) sourceC2647) = raw37212 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37212; decide +kernel
    rw [ha]
    exact (canonical37212 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2647 + difference 3 2) (sourceB2647 + difference 2 3) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2647 + difference 3 2) (sourceB2647 + difference 2 3) sourceC2647) = raw36139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw36139; decide +kernel
    rw [ha]
    exact (canonical36139 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2647 + difference 3 4) (sourceB2647 + difference 4 3) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2647 + difference 3 4) (sourceB2647 + difference 4 3) sourceC2647) = raw37213 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37213; decide +kernel
    rw [ha]
    exact (canonical37213 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2647 + difference 3 5) (sourceB2647 + difference 5 3) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2647 + difference 3 5) (sourceB2647 + difference 5 3) sourceC2647) = raw37214 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37214; decide +kernel
    rw [ha]
    exact (canonical37214 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2647 + difference 4 0) (sourceB2647 + difference 0 4) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2647 + difference 4 0) (sourceB2647 + difference 0 4) sourceC2647) = raw37215 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37215; decide +kernel
    rw [ha]
    exact (canonical37215 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2647 + difference 4 1) (sourceB2647 + difference 1 4) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2647 + difference 4 1) (sourceB2647 + difference 1 4) sourceC2647) = raw37216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37216; decide +kernel
    rw [ha]
    exact (canonical37216 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2647 + difference 4 2) (sourceB2647 + difference 2 4) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2647 + difference 4 2) (sourceB2647 + difference 2 4) sourceC2647) = raw35231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw35231; decide +kernel
    rw [ha]
    exact (canonical35231 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2647 + difference 4 3) (sourceB2647 + difference 3 4) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2647 + difference 4 3) (sourceB2647 + difference 3 4) sourceC2647) = raw35228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw35228; decide +kernel
    rw [ha]
    exact (canonical35228 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2647 + difference 4 5) (sourceB2647 + difference 5 4) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA2647 + difference 4 5) (sourceB2647 + difference 5 4) sourceC2647) = raw37217 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37217; decide +kernel
    rw [ha]
    exact (canonical37217 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2647 + difference 5 0) (sourceB2647 + difference 0 5) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2647 + difference 5 0) (sourceB2647 + difference 0 5) sourceC2647) = raw36131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw36131; decide +kernel
    rw [ha]
    exact (canonical36131 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2647 + difference 5 1) (sourceB2647 + difference 1 5) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2647 + difference 5 1) (sourceB2647 + difference 1 5) sourceC2647) = raw36132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw36132; decide +kernel
    rw [ha]
    exact (canonical36132 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2647 + difference 5 2) (sourceB2647 + difference 2 5) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2647 + difference 5 2) (sourceB2647 + difference 2 5) sourceC2647) = raw17672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw17672; decide +kernel
    rw [ha]
    exact (canonical17672 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2647 + difference 5 3) (sourceB2647 + difference 3 5) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2647 + difference 5 3) (sourceB2647 + difference 3 5) sourceC2647) = raw17668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw17668; decide +kernel
    rw [ha]
    exact (canonical17668 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2647 + difference 5 4) (sourceB2647 + difference 4 5) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA2647 + difference 5 4) (sourceB2647 + difference 4 5) sourceC2647) = raw36133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw36133; decide +kernel
    rw [ha]
    exact (canonical36133 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2647 sourceB2647 sourceC2647
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2647, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2648 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2648 : Charge := ![1, 2, -2, -1, 0, 0]
def sourceC2648 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceForm2648 : Integer.Sparse Master := [(Sum.inr 4639, 1), (Sum.inr 4640, 1), (Sum.inr 4642, 2), (Sum.inr 4831, 1), (Sum.inr 4909, 1), (Sum.inr 4910, 1), (Sum.inr 4912, 2), (Sum.inr 5056, 2), (Sum.inr 5098, 1), (Sum.inr 5248, 1), (Sum.inr 5344, 2), (Sum.inr 5346, 2), (Sum.inr 5351, 1), (Sum.inr 5352, 2), (Sum.inr 5368, 2), (Sum.inr 5424, 2), (Sum.inr 5433, 1), (Sum.inr 5439, 1), (Sum.inr 5478, 2), (Sum.inr 5482, 1), (Sum.inr 5485, 1)]

theorem sourceEq2648 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2648 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2648 + difference 0 1) (sourceB2648 + difference 1 0) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA2648 + difference 0 1) (sourceB2648 + difference 1 0) sourceC2648) = raw37218 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw37218; decide +kernel
    rw [ha]
    exact (canonical37218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2648 + difference 0 2) (sourceB2648 + difference 2 0) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2648 + difference 0 2) (sourceB2648 + difference 2 0) sourceC2648) = raw36489 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw36489; decide +kernel
    rw [ha]
    exact (canonical36489 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2648 + difference 0 3) (sourceB2648 + difference 3 0) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2648 + difference 0 3) (sourceB2648 + difference 3 0) sourceC2648) = raw37219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw37219; decide +kernel
    rw [ha]
    exact (canonical37219 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2648 + difference 0 4) (sourceB2648 + difference 4 0) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2648 + difference 0 4) (sourceB2648 + difference 4 0) sourceC2648) = raw37220 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw37220; decide +kernel
    rw [ha]
    exact (canonical37220 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2648 + difference 0 5) (sourceB2648 + difference 5 0) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2648 + difference 0 5) (sourceB2648 + difference 5 0) sourceC2648) = raw37221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw37221; decide +kernel
    rw [ha]
    exact (canonical37221 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2648 + difference 1 0) (sourceB2648 + difference 0 1) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA2648 + difference 1 0) (sourceB2648 + difference 0 1) sourceC2648) = raw27121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw27121; decide +kernel
    rw [ha]
    exact (canonical27121 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2648 + difference 1 2) (sourceB2648 + difference 2 1) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2648 + difference 1 2) (sourceB2648 + difference 2 1) sourceC2648) = raw33095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw33095; decide +kernel
    rw [ha]
    exact (canonical33095 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2648 + difference 1 3) (sourceB2648 + difference 3 1) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2648 + difference 1 3) (sourceB2648 + difference 3 1) sourceC2648) = raw34562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw34562; decide +kernel
    rw [ha]
    exact (canonical34562 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2648 + difference 1 4) (sourceB2648 + difference 4 1) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA2648 + difference 1 4) (sourceB2648 + difference 4 1) sourceC2648) = raw34563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw34563; decide +kernel
    rw [ha]
    exact (canonical34563 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2648 + difference 1 5) (sourceB2648 + difference 5 1) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA2648 + difference 1 5) (sourceB2648 + difference 5 1) sourceC2648) = raw34564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw34564; decide +kernel
    rw [ha]
    exact (canonical34564 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2648 + difference 2 0) (sourceB2648 + difference 0 2) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4909) := by
    have ha : (tripleCharges (sourceA2648 + difference 2 0) (sourceB2648 + difference 0 2) sourceC2648) = raw34566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw34566; decide +kernel
    rw [ha]
    exact (canonical34566 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2648 + difference 2 1) (sourceB2648 + difference 1 2) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4639) := by
    have ha : (tripleCharges (sourceA2648 + difference 2 1) (sourceB2648 + difference 1 2) sourceC2648) = raw37222 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw37222; decide +kernel
    rw [ha]
    exact (canonical37222 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2648 + difference 2 3) (sourceB2648 + difference 3 2) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2648 + difference 2 3) (sourceB2648 + difference 3 2) sourceC2648) = raw37223 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw37223; decide +kernel
    rw [ha]
    exact (canonical37223 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2648 + difference 2 4) (sourceB2648 + difference 4 2) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2648 + difference 2 4) (sourceB2648 + difference 4 2) sourceC2648) = raw37224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw37224; decide +kernel
    rw [ha]
    exact (canonical37224 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2648 + difference 2 5) (sourceB2648 + difference 5 2) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2648 + difference 2 5) (sourceB2648 + difference 5 2) sourceC2648) = raw37225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw37225; decide +kernel
    rw [ha]
    exact (canonical37225 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2648 + difference 3 0) (sourceB2648 + difference 0 3) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4910) := by
    have ha : (tripleCharges (sourceA2648 + difference 3 0) (sourceB2648 + difference 0 3) sourceC2648) = raw34570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw34570; decide +kernel
    rw [ha]
    exact (canonical34570 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2648 + difference 3 1) (sourceB2648 + difference 1 3) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4640) := by
    have ha : (tripleCharges (sourceA2648 + difference 3 1) (sourceB2648 + difference 1 3) sourceC2648) = raw37226 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw37226; decide +kernel
    rw [ha]
    exact (canonical37226 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2648 + difference 3 2) (sourceB2648 + difference 2 3) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2648 + difference 3 2) (sourceB2648 + difference 2 3) sourceC2648) = raw36496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw36496; decide +kernel
    rw [ha]
    exact (canonical36496 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2648 + difference 3 4) (sourceB2648 + difference 4 3) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA2648 + difference 3 4) (sourceB2648 + difference 4 3) sourceC2648) = raw37227 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw37227; decide +kernel
    rw [ha]
    exact (canonical37227 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2648 + difference 3 5) (sourceB2648 + difference 5 3) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA2648 + difference 3 5) (sourceB2648 + difference 5 3) sourceC2648) = raw37228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw37228; decide +kernel
    rw [ha]
    exact (canonical37228 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2648 + difference 4 0) (sourceB2648 + difference 0 4) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4912) := by
    have ha : (tripleCharges (sourceA2648 + difference 4 0) (sourceB2648 + difference 0 4) sourceC2648) = raw34573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw34573; decide +kernel
    rw [ha]
    exact (canonical34573 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2648 + difference 4 1) (sourceB2648 + difference 1 4) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4642) := by
    have ha : (tripleCharges (sourceA2648 + difference 4 1) (sourceB2648 + difference 1 4) sourceC2648) = raw37229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw37229; decide +kernel
    rw [ha]
    exact (canonical37229 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2648 + difference 4 2) (sourceB2648 + difference 2 4) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2648 + difference 4 2) (sourceB2648 + difference 2 4) sourceC2648) = raw36499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw36499; decide +kernel
    rw [ha]
    exact (canonical36499 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2648 + difference 4 3) (sourceB2648 + difference 3 4) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2648 + difference 4 3) (sourceB2648 + difference 3 4) sourceC2648) = raw37230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw37230; decide +kernel
    rw [ha]
    exact (canonical37230 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2648 + difference 4 5) (sourceB2648 + difference 5 4) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2648 + difference 4 5) (sourceB2648 + difference 5 4) sourceC2648) = raw37231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw37231; decide +kernel
    rw [ha]
    exact (canonical37231 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2648 + difference 5 0) (sourceB2648 + difference 0 5) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4912) := by
    have ha : (tripleCharges (sourceA2648 + difference 5 0) (sourceB2648 + difference 0 5) sourceC2648) = raw33098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw33098; decide +kernel
    rw [ha]
    exact (canonical33098 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2648 + difference 5 1) (sourceB2648 + difference 1 5) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4642) := by
    have ha : (tripleCharges (sourceA2648 + difference 5 1) (sourceB2648 + difference 1 5) sourceC2648) = raw36490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw36490; decide +kernel
    rw [ha]
    exact (canonical36490 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2648 + difference 5 2) (sourceB2648 + difference 2 5) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2648 + difference 5 2) (sourceB2648 + difference 2 5) sourceC2648) = raw33092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw33092; decide +kernel
    rw [ha]
    exact (canonical33092 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2648 + difference 5 3) (sourceB2648 + difference 3 5) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2648 + difference 5 3) (sourceB2648 + difference 3 5) sourceC2648) = raw36491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw36491; decide +kernel
    rw [ha]
    exact (canonical36491 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2648 + difference 5 4) (sourceB2648 + difference 4 5) sourceC2648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2648 + difference 5 4) (sourceB2648 + difference 4 5) sourceC2648) = raw36492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2648 sourceB2648 sourceC2648 difference raw36492; decide +kernel
    rw [ha]
    exact (canonical36492 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2648 sourceB2648 sourceC2648
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2648, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2649 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2649 : Charge := ![2, 2, -1, -1, -1, -1]
def sourceC2649 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm2649 : Integer.Sparse Master := [(Sum.inr 4073, 8), (Sum.inr 4079, 2), (Sum.inr 4088, 12), (Sum.inr 4091, 8)]

theorem sourceEq2649 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2649 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2649 + difference 0 1) (sourceB2649 + difference 1 0) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (tripleCharges (sourceA2649 + difference 0 1) (sourceB2649 + difference 1 0) sourceC2649) = raw37232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37232; decide +kernel
    rw [ha]
    exact (canonical37232 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2649 + difference 0 2) (sourceB2649 + difference 2 0) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 0 2) (sourceB2649 + difference 2 0) sourceC2649) = raw3440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw3440; decide +kernel
    rw [ha]
    exact (canonical3440 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2649 + difference 0 3) (sourceB2649 + difference 3 0) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 0 3) (sourceB2649 + difference 3 0) sourceC2649) = raw3436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw3436; decide +kernel
    rw [ha]
    exact (canonical3436 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2649 + difference 0 4) (sourceB2649 + difference 4 0) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 0 4) (sourceB2649 + difference 4 0) sourceC2649) = raw37233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37233; decide +kernel
    rw [ha]
    exact (canonical37233 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2649 + difference 0 5) (sourceB2649 + difference 5 0) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 0 5) (sourceB2649 + difference 5 0) sourceC2649) = raw37234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37234; decide +kernel
    rw [ha]
    exact (canonical37234 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2649 + difference 1 0) (sourceB2649 + difference 0 1) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (tripleCharges (sourceA2649 + difference 1 0) (sourceB2649 + difference 0 1) sourceC2649) = raw14365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw14365; decide +kernel
    rw [ha]
    exact (canonical14365 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2649 + difference 1 2) (sourceB2649 + difference 2 1) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 1 2) (sourceB2649 + difference 2 1) sourceC2649) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2649 + difference 1 3) (sourceB2649 + difference 3 1) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 1 3) (sourceB2649 + difference 3 1) sourceC2649) = raw3328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw3328; decide +kernel
    rw [ha]
    exact (canonical3328 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2649 + difference 1 4) (sourceB2649 + difference 4 1) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 1 4) (sourceB2649 + difference 4 1) sourceC2649) = raw19361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw19361; decide +kernel
    rw [ha]
    exact (canonical19361 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2649 + difference 1 5) (sourceB2649 + difference 5 1) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2649 + difference 1 5) (sourceB2649 + difference 5 1) sourceC2649) = raw19362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw19362; decide +kernel
    rw [ha]
    exact (canonical19362 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2649 + difference 2 0) (sourceB2649 + difference 0 2) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 2 0) (sourceB2649 + difference 0 2) sourceC2649) = raw34724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw34724; decide +kernel
    rw [ha]
    exact (canonical34724 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2649 + difference 2 1) (sourceB2649 + difference 1 2) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 2 1) (sourceB2649 + difference 1 2) sourceC2649) = raw37235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37235; decide +kernel
    rw [ha]
    exact (canonical37235 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2649 + difference 2 3) (sourceB2649 + difference 3 2) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 2 3) (sourceB2649 + difference 3 2) sourceC2649) = raw37236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37236; decide +kernel
    rw [ha]
    exact (canonical37236 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2649 + difference 2 4) (sourceB2649 + difference 4 2) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 2 4) (sourceB2649 + difference 4 2) sourceC2649) = raw37237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37237; decide +kernel
    rw [ha]
    exact (canonical37237 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2649 + difference 2 5) (sourceB2649 + difference 5 2) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 2 5) (sourceB2649 + difference 5 2) sourceC2649) = raw37238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37238; decide +kernel
    rw [ha]
    exact (canonical37238 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2649 + difference 3 0) (sourceB2649 + difference 0 3) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 3 0) (sourceB2649 + difference 0 3) sourceC2649) = raw34728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw34728; decide +kernel
    rw [ha]
    exact (canonical34728 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2649 + difference 3 1) (sourceB2649 + difference 1 3) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 3 1) (sourceB2649 + difference 1 3) sourceC2649) = raw37239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37239; decide +kernel
    rw [ha]
    exact (canonical37239 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2649 + difference 3 2) (sourceB2649 + difference 2 3) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 3 2) (sourceB2649 + difference 2 3) sourceC2649) = raw19363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw19363; decide +kernel
    rw [ha]
    exact (canonical19363 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2649 + difference 3 4) (sourceB2649 + difference 4 3) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 3 4) (sourceB2649 + difference 4 3) sourceC2649) = raw37240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37240; decide +kernel
    rw [ha]
    exact (canonical37240 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2649 + difference 3 5) (sourceB2649 + difference 5 3) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 3 5) (sourceB2649 + difference 5 3) sourceC2649) = raw37241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37241; decide +kernel
    rw [ha]
    exact (canonical37241 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2649 + difference 4 0) (sourceB2649 + difference 0 4) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 4 0) (sourceB2649 + difference 0 4) sourceC2649) = raw34731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw34731; decide +kernel
    rw [ha]
    exact (canonical34731 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2649 + difference 4 1) (sourceB2649 + difference 1 4) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 4 1) (sourceB2649 + difference 1 4) sourceC2649) = raw37242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37242; decide +kernel
    rw [ha]
    exact (canonical37242 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2649 + difference 4 2) (sourceB2649 + difference 2 4) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 4 2) (sourceB2649 + difference 2 4) sourceC2649) = raw19367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw19367; decide +kernel
    rw [ha]
    exact (canonical19367 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2649 + difference 4 3) (sourceB2649 + difference 3 4) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 4 3) (sourceB2649 + difference 3 4) sourceC2649) = raw35539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw35539; decide +kernel
    rw [ha]
    exact (canonical35539 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2649 + difference 4 5) (sourceB2649 + difference 5 4) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 4 5) (sourceB2649 + difference 5 4) sourceC2649) = raw37243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37243; decide +kernel
    rw [ha]
    exact (canonical37243 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2649 + difference 5 0) (sourceB2649 + difference 0 5) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 5 0) (sourceB2649 + difference 0 5) sourceC2649) = raw34405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw34405; decide +kernel
    rw [ha]
    exact (canonical34405 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2649 + difference 5 1) (sourceB2649 + difference 1 5) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4073) := by
    have ha : (tripleCharges (sourceA2649 + difference 5 1) (sourceB2649 + difference 1 5) sourceC2649) = raw37019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37019; decide +kernel
    rw [ha]
    exact (canonical37019 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2649 + difference 5 2) (sourceB2649 + difference 2 5) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 5 2) (sourceB2649 + difference 2 5) sourceC2649) = raw18337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw18337; decide +kernel
    rw [ha]
    exact (canonical18337 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2649 + difference 5 3) (sourceB2649 + difference 3 5) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 5 3) (sourceB2649 + difference 3 5) sourceC2649) = raw18335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw18335; decide +kernel
    rw [ha]
    exact (canonical18335 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2649 + difference 5 4) (sourceB2649 + difference 4 5) sourceC2649) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2649 + difference 5 4) (sourceB2649 + difference 4 5) sourceC2649) = raw37020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2649 sourceB2649 sourceC2649 difference raw37020; decide +kernel
    rw [ha]
    exact (canonical37020 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2649 sourceB2649 sourceC2649
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2649, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2650 : Charge := ![-2, -1, -1, 1, 1, 2]
def sourceB2650 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC2650 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm2650 : Integer.Sparse Master := [(Sum.inr 5113, 1), (Sum.inr 5114, 4), (Sum.inr 5168, 4), (Sum.inr 5372, 4), (Sum.inr 5387, 4), (Sum.inr 5403, 4), (Sum.inr 5439, 4), (Sum.inr 5441, 4), (Sum.inr 5488, 1)]

theorem sourceEq2650 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2650 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2650 + difference 0 1) (sourceB2650 + difference 1 0) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA2650 + difference 0 1) (sourceB2650 + difference 1 0) sourceC2650) = raw19387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw19387; decide +kernel
    rw [ha]
    exact (canonical19387 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2650 + difference 0 2) (sourceB2650 + difference 2 0) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA2650 + difference 0 2) (sourceB2650 + difference 2 0) sourceC2650) = raw19388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw19388; decide +kernel
    rw [ha]
    exact (canonical19388 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2650 + difference 0 3) (sourceB2650 + difference 3 0) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2650 + difference 0 3) (sourceB2650 + difference 3 0) sourceC2650) = raw18295 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw18295; decide +kernel
    rw [ha]
    exact (canonical18295 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2650 + difference 0 4) (sourceB2650 + difference 4 0) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2650 + difference 0 4) (sourceB2650 + difference 4 0) sourceC2650) = raw19389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw19389; decide +kernel
    rw [ha]
    exact (canonical19389 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2650 + difference 0 5) (sourceB2650 + difference 5 0) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5488) := by
    have ha : (tripleCharges (sourceA2650 + difference 0 5) (sourceB2650 + difference 5 0) sourceC2650) = raw18346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw18346; decide +kernel
    rw [ha]
    exact (canonical18346 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2650 + difference 1 0) (sourceB2650 + difference 0 1) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2650 + difference 1 0) (sourceB2650 + difference 0 1) sourceC2650) = raw10230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw10230; decide +kernel
    rw [ha]
    exact (canonical10230 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2650 + difference 1 2) (sourceB2650 + difference 2 1) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2650 + difference 1 2) (sourceB2650 + difference 2 1) sourceC2650) = raw37244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw37244; decide +kernel
    rw [ha]
    exact (canonical37244 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2650 + difference 1 3) (sourceB2650 + difference 3 1) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA2650 + difference 1 3) (sourceB2650 + difference 3 1) sourceC2650) = raw10217 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw10217; decide +kernel
    rw [ha]
    exact (canonical10217 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2650 + difference 1 4) (sourceB2650 + difference 4 1) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA2650 + difference 1 4) (sourceB2650 + difference 4 1) sourceC2650) = raw37245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw37245; decide +kernel
    rw [ha]
    exact (canonical37245 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2650 + difference 1 5) (sourceB2650 + difference 5 1) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2650 + difference 1 5) (sourceB2650 + difference 5 1) sourceC2650) = raw12081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw12081; decide +kernel
    rw [ha]
    exact (canonical12081 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2650 + difference 2 0) (sourceB2650 + difference 0 2) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2650 + difference 2 0) (sourceB2650 + difference 0 2) sourceC2650) = raw10229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw10229; decide +kernel
    rw [ha]
    exact (canonical10229 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2650 + difference 2 1) (sourceB2650 + difference 1 2) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2650 + difference 2 1) (sourceB2650 + difference 1 2) sourceC2650) = raw18303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw18303; decide +kernel
    rw [ha]
    exact (canonical18303 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2650 + difference 2 3) (sourceB2650 + difference 3 2) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA2650 + difference 2 3) (sourceB2650 + difference 3 2) sourceC2650) = raw10216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw10216; decide +kernel
    rw [ha]
    exact (canonical10216 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2650 + difference 2 4) (sourceB2650 + difference 4 2) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA2650 + difference 2 4) (sourceB2650 + difference 4 2) sourceC2650) = raw18305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw18305; decide +kernel
    rw [ha]
    exact (canonical18305 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2650 + difference 2 5) (sourceB2650 + difference 5 2) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2650 + difference 2 5) (sourceB2650 + difference 5 2) sourceC2650) = raw12080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw12080; decide +kernel
    rw [ha]
    exact (canonical12080 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2650 + difference 3 0) (sourceB2650 + difference 0 3) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5114) := by
    have ha : (tripleCharges (sourceA2650 + difference 3 0) (sourceB2650 + difference 0 3) sourceC2650) = raw32034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw32034; decide +kernel
    rw [ha]
    exact (canonical32034 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2650 + difference 3 1) (sourceB2650 + difference 1 3) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5372) := by
    have ha : (tripleCharges (sourceA2650 + difference 3 1) (sourceB2650 + difference 1 3) sourceC2650) = raw35554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw35554; decide +kernel
    rw [ha]
    exact (canonical35554 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2650 + difference 3 2) (sourceB2650 + difference 2 3) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5372) := by
    have ha : (tripleCharges (sourceA2650 + difference 3 2) (sourceB2650 + difference 2 3) sourceC2650) = raw37246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw37246; decide +kernel
    rw [ha]
    exact (canonical37246 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2650 + difference 3 4) (sourceB2650 + difference 4 3) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2650 + difference 3 4) (sourceB2650 + difference 4 3) sourceC2650) = raw37247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw37247; decide +kernel
    rw [ha]
    exact (canonical37247 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2650 + difference 3 5) (sourceB2650 + difference 5 3) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA2650 + difference 3 5) (sourceB2650 + difference 5 3) sourceC2650) = raw18353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw18353; decide +kernel
    rw [ha]
    exact (canonical18353 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2650 + difference 4 0) (sourceB2650 + difference 0 4) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5114) := by
    have ha : (tripleCharges (sourceA2650 + difference 4 0) (sourceB2650 + difference 0 4) sourceC2650) = raw29510 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw29510; decide +kernel
    rw [ha]
    exact (canonical29510 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2650 + difference 4 1) (sourceB2650 + difference 1 4) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5372) := by
    have ha : (tripleCharges (sourceA2650 + difference 4 1) (sourceB2650 + difference 1 4) sourceC2650) = raw34790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw34790; decide +kernel
    rw [ha]
    exact (canonical34790 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2650 + difference 4 2) (sourceB2650 + difference 2 4) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5372) := by
    have ha : (tripleCharges (sourceA2650 + difference 4 2) (sourceB2650 + difference 2 4) sourceC2650) = raw37248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw37248; decide +kernel
    rw [ha]
    exact (canonical37248 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2650 + difference 4 3) (sourceB2650 + difference 3 4) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2650 + difference 4 3) (sourceB2650 + difference 3 4) sourceC2650) = raw18307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw18307; decide +kernel
    rw [ha]
    exact (canonical18307 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2650 + difference 4 5) (sourceB2650 + difference 5 4) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA2650 + difference 4 5) (sourceB2650 + difference 5 4) sourceC2650) = raw18357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw18357; decide +kernel
    rw [ha]
    exact (canonical18357 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2650 + difference 5 0) (sourceB2650 + difference 0 5) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5113) := by
    have ha : (tripleCharges (sourceA2650 + difference 5 0) (sourceB2650 + difference 0 5) sourceC2650) = raw27561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw27561; decide +kernel
    rw [ha]
    exact (canonical27561 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2650 + difference 5 1) (sourceB2650 + difference 1 5) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5114) := by
    have ha : (tripleCharges (sourceA2650 + difference 5 1) (sourceB2650 + difference 1 5) sourceC2650) = raw35557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw35557; decide +kernel
    rw [ha]
    exact (canonical35557 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2650 + difference 5 2) (sourceB2650 + difference 2 5) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5114) := by
    have ha : (tripleCharges (sourceA2650 + difference 5 2) (sourceB2650 + difference 2 5) sourceC2650) = raw37249 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw37249; decide +kernel
    rw [ha]
    exact (canonical37249 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2650 + difference 5 3) (sourceB2650 + difference 3 5) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2650 + difference 5 3) (sourceB2650 + difference 3 5) sourceC2650) = raw18311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw18311; decide +kernel
    rw [ha]
    exact (canonical18311 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2650 + difference 5 4) (sourceB2650 + difference 4 5) sourceC2650) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2650 + difference 5 4) (sourceB2650 + difference 4 5) sourceC2650) = raw37250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2650 sourceB2650 sourceC2650 difference raw37250; decide +kernel
    rw [ha]
    exact (canonical37250 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2650 sourceB2650 sourceC2650
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2650, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2651 : Charge := ![-2, -1, -1, 1, 1, 2]
def sourceB2651 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2651 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceForm2651 : Integer.Sparse Master := [(Sum.inr 4759, 1), (Sum.inr 4763, 4), (Sum.inr 4801, 4), (Sum.inr 5335, 4), (Sum.inr 5351, 4), (Sum.inr 5416, 4), (Sum.inr 5423, 4), (Sum.inr 5433, 4), (Sum.inr 5497, 1)]

theorem sourceEq2651 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2651 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2651 + difference 0 1) (sourceB2651 + difference 1 0) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2651 + difference 0 1) (sourceB2651 + difference 1 0) sourceC2651) = raw37251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37251; decide +kernel
    rw [ha]
    exact (canonical37251 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2651 + difference 0 2) (sourceB2651 + difference 2 0) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2651 + difference 0 2) (sourceB2651 + difference 2 0) sourceC2651) = raw37252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37252; decide +kernel
    rw [ha]
    exact (canonical37252 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2651 + difference 0 3) (sourceB2651 + difference 3 0) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2651 + difference 0 3) (sourceB2651 + difference 3 0) sourceC2651) = raw18265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18265; decide +kernel
    rw [ha]
    exact (canonical18265 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2651 + difference 0 4) (sourceB2651 + difference 4 0) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2651 + difference 0 4) (sourceB2651 + difference 4 0) sourceC2651) = raw37253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37253; decide +kernel
    rw [ha]
    exact (canonical37253 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2651 + difference 0 5) (sourceB2651 + difference 5 0) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5497) := by
    have ha : (tripleCharges (sourceA2651 + difference 0 5) (sourceB2651 + difference 5 0) sourceC2651) = raw18382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18382; decide +kernel
    rw [ha]
    exact (canonical18382 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2651 + difference 1 0) (sourceB2651 + difference 0 1) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2651 + difference 1 0) (sourceB2651 + difference 0 1) sourceC2651) = raw34080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw34080; decide +kernel
    rw [ha]
    exact (canonical34080 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2651 + difference 1 2) (sourceB2651 + difference 2 1) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2651 + difference 1 2) (sourceB2651 + difference 2 1) sourceC2651) = raw37254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37254; decide +kernel
    rw [ha]
    exact (canonical37254 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2651 + difference 1 3) (sourceB2651 + difference 3 1) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA2651 + difference 1 3) (sourceB2651 + difference 3 1) sourceC2651) = raw18270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18270; decide +kernel
    rw [ha]
    exact (canonical18270 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2651 + difference 1 4) (sourceB2651 + difference 4 1) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA2651 + difference 1 4) (sourceB2651 + difference 4 1) sourceC2651) = raw37255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37255; decide +kernel
    rw [ha]
    exact (canonical37255 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2651 + difference 1 5) (sourceB2651 + difference 5 1) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2651 + difference 1 5) (sourceB2651 + difference 5 1) sourceC2651) = raw18386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18386; decide +kernel
    rw [ha]
    exact (canonical18386 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2651 + difference 2 0) (sourceB2651 + difference 0 2) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2651 + difference 2 0) (sourceB2651 + difference 0 2) sourceC2651) = raw18279 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18279; decide +kernel
    rw [ha]
    exact (canonical18279 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2651 + difference 2 1) (sourceB2651 + difference 1 2) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2651 + difference 2 1) (sourceB2651 + difference 1 2) sourceC2651) = raw18280 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18280; decide +kernel
    rw [ha]
    exact (canonical18280 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2651 + difference 2 3) (sourceB2651 + difference 3 2) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA2651 + difference 2 3) (sourceB2651 + difference 3 2) sourceC2651) = raw18402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18402; decide +kernel
    rw [ha]
    exact (canonical18402 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2651 + difference 2 4) (sourceB2651 + difference 4 2) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA2651 + difference 2 4) (sourceB2651 + difference 4 2) sourceC2651) = raw18282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18282; decide +kernel
    rw [ha]
    exact (canonical18282 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2651 + difference 2 5) (sourceB2651 + difference 5 2) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2651 + difference 2 5) (sourceB2651 + difference 5 2) sourceC2651) = raw18283 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18283; decide +kernel
    rw [ha]
    exact (canonical18283 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2651 + difference 3 0) (sourceB2651 + difference 0 3) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2651 + difference 3 0) (sourceB2651 + difference 0 3) sourceC2651) = raw34087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw34087; decide +kernel
    rw [ha]
    exact (canonical34087 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2651 + difference 3 1) (sourceB2651 + difference 1 3) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2651 + difference 3 1) (sourceB2651 + difference 1 3) sourceC2651) = raw37256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37256; decide +kernel
    rw [ha]
    exact (canonical37256 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2651 + difference 3 2) (sourceB2651 + difference 2 3) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2651 + difference 3 2) (sourceB2651 + difference 2 3) sourceC2651) = raw37257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37257; decide +kernel
    rw [ha]
    exact (canonical37257 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2651 + difference 3 4) (sourceB2651 + difference 4 3) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2651 + difference 3 4) (sourceB2651 + difference 4 3) sourceC2651) = raw37258 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37258; decide +kernel
    rw [ha]
    exact (canonical37258 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2651 + difference 3 5) (sourceB2651 + difference 5 3) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2651 + difference 3 5) (sourceB2651 + difference 5 3) sourceC2651) = raw18395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18395; decide +kernel
    rw [ha]
    exact (canonical18395 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2651 + difference 4 0) (sourceB2651 + difference 0 4) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2651 + difference 4 0) (sourceB2651 + difference 0 4) sourceC2651) = raw34091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw34091; decide +kernel
    rw [ha]
    exact (canonical34091 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2651 + difference 4 1) (sourceB2651 + difference 1 4) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2651 + difference 4 1) (sourceB2651 + difference 1 4) sourceC2651) = raw37259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37259; decide +kernel
    rw [ha]
    exact (canonical37259 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2651 + difference 4 2) (sourceB2651 + difference 2 4) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2651 + difference 4 2) (sourceB2651 + difference 2 4) sourceC2651) = raw37260 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37260; decide +kernel
    rw [ha]
    exact (canonical37260 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2651 + difference 4 3) (sourceB2651 + difference 3 4) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2651 + difference 4 3) (sourceB2651 + difference 3 4) sourceC2651) = raw18286 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18286; decide +kernel
    rw [ha]
    exact (canonical18286 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2651 + difference 4 5) (sourceB2651 + difference 5 4) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2651 + difference 4 5) (sourceB2651 + difference 5 4) sourceC2651) = raw18400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18400; decide +kernel
    rw [ha]
    exact (canonical18400 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2651 + difference 5 0) (sourceB2651 + difference 0 5) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4759) := by
    have ha : (tripleCharges (sourceA2651 + difference 5 0) (sourceB2651 + difference 0 5) sourceC2651) = raw34094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw34094; decide +kernel
    rw [ha]
    exact (canonical34094 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2651 + difference 5 1) (sourceB2651 + difference 1 5) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2651 + difference 5 1) (sourceB2651 + difference 1 5) sourceC2651) = raw37261 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37261; decide +kernel
    rw [ha]
    exact (canonical37261 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2651 + difference 5 2) (sourceB2651 + difference 2 5) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2651 + difference 5 2) (sourceB2651 + difference 2 5) sourceC2651) = raw37262 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37262; decide +kernel
    rw [ha]
    exact (canonical37262 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2651 + difference 5 3) (sourceB2651 + difference 3 5) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2651 + difference 5 3) (sourceB2651 + difference 3 5) sourceC2651) = raw18291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw18291; decide +kernel
    rw [ha]
    exact (canonical18291 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2651 + difference 5 4) (sourceB2651 + difference 4 5) sourceC2651) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2651 + difference 5 4) (sourceB2651 + difference 4 5) sourceC2651) = raw37263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2651 sourceB2651 sourceC2651 difference raw37263; decide +kernel
    rw [ha]
    exact (canonical37263 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2651 sourceB2651 sourceC2651
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2651, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2652 : Charge := ![-2, -1, -1, 1, 1, 2]
def sourceB2652 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2652 : Charge := ![0, 1, 1, -1, 1, -2]
def sourceForm2652 : Integer.Sparse Master := [(Sum.inr 4761, 1), (Sum.inr 4762, 1), (Sum.inr 4768, 1), (Sum.inr 4803, 2), (Sum.inr 5044, 2), (Sum.inr 5076, 1), (Sum.inr 5187, 1), (Sum.inr 5215, 2), (Sum.inr 5219, 1), (Sum.inr 5249, 1), (Sum.inr 5338, 2), (Sum.inr 5353, 2), (Sum.inr 5354, 1), (Sum.inr 5401, 2), (Sum.inr 5406, 2), (Sum.inr 5408, 1), (Sum.inr 5414, 1), (Sum.inr 5425, 2), (Sum.inr 5430, 2), (Sum.inr 5431, 1), (Sum.inr 5481, 1)]

theorem sourceEq2652 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2652 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2652 + difference 0 1) (sourceB2652 + difference 1 0) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA2652 + difference 0 1) (sourceB2652 + difference 1 0) sourceC2652) = raw37264 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37264; decide +kernel
    rw [ha]
    exact (canonical37264 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2652 + difference 0 2) (sourceB2652 + difference 2 0) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA2652 + difference 0 2) (sourceB2652 + difference 2 0) sourceC2652) = raw37265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37265; decide +kernel
    rw [ha]
    exact (canonical37265 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2652 + difference 0 3) (sourceB2652 + difference 3 0) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA2652 + difference 0 3) (sourceB2652 + difference 3 0) sourceC2652) = raw37266 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37266; decide +kernel
    rw [ha]
    exact (canonical37266 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2652 + difference 0 4) (sourceB2652 + difference 4 0) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA2652 + difference 0 4) (sourceB2652 + difference 4 0) sourceC2652) = raw37267 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37267; decide +kernel
    rw [ha]
    exact (canonical37267 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2652 + difference 0 5) (sourceB2652 + difference 5 0) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA2652 + difference 0 5) (sourceB2652 + difference 5 0) sourceC2652) = raw37268 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37268; decide +kernel
    rw [ha]
    exact (canonical37268 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2652 + difference 1 0) (sourceB2652 + difference 0 1) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA2652 + difference 1 0) (sourceB2652 + difference 0 1) sourceC2652) = raw37269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37269; decide +kernel
    rw [ha]
    exact (canonical37269 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2652 + difference 1 2) (sourceB2652 + difference 2 1) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA2652 + difference 1 2) (sourceB2652 + difference 2 1) sourceC2652) = raw37270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37270; decide +kernel
    rw [ha]
    exact (canonical37270 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2652 + difference 1 3) (sourceB2652 + difference 3 1) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA2652 + difference 1 3) (sourceB2652 + difference 3 1) sourceC2652) = raw37271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37271; decide +kernel
    rw [ha]
    exact (canonical37271 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2652 + difference 1 4) (sourceB2652 + difference 4 1) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA2652 + difference 1 4) (sourceB2652 + difference 4 1) sourceC2652) = raw37272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37272; decide +kernel
    rw [ha]
    exact (canonical37272 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2652 + difference 1 5) (sourceB2652 + difference 5 1) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA2652 + difference 1 5) (sourceB2652 + difference 5 1) sourceC2652) = raw37273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37273; decide +kernel
    rw [ha]
    exact (canonical37273 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2652 + difference 2 0) (sourceB2652 + difference 0 2) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA2652 + difference 2 0) (sourceB2652 + difference 0 2) sourceC2652) = raw37274 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37274; decide +kernel
    rw [ha]
    exact (canonical37274 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2652 + difference 2 1) (sourceB2652 + difference 1 2) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA2652 + difference 2 1) (sourceB2652 + difference 1 2) sourceC2652) = raw37275 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37275; decide +kernel
    rw [ha]
    exact (canonical37275 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2652 + difference 2 3) (sourceB2652 + difference 3 2) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA2652 + difference 2 3) (sourceB2652 + difference 3 2) sourceC2652) = raw37276 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37276; decide +kernel
    rw [ha]
    exact (canonical37276 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2652 + difference 2 4) (sourceB2652 + difference 4 2) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA2652 + difference 2 4) (sourceB2652 + difference 4 2) sourceC2652) = raw37277 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37277; decide +kernel
    rw [ha]
    exact (canonical37277 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2652 + difference 2 5) (sourceB2652 + difference 5 2) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA2652 + difference 2 5) (sourceB2652 + difference 5 2) sourceC2652) = raw37278 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37278; decide +kernel
    rw [ha]
    exact (canonical37278 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2652 + difference 3 0) (sourceB2652 + difference 0 3) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4768) := by
    have ha : (tripleCharges (sourceA2652 + difference 3 0) (sourceB2652 + difference 0 3) sourceC2652) = raw37279 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37279; decide +kernel
    rw [ha]
    exact (canonical37279 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2652 + difference 3 1) (sourceB2652 + difference 1 3) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5338) := by
    have ha : (tripleCharges (sourceA2652 + difference 3 1) (sourceB2652 + difference 1 3) sourceC2652) = raw37280 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37280; decide +kernel
    rw [ha]
    exact (canonical37280 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2652 + difference 3 2) (sourceB2652 + difference 2 3) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5338) := by
    have ha : (tripleCharges (sourceA2652 + difference 3 2) (sourceB2652 + difference 2 3) sourceC2652) = raw37281 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37281; decide +kernel
    rw [ha]
    exact (canonical37281 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2652 + difference 3 4) (sourceB2652 + difference 4 3) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2652 + difference 3 4) (sourceB2652 + difference 4 3) sourceC2652) = raw37282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37282; decide +kernel
    rw [ha]
    exact (canonical37282 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2652 + difference 3 5) (sourceB2652 + difference 5 3) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA2652 + difference 3 5) (sourceB2652 + difference 5 3) sourceC2652) = raw37283 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37283; decide +kernel
    rw [ha]
    exact (canonical37283 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2652 + difference 4 0) (sourceB2652 + difference 0 4) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4762) := by
    have ha : (tripleCharges (sourceA2652 + difference 4 0) (sourceB2652 + difference 0 4) sourceC2652) = raw37284 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37284; decide +kernel
    rw [ha]
    exact (canonical37284 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2652 + difference 4 1) (sourceB2652 + difference 1 4) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5215) := by
    have ha : (tripleCharges (sourceA2652 + difference 4 1) (sourceB2652 + difference 1 4) sourceC2652) = raw37285 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37285; decide +kernel
    rw [ha]
    exact (canonical37285 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2652 + difference 4 2) (sourceB2652 + difference 2 4) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5215) := by
    have ha : (tripleCharges (sourceA2652 + difference 4 2) (sourceB2652 + difference 2 4) sourceC2652) = raw37286 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37286; decide +kernel
    rw [ha]
    exact (canonical37286 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2652 + difference 4 3) (sourceB2652 + difference 3 4) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA2652 + difference 4 3) (sourceB2652 + difference 3 4) sourceC2652) = raw37287 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37287; decide +kernel
    rw [ha]
    exact (canonical37287 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2652 + difference 4 5) (sourceB2652 + difference 5 4) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA2652 + difference 4 5) (sourceB2652 + difference 5 4) sourceC2652) = raw37288 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37288; decide +kernel
    rw [ha]
    exact (canonical37288 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2652 + difference 5 0) (sourceB2652 + difference 0 5) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4761) := by
    have ha : (tripleCharges (sourceA2652 + difference 5 0) (sourceB2652 + difference 0 5) sourceC2652) = raw37289 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37289; decide +kernel
    rw [ha]
    exact (canonical37289 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2652 + difference 5 1) (sourceB2652 + difference 1 5) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5044) := by
    have ha : (tripleCharges (sourceA2652 + difference 5 1) (sourceB2652 + difference 1 5) sourceC2652) = raw37290 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37290; decide +kernel
    rw [ha]
    exact (canonical37290 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2652 + difference 5 2) (sourceB2652 + difference 2 5) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5044) := by
    have ha : (tripleCharges (sourceA2652 + difference 5 2) (sourceB2652 + difference 2 5) sourceC2652) = raw37291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37291; decide +kernel
    rw [ha]
    exact (canonical37291 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2652 + difference 5 3) (sourceB2652 + difference 3 5) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA2652 + difference 5 3) (sourceB2652 + difference 3 5) sourceC2652) = raw37292 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37292; decide +kernel
    rw [ha]
    exact (canonical37292 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2652 + difference 5 4) (sourceB2652 + difference 4 5) sourceC2652) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2652 + difference 5 4) (sourceB2652 + difference 4 5) sourceC2652) = raw37293 := by
      apply Matrix.ext; unfold tripleCharges sourceA2652 sourceB2652 sourceC2652 difference raw37293; decide +kernel
    rw [ha]
    exact (canonical37293 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2652 sourceB2652 sourceC2652
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2652, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2653 : Charge := ![-2, -1, -1, 1, 1, 2]
def sourceB2653 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2653 : Charge := ![0, 1, 1, -1, 1, -2]
def sourceForm2653 : Integer.Sparse Master := [(Sum.inr 2171, 1), (Sum.inr 2175, 1), (Sum.inr 2178, 1), (Sum.inr 2195, 2), (Sum.inr 2653, 2), (Sum.inr 2661, 1), (Sum.inr 2708, 1), (Sum.inr 3474, 2), (Sum.inr 3477, 1), (Sum.inr 3537, 1), (Sum.inr 3755, 2), (Sum.inr 3761, 2), (Sum.inr 3769, 1), (Sum.inr 3804, 2), (Sum.inr 3806, 1), (Sum.inr 3812, 2), (Sum.inr 3840, 2), (Sum.inr 3849, 1), (Sum.inr 3869, 1), (Sum.inr 3871, 2), (Sum.inr 3979, 1)]

theorem sourceEq2653 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2653 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2653 + difference 0 1) (sourceB2653 + difference 1 0) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA2653 + difference 0 1) (sourceB2653 + difference 1 0) sourceC2653) = raw37294 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37294; decide +kernel
    rw [ha]
    exact (canonical37294 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2653 + difference 0 2) (sourceB2653 + difference 2 0) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA2653 + difference 0 2) (sourceB2653 + difference 2 0) sourceC2653) = raw37295 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37295; decide +kernel
    rw [ha]
    exact (canonical37295 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2653 + difference 0 3) (sourceB2653 + difference 3 0) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA2653 + difference 0 3) (sourceB2653 + difference 3 0) sourceC2653) = raw37296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37296; decide +kernel
    rw [ha]
    exact (canonical37296 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2653 + difference 0 4) (sourceB2653 + difference 4 0) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA2653 + difference 0 4) (sourceB2653 + difference 4 0) sourceC2653) = raw37297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37297; decide +kernel
    rw [ha]
    exact (canonical37297 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2653 + difference 0 5) (sourceB2653 + difference 5 0) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA2653 + difference 0 5) (sourceB2653 + difference 5 0) sourceC2653) = raw37298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37298; decide +kernel
    rw [ha]
    exact (canonical37298 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2653 + difference 1 0) (sourceB2653 + difference 0 1) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA2653 + difference 1 0) (sourceB2653 + difference 0 1) sourceC2653) = raw37299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37299; decide +kernel
    rw [ha]
    exact (canonical37299 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2653 + difference 1 2) (sourceB2653 + difference 2 1) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA2653 + difference 1 2) (sourceB2653 + difference 2 1) sourceC2653) = raw37300 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37300; decide +kernel
    rw [ha]
    exact (canonical37300 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2653 + difference 1 3) (sourceB2653 + difference 3 1) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA2653 + difference 1 3) (sourceB2653 + difference 3 1) sourceC2653) = raw37301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37301; decide +kernel
    rw [ha]
    exact (canonical37301 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2653 + difference 1 4) (sourceB2653 + difference 4 1) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA2653 + difference 1 4) (sourceB2653 + difference 4 1) sourceC2653) = raw37302 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37302; decide +kernel
    rw [ha]
    exact (canonical37302 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2653 + difference 1 5) (sourceB2653 + difference 5 1) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA2653 + difference 1 5) (sourceB2653 + difference 5 1) sourceC2653) = raw37303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37303; decide +kernel
    rw [ha]
    exact (canonical37303 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2653 + difference 2 0) (sourceB2653 + difference 0 2) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA2653 + difference 2 0) (sourceB2653 + difference 0 2) sourceC2653) = raw37304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37304; decide +kernel
    rw [ha]
    exact (canonical37304 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2653 + difference 2 1) (sourceB2653 + difference 1 2) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA2653 + difference 2 1) (sourceB2653 + difference 1 2) sourceC2653) = raw37305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37305; decide +kernel
    rw [ha]
    exact (canonical37305 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2653 + difference 2 3) (sourceB2653 + difference 3 2) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA2653 + difference 2 3) (sourceB2653 + difference 3 2) sourceC2653) = raw37306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37306; decide +kernel
    rw [ha]
    exact (canonical37306 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2653 + difference 2 4) (sourceB2653 + difference 4 2) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA2653 + difference 2 4) (sourceB2653 + difference 4 2) sourceC2653) = raw37307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37307; decide +kernel
    rw [ha]
    exact (canonical37307 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2653 + difference 2 5) (sourceB2653 + difference 5 2) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA2653 + difference 2 5) (sourceB2653 + difference 5 2) sourceC2653) = raw37308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37308; decide +kernel
    rw [ha]
    exact (canonical37308 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2653 + difference 3 0) (sourceB2653 + difference 0 3) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2178) := by
    have ha : (tripleCharges (sourceA2653 + difference 3 0) (sourceB2653 + difference 0 3) sourceC2653) = raw37309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37309; decide +kernel
    rw [ha]
    exact (canonical37309 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2653 + difference 3 1) (sourceB2653 + difference 1 3) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3755) := by
    have ha : (tripleCharges (sourceA2653 + difference 3 1) (sourceB2653 + difference 1 3) sourceC2653) = raw37310 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37310; decide +kernel
    rw [ha]
    exact (canonical37310 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2653 + difference 3 2) (sourceB2653 + difference 2 3) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3755) := by
    have ha : (tripleCharges (sourceA2653 + difference 3 2) (sourceB2653 + difference 2 3) sourceC2653) = raw37311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37311; decide +kernel
    rw [ha]
    exact (canonical37311 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2653 + difference 3 4) (sourceB2653 + difference 4 3) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA2653 + difference 3 4) (sourceB2653 + difference 4 3) sourceC2653) = raw37312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37312; decide +kernel
    rw [ha]
    exact (canonical37312 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2653 + difference 3 5) (sourceB2653 + difference 5 3) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA2653 + difference 3 5) (sourceB2653 + difference 5 3) sourceC2653) = raw37313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37313; decide +kernel
    rw [ha]
    exact (canonical37313 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2653 + difference 4 0) (sourceB2653 + difference 0 4) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2171) := by
    have ha : (tripleCharges (sourceA2653 + difference 4 0) (sourceB2653 + difference 0 4) sourceC2653) = raw37314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37314; decide +kernel
    rw [ha]
    exact (canonical37314 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2653 + difference 4 1) (sourceB2653 + difference 1 4) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2653) := by
    have ha : (tripleCharges (sourceA2653 + difference 4 1) (sourceB2653 + difference 1 4) sourceC2653) = raw37315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37315; decide +kernel
    rw [ha]
    exact (canonical37315 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2653 + difference 4 2) (sourceB2653 + difference 2 4) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2653) := by
    have ha : (tripleCharges (sourceA2653 + difference 4 2) (sourceB2653 + difference 2 4) sourceC2653) = raw37316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37316; decide +kernel
    rw [ha]
    exact (canonical37316 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2653 + difference 4 3) (sourceB2653 + difference 3 4) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA2653 + difference 4 3) (sourceB2653 + difference 3 4) sourceC2653) = raw37317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37317; decide +kernel
    rw [ha]
    exact (canonical37317 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2653 + difference 4 5) (sourceB2653 + difference 5 4) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA2653 + difference 4 5) (sourceB2653 + difference 5 4) sourceC2653) = raw37318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37318; decide +kernel
    rw [ha]
    exact (canonical37318 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2653 + difference 5 0) (sourceB2653 + difference 0 5) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2175) := by
    have ha : (tripleCharges (sourceA2653 + difference 5 0) (sourceB2653 + difference 0 5) sourceC2653) = raw37319 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37319; decide +kernel
    rw [ha]
    exact (canonical37319 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2653 + difference 5 1) (sourceB2653 + difference 1 5) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3474) := by
    have ha : (tripleCharges (sourceA2653 + difference 5 1) (sourceB2653 + difference 1 5) sourceC2653) = raw37320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37320; decide +kernel
    rw [ha]
    exact (canonical37320 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2653 + difference 5 2) (sourceB2653 + difference 2 5) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3474) := by
    have ha : (tripleCharges (sourceA2653 + difference 5 2) (sourceB2653 + difference 2 5) sourceC2653) = raw37321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37321; decide +kernel
    rw [ha]
    exact (canonical37321 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2653 + difference 5 3) (sourceB2653 + difference 3 5) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA2653 + difference 5 3) (sourceB2653 + difference 3 5) sourceC2653) = raw37322 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37322; decide +kernel
    rw [ha]
    exact (canonical37322 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2653 + difference 5 4) (sourceB2653 + difference 4 5) sourceC2653) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3477) := by
    have ha : (tripleCharges (sourceA2653 + difference 5 4) (sourceB2653 + difference 4 5) sourceC2653) = raw37323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2653 sourceB2653 sourceC2653 difference raw37323; decide +kernel
    rw [ha]
    exact (canonical37323 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2653 sourceB2653 sourceC2653
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2653, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2654 : Charge := ![-2, -1, -1, 1, 1, 2]
def sourceB2654 : Charge := ![2, 1, 1, -1, -1, -2]
def sourceC2654 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm2654 : Integer.Sparse Master := [(Sum.inr 4077, 1), (Sum.inr 4078, 4), (Sum.inr 4080, 4), (Sum.inr 4086, 4), (Sum.inr 4088, 4), (Sum.inr 4090, 4), (Sum.inr 4091, 4), (Sum.inr 4092, 4), (Sum.inr 4095, 1)]

theorem sourceEq2654 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2654 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2654 + difference 0 1) (sourceB2654 + difference 1 0) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2654 + difference 0 1) (sourceB2654 + difference 1 0) sourceC2654) = raw19404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw19404; decide +kernel
    rw [ha]
    exact (canonical19404 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2654 + difference 0 2) (sourceB2654 + difference 2 0) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2654 + difference 0 2) (sourceB2654 + difference 2 0) sourceC2654) = raw19405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw19405; decide +kernel
    rw [ha]
    exact (canonical19405 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2654 + difference 0 3) (sourceB2654 + difference 3 0) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2654 + difference 0 3) (sourceB2654 + difference 3 0) sourceC2654) = raw3449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw3449; decide +kernel
    rw [ha]
    exact (canonical3449 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2654 + difference 0 4) (sourceB2654 + difference 4 0) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2654 + difference 0 4) (sourceB2654 + difference 4 0) sourceC2654) = raw19406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw19406; decide +kernel
    rw [ha]
    exact (canonical19406 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2654 + difference 0 5) (sourceB2654 + difference 5 0) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4095) := by
    have ha : (tripleCharges (sourceA2654 + difference 0 5) (sourceB2654 + difference 5 0) sourceC2654) = raw3441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw3441; decide +kernel
    rw [ha]
    exact (canonical3441 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2654 + difference 1 0) (sourceB2654 + difference 0 1) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2654 + difference 1 0) (sourceB2654 + difference 0 1) sourceC2654) = raw11539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw11539; decide +kernel
    rw [ha]
    exact (canonical11539 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2654 + difference 1 2) (sourceB2654 + difference 2 1) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2654 + difference 1 2) (sourceB2654 + difference 2 1) sourceC2654) = raw37324 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37324; decide +kernel
    rw [ha]
    exact (canonical37324 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2654 + difference 1 3) (sourceB2654 + difference 3 1) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2654 + difference 1 3) (sourceB2654 + difference 3 1) sourceC2654) = raw2931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw2931; decide +kernel
    rw [ha]
    exact (canonical2931 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2654 + difference 1 4) (sourceB2654 + difference 4 1) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2654 + difference 1 4) (sourceB2654 + difference 4 1) sourceC2654) = raw2926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw2926; decide +kernel
    rw [ha]
    exact (canonical2926 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2654 + difference 1 5) (sourceB2654 + difference 5 1) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2654 + difference 1 5) (sourceB2654 + difference 5 1) sourceC2654) = raw3333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw3333; decide +kernel
    rw [ha]
    exact (canonical3333 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2654 + difference 2 0) (sourceB2654 + difference 0 2) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2654 + difference 2 0) (sourceB2654 + difference 0 2) sourceC2654) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2654 + difference 2 1) (sourceB2654 + difference 1 2) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2654 + difference 2 1) (sourceB2654 + difference 1 2) sourceC2654) = raw18337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw18337; decide +kernel
    rw [ha]
    exact (canonical18337 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2654 + difference 2 3) (sourceB2654 + difference 3 2) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2654 + difference 2 3) (sourceB2654 + difference 3 2) sourceC2654) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2654 + difference 2 4) (sourceB2654 + difference 4 2) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2654 + difference 2 4) (sourceB2654 + difference 4 2) sourceC2654) = raw2925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw2925; decide +kernel
    rw [ha]
    exact (canonical2925 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2654 + difference 2 5) (sourceB2654 + difference 5 2) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA2654 + difference 2 5) (sourceB2654 + difference 5 2) sourceC2654) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2654 + difference 3 0) (sourceB2654 + difference 0 3) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2654 + difference 3 0) (sourceB2654 + difference 0 3) sourceC2654) = raw34408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw34408; decide +kernel
    rw [ha]
    exact (canonical34408 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2654 + difference 3 1) (sourceB2654 + difference 1 3) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2654 + difference 3 1) (sourceB2654 + difference 1 3) sourceC2654) = raw37022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37022; decide +kernel
    rw [ha]
    exact (canonical37022 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2654 + difference 3 2) (sourceB2654 + difference 2 3) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2654 + difference 3 2) (sourceB2654 + difference 2 3) sourceC2654) = raw37325 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37325; decide +kernel
    rw [ha]
    exact (canonical37325 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2654 + difference 3 4) (sourceB2654 + difference 4 3) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2654 + difference 3 4) (sourceB2654 + difference 4 3) sourceC2654) = raw37326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37326; decide +kernel
    rw [ha]
    exact (canonical37326 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2654 + difference 3 5) (sourceB2654 + difference 5 3) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2654 + difference 3 5) (sourceB2654 + difference 5 3) sourceC2654) = raw19364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw19364; decide +kernel
    rw [ha]
    exact (canonical19364 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2654 + difference 4 0) (sourceB2654 + difference 0 4) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2654 + difference 4 0) (sourceB2654 + difference 0 4) sourceC2654) = raw31881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw31881; decide +kernel
    rw [ha]
    exact (canonical31881 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2654 + difference 4 1) (sourceB2654 + difference 1 4) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2654 + difference 4 1) (sourceB2654 + difference 1 4) sourceC2654) = raw35541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw35541; decide +kernel
    rw [ha]
    exact (canonical35541 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2654 + difference 4 2) (sourceB2654 + difference 2 4) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2654 + difference 4 2) (sourceB2654 + difference 2 4) sourceC2654) = raw37327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37327; decide +kernel
    rw [ha]
    exact (canonical37327 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2654 + difference 4 3) (sourceB2654 + difference 3 4) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2654 + difference 4 3) (sourceB2654 + difference 3 4) sourceC2654) = raw18340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw18340; decide +kernel
    rw [ha]
    exact (canonical18340 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2654 + difference 4 5) (sourceB2654 + difference 5 4) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2654 + difference 4 5) (sourceB2654 + difference 5 4) sourceC2654) = raw19368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw19368; decide +kernel
    rw [ha]
    exact (canonical19368 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2654 + difference 5 0) (sourceB2654 + difference 0 5) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4077) := by
    have ha : (tripleCharges (sourceA2654 + difference 5 0) (sourceB2654 + difference 0 5) sourceC2654) = raw29298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw29298; decide +kernel
    rw [ha]
    exact (canonical29298 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2654 + difference 5 1) (sourceB2654 + difference 1 5) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2654 + difference 5 1) (sourceB2654 + difference 1 5) sourceC2654) = raw37025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37025; decide +kernel
    rw [ha]
    exact (canonical37025 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2654 + difference 5 2) (sourceB2654 + difference 2 5) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2654 + difference 5 2) (sourceB2654 + difference 2 5) sourceC2654) = raw37328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37328; decide +kernel
    rw [ha]
    exact (canonical37328 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2654 + difference 5 3) (sourceB2654 + difference 3 5) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2654 + difference 5 3) (sourceB2654 + difference 3 5) sourceC2654) = raw18343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw18343; decide +kernel
    rw [ha]
    exact (canonical18343 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2654 + difference 5 4) (sourceB2654 + difference 4 5) sourceC2654) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2654 + difference 5 4) (sourceB2654 + difference 4 5) sourceC2654) = raw37329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2654 sourceB2654 sourceC2654 difference raw37329; decide +kernel
    rw [ha]
    exact (canonical37329 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2654 sourceB2654 sourceC2654
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2654, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2655 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2655 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2655 : Charge := ![-5, 0, 0, 0, 0, 5]
def sourceForm2655 : Integer.Sparse Master := [(Sum.inr 1534, 4), (Sum.inr 1541, 2), (Sum.inr 4062, -1)]

theorem sourceEq2655 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2655 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2655 + difference 0 4) (sourceB2655 + difference 4 0) sourceC2655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1541) := by
    have ha : (tripleCharges (sourceA2655 + difference 0 4) (sourceB2655 + difference 4 0) sourceC2655) = raw37330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2655 sourceB2655 sourceC2655 difference raw37330; decide +kernel
    rw [ha]
    exact (canonical37330 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2655 + difference 1 4) (sourceB2655 + difference 4 1) sourceC2655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1534) := by
    have ha : (tripleCharges (sourceA2655 + difference 1 4) (sourceB2655 + difference 4 1) sourceC2655) = raw37331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2655 sourceB2655 sourceC2655 difference raw37331; decide +kernel
    rw [ha]
    exact (canonical37331 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2655 + difference 2 4) (sourceB2655 + difference 4 2) sourceC2655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1534) := by
    have ha : (tripleCharges (sourceA2655 + difference 2 4) (sourceB2655 + difference 4 2) sourceC2655) = raw37332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2655 sourceB2655 sourceC2655 difference raw37332; decide +kernel
    rw [ha]
    exact (canonical37332 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2655 + difference 3 4) (sourceB2655 + difference 4 3) sourceC2655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1534) := by
    have ha : (tripleCharges (sourceA2655 + difference 3 4) (sourceB2655 + difference 4 3) sourceC2655) = raw37333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2655 sourceB2655 sourceC2655 difference raw37333; decide +kernel
    rw [ha]
    exact (canonical37333 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2655 + difference 4 4) (sourceB2655 + difference 4 4) sourceC2655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1534) := by
    have ha : (tripleCharges (sourceA2655 + difference 4 4) (sourceB2655 + difference 4 4) sourceC2655) = raw37334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2655 sourceB2655 sourceC2655 difference raw37334; decide +kernel
    rw [ha]
    exact (canonical37334 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2655 + difference 5 4) (sourceB2655 + difference 4 5) sourceC2655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1541) := by
    have ha : (tripleCharges (sourceA2655 + difference 5 4) (sourceB2655 + difference 4 5) sourceC2655) = raw37335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2655 sourceB2655 sourceC2655 difference raw37335; decide +kernel
    rw [ha]
    exact (canonical37335 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2655 + sourceB2655) sourceC2655) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4062) := by
    have ha : (doubleCharges (sourceA2655 + sourceB2655) sourceC2655) = raw37336 := by
      apply Matrix.ext; unfold doubleCharges sourceA2655 sourceB2655 sourceC2655 raw37336; decide +kernel
    rw [ha]
    exact (canonical37336 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2655 sourceB2655 sourceC2655
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2655, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
