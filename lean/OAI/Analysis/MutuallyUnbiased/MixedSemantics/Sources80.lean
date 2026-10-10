import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical97
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical116
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical133
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical140
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical142
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical144
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical145
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical151
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical174
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical193
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical220
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical228
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical235
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical250
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical252
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical254
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical263
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical268
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical269
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical271
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical272
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical274
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical275
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical276
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical277
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical278
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical279
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical280
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical281

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2560 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2560 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC2560 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceForm2560 : Integer.Sparse Master := [(Sum.inr 1764, 1), (Sum.inr 1766, 2), (Sum.inr 1782, 1), (Sum.inr 2029, 1), (Sum.inr 2299, 1), (Sum.inr 2300, 2), (Sum.inr 2314, 1), (Sum.inr 2318, 2), (Sum.inr 2337, 2), (Sum.inr 2489, 1), (Sum.inr 2561, 2), (Sum.inr 3669, 1), (Sum.inr 3672, 1), (Sum.inr 3690, 2), (Sum.inr 3705, 2), (Sum.inr 3779, 1), (Sum.inr 3824, 1), (Sum.inr 3852, 2), (Sum.inr 3921, 1), (Sum.inr 3931, 1), (Sum.inr 3981, 2)]

theorem sourceEq2560 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2560 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2560 + difference 0 1) (sourceB2560 + difference 1 0) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2560 + difference 0 1) (sourceB2560 + difference 1 0) sourceC2560) = raw35363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35363; decide +kernel
    rw [ha]
    exact (canonical35363 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2560 + difference 0 2) (sourceB2560 + difference 2 0) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA2560 + difference 0 2) (sourceB2560 + difference 2 0) sourceC2560) = raw35364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35364; decide +kernel
    rw [ha]
    exact (canonical35364 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2560 + difference 0 3) (sourceB2560 + difference 3 0) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3705) := by
    have ha : (tripleCharges (sourceA2560 + difference 0 3) (sourceB2560 + difference 3 0) sourceC2560) = raw35365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35365; decide +kernel
    rw [ha]
    exact (canonical35365 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2560 + difference 0 4) (sourceB2560 + difference 4 0) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA2560 + difference 0 4) (sourceB2560 + difference 4 0) sourceC2560) = raw17103 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw17103; decide +kernel
    rw [ha]
    exact (canonical17103 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2560 + difference 0 5) (sourceB2560 + difference 5 0) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA2560 + difference 0 5) (sourceB2560 + difference 5 0) sourceC2560) = raw35366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35366; decide +kernel
    rw [ha]
    exact (canonical35366 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2560 + difference 1 0) (sourceB2560 + difference 0 1) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2560 + difference 1 0) (sourceB2560 + difference 0 1) sourceC2560) = raw9883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw9883; decide +kernel
    rw [ha]
    exact (canonical9883 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2560 + difference 1 2) (sourceB2560 + difference 2 1) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA2560 + difference 1 2) (sourceB2560 + difference 2 1) sourceC2560) = raw17114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw17114; decide +kernel
    rw [ha]
    exact (canonical17114 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2560 + difference 1 3) (sourceB2560 + difference 3 1) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3705) := by
    have ha : (tripleCharges (sourceA2560 + difference 1 3) (sourceB2560 + difference 3 1) sourceC2560) = raw17115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw17115; decide +kernel
    rw [ha]
    exact (canonical17115 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2560 + difference 1 4) (sourceB2560 + difference 4 1) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA2560 + difference 1 4) (sourceB2560 + difference 4 1) sourceC2560) = raw3175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw3175; decide +kernel
    rw [ha]
    exact (canonical3175 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2560 + difference 1 5) (sourceB2560 + difference 5 1) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA2560 + difference 1 5) (sourceB2560 + difference 5 1) sourceC2560) = raw3170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw3170; decide +kernel
    rw [ha]
    exact (canonical3170 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2560 + difference 2 0) (sourceB2560 + difference 0 2) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2318) := by
    have ha : (tripleCharges (sourceA2560 + difference 2 0) (sourceB2560 + difference 0 2) sourceC2560) = raw30153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw30153; decide +kernel
    rw [ha]
    exact (canonical30153 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2560 + difference 2 1) (sourceB2560 + difference 1 2) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2318) := by
    have ha : (tripleCharges (sourceA2560 + difference 2 1) (sourceB2560 + difference 1 2) sourceC2560) = raw35367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35367; decide +kernel
    rw [ha]
    exact (canonical35367 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2560 + difference 2 3) (sourceB2560 + difference 3 2) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3669) := by
    have ha : (tripleCharges (sourceA2560 + difference 2 3) (sourceB2560 + difference 3 2) sourceC2560) = raw35368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35368; decide +kernel
    rw [ha]
    exact (canonical35368 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2560 + difference 2 4) (sourceB2560 + difference 4 2) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3921) := by
    have ha : (tripleCharges (sourceA2560 + difference 2 4) (sourceB2560 + difference 4 2) sourceC2560) = raw17107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw17107; decide +kernel
    rw [ha]
    exact (canonical17107 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2560 + difference 2 5) (sourceB2560 + difference 5 2) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3779) := by
    have ha : (tripleCharges (sourceA2560 + difference 2 5) (sourceB2560 + difference 5 2) sourceC2560) = raw35369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35369; decide +kernel
    rw [ha]
    exact (canonical35369 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2560 + difference 3 0) (sourceB2560 + difference 0 3) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2337) := by
    have ha : (tripleCharges (sourceA2560 + difference 3 0) (sourceB2560 + difference 0 3) sourceC2560) = raw30157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw30157; decide +kernel
    rw [ha]
    exact (canonical30157 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2560 + difference 3 1) (sourceB2560 + difference 1 3) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2337) := by
    have ha : (tripleCharges (sourceA2560 + difference 3 1) (sourceB2560 + difference 1 3) sourceC2560) = raw35370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35370; decide +kernel
    rw [ha]
    exact (canonical35370 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2560 + difference 3 2) (sourceB2560 + difference 2 3) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3672) := by
    have ha : (tripleCharges (sourceA2560 + difference 3 2) (sourceB2560 + difference 2 3) sourceC2560) = raw35371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35371; decide +kernel
    rw [ha]
    exact (canonical35371 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2560 + difference 3 4) (sourceB2560 + difference 4 3) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA2560 + difference 3 4) (sourceB2560 + difference 4 3) sourceC2560) = raw17110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw17110; decide +kernel
    rw [ha]
    exact (canonical17110 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2560 + difference 3 5) (sourceB2560 + difference 5 3) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3824) := by
    have ha : (tripleCharges (sourceA2560 + difference 3 5) (sourceB2560 + difference 5 3) sourceC2560) = raw35372 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35372; decide +kernel
    rw [ha]
    exact (canonical35372 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2560 + difference 4 0) (sourceB2560 + difference 0 4) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1766) := by
    have ha : (tripleCharges (sourceA2560 + difference 4 0) (sourceB2560 + difference 0 4) sourceC2560) = raw30161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw30161; decide +kernel
    rw [ha]
    exact (canonical30161 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2560 + difference 4 1) (sourceB2560 + difference 1 4) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1766) := by
    have ha : (tripleCharges (sourceA2560 + difference 4 1) (sourceB2560 + difference 1 4) sourceC2560) = raw35373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35373; decide +kernel
    rw [ha]
    exact (canonical35373 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2560 + difference 4 2) (sourceB2560 + difference 2 4) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1764) := by
    have ha : (tripleCharges (sourceA2560 + difference 4 2) (sourceB2560 + difference 2 4) sourceC2560) = raw35374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35374; decide +kernel
    rw [ha]
    exact (canonical35374 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2560 + difference 4 3) (sourceB2560 + difference 3 4) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1782) := by
    have ha : (tripleCharges (sourceA2560 + difference 4 3) (sourceB2560 + difference 3 4) sourceC2560) = raw35375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35375; decide +kernel
    rw [ha]
    exact (canonical35375 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2560 + difference 4 5) (sourceB2560 + difference 5 4) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA2560 + difference 4 5) (sourceB2560 + difference 5 4) sourceC2560) = raw35376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35376; decide +kernel
    rw [ha]
    exact (canonical35376 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2560 + difference 5 0) (sourceB2560 + difference 0 5) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2300) := by
    have ha : (tripleCharges (sourceA2560 + difference 5 0) (sourceB2560 + difference 0 5) sourceC2560) = raw28790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw28790; decide +kernel
    rw [ha]
    exact (canonical28790 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2560 + difference 5 1) (sourceB2560 + difference 1 5) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2300) := by
    have ha : (tripleCharges (sourceA2560 + difference 5 1) (sourceB2560 + difference 1 5) sourceC2560) = raw35377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35377; decide +kernel
    rw [ha]
    exact (canonical35377 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2560 + difference 5 2) (sourceB2560 + difference 2 5) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2299) := by
    have ha : (tripleCharges (sourceA2560 + difference 5 2) (sourceB2560 + difference 2 5) sourceC2560) = raw35378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35378; decide +kernel
    rw [ha]
    exact (canonical35378 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2560 + difference 5 3) (sourceB2560 + difference 3 5) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2314) := by
    have ha : (tripleCharges (sourceA2560 + difference 5 3) (sourceB2560 + difference 3 5) sourceC2560) = raw35379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw35379; decide +kernel
    rw [ha]
    exact (canonical35379 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2560 + difference 5 4) (sourceB2560 + difference 4 5) sourceC2560) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2560 + difference 5 4) (sourceB2560 + difference 4 5) sourceC2560) = raw17116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2560 sourceB2560 sourceC2560 difference raw17116; decide +kernel
    rw [ha]
    exact (canonical17116 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2560 sourceB2560 sourceC2560
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2560, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2561 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB2561 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC2561 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceForm2561 : Integer.Sparse Master := [(Sum.inr 5012, 1), (Sum.inr 5015, 2), (Sum.inr 5020, 1), (Sum.inr 5236, 1), (Sum.inr 5321, 1), (Sum.inr 5327, 2), (Sum.inr 5330, 1), (Sum.inr 5341, 2), (Sum.inr 5343, 1), (Sum.inr 5348, 2), (Sum.inr 5355, 4), (Sum.inr 5356, 4), (Sum.inr 5361, 2), (Sum.inr 5371, 2), (Sum.inr 5377, 1), (Sum.inr 5390, 1), (Sum.inr 5458, 1), (Sum.inr 5466, 1)]

theorem sourceEq2561 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2561 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2561 + difference 0 1) (sourceB2561 + difference 1 0) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2561 + difference 0 1) (sourceB2561 + difference 1 0) sourceC2561) = raw35380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35380; decide +kernel
    rw [ha]
    exact (canonical35380 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2561 + difference 0 2) (sourceB2561 + difference 2 0) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5348) := by
    have ha : (tripleCharges (sourceA2561 + difference 0 2) (sourceB2561 + difference 2 0) sourceC2561) = raw35381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35381; decide +kernel
    rw [ha]
    exact (canonical35381 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2561 + difference 0 3) (sourceB2561 + difference 3 0) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5361) := by
    have ha : (tripleCharges (sourceA2561 + difference 0 3) (sourceB2561 + difference 3 0) sourceC2561) = raw35382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35382; decide +kernel
    rw [ha]
    exact (canonical35382 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2561 + difference 0 4) (sourceB2561 + difference 4 0) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2561 + difference 0 4) (sourceB2561 + difference 4 0) sourceC2561) = raw35261 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35261; decide +kernel
    rw [ha]
    exact (canonical35261 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2561 + difference 0 5) (sourceB2561 + difference 5 0) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2561 + difference 0 5) (sourceB2561 + difference 5 0) sourceC2561) = raw35383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35383; decide +kernel
    rw [ha]
    exact (canonical35383 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2561 + difference 1 0) (sourceB2561 + difference 0 1) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2561 + difference 1 0) (sourceB2561 + difference 0 1) sourceC2561) = raw34904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw34904; decide +kernel
    rw [ha]
    exact (canonical34904 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2561 + difference 1 2) (sourceB2561 + difference 2 1) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5348) := by
    have ha : (tripleCharges (sourceA2561 + difference 1 2) (sourceB2561 + difference 2 1) sourceC2561) = raw35384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35384; decide +kernel
    rw [ha]
    exact (canonical35384 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2561 + difference 1 3) (sourceB2561 + difference 3 1) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5361) := by
    have ha : (tripleCharges (sourceA2561 + difference 1 3) (sourceB2561 + difference 3 1) sourceC2561) = raw35385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35385; decide +kernel
    rw [ha]
    exact (canonical35385 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2561 + difference 1 4) (sourceB2561 + difference 4 1) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2561 + difference 1 4) (sourceB2561 + difference 4 1) sourceC2561) = raw34887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw34887; decide +kernel
    rw [ha]
    exact (canonical34887 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2561 + difference 1 5) (sourceB2561 + difference 5 1) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2561 + difference 1 5) (sourceB2561 + difference 5 1) sourceC2561) = raw35386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35386; decide +kernel
    rw [ha]
    exact (canonical35386 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2561 + difference 2 0) (sourceB2561 + difference 0 2) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA2561 + difference 2 0) (sourceB2561 + difference 0 2) sourceC2561) = raw35387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35387; decide +kernel
    rw [ha]
    exact (canonical35387 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2561 + difference 2 1) (sourceB2561 + difference 1 2) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA2561 + difference 2 1) (sourceB2561 + difference 1 2) sourceC2561) = raw35388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35388; decide +kernel
    rw [ha]
    exact (canonical35388 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2561 + difference 2 3) (sourceB2561 + difference 3 2) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5343) := by
    have ha : (tripleCharges (sourceA2561 + difference 2 3) (sourceB2561 + difference 3 2) sourceC2561) = raw35389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35389; decide +kernel
    rw [ha]
    exact (canonical35389 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2561 + difference 2 4) (sourceB2561 + difference 4 2) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5458) := by
    have ha : (tripleCharges (sourceA2561 + difference 2 4) (sourceB2561 + difference 4 2) sourceC2561) = raw35265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35265; decide +kernel
    rw [ha]
    exact (canonical35265 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2561 + difference 2 5) (sourceB2561 + difference 5 2) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5377) := by
    have ha : (tripleCharges (sourceA2561 + difference 2 5) (sourceB2561 + difference 5 2) sourceC2561) = raw35390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35390; decide +kernel
    rw [ha]
    exact (canonical35390 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2561 + difference 3 0) (sourceB2561 + difference 0 3) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2561 + difference 3 0) (sourceB2561 + difference 0 3) sourceC2561) = raw34902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw34902; decide +kernel
    rw [ha]
    exact (canonical34902 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2561 + difference 3 1) (sourceB2561 + difference 1 3) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2561 + difference 3 1) (sourceB2561 + difference 1 3) sourceC2561) = raw35271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35271; decide +kernel
    rw [ha]
    exact (canonical35271 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2561 + difference 3 2) (sourceB2561 + difference 2 3) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2561 + difference 3 2) (sourceB2561 + difference 2 3) sourceC2561) = raw35272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35272; decide +kernel
    rw [ha]
    exact (canonical35272 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2561 + difference 3 4) (sourceB2561 + difference 4 3) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5466) := by
    have ha : (tripleCharges (sourceA2561 + difference 3 4) (sourceB2561 + difference 4 3) sourceC2561) = raw34885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw34885; decide +kernel
    rw [ha]
    exact (canonical34885 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2561 + difference 3 5) (sourceB2561 + difference 5 3) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2561 + difference 3 5) (sourceB2561 + difference 5 3) sourceC2561) = raw35274 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35274; decide +kernel
    rw [ha]
    exact (canonical35274 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2561 + difference 4 0) (sourceB2561 + difference 0 4) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2561 + difference 4 0) (sourceB2561 + difference 0 4) sourceC2561) = raw35391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35391; decide +kernel
    rw [ha]
    exact (canonical35391 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2561 + difference 4 1) (sourceB2561 + difference 1 4) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2561 + difference 4 1) (sourceB2561 + difference 1 4) sourceC2561) = raw35392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35392; decide +kernel
    rw [ha]
    exact (canonical35392 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2561 + difference 4 2) (sourceB2561 + difference 2 4) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5012) := by
    have ha : (tripleCharges (sourceA2561 + difference 4 2) (sourceB2561 + difference 2 4) sourceC2561) = raw35393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35393; decide +kernel
    rw [ha]
    exact (canonical35393 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2561 + difference 4 3) (sourceB2561 + difference 3 4) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5020) := by
    have ha : (tripleCharges (sourceA2561 + difference 4 3) (sourceB2561 + difference 3 4) sourceC2561) = raw35394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35394; decide +kernel
    rw [ha]
    exact (canonical35394 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2561 + difference 4 5) (sourceB2561 + difference 5 4) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA2561 + difference 4 5) (sourceB2561 + difference 5 4) sourceC2561) = raw35395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35395; decide +kernel
    rw [ha]
    exact (canonical35395 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2561 + difference 5 0) (sourceB2561 + difference 0 5) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5327) := by
    have ha : (tripleCharges (sourceA2561 + difference 5 0) (sourceB2561 + difference 0 5) sourceC2561) = raw35396 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35396; decide +kernel
    rw [ha]
    exact (canonical35396 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2561 + difference 5 1) (sourceB2561 + difference 1 5) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5327) := by
    have ha : (tripleCharges (sourceA2561 + difference 5 1) (sourceB2561 + difference 1 5) sourceC2561) = raw35397 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35397; decide +kernel
    rw [ha]
    exact (canonical35397 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2561 + difference 5 2) (sourceB2561 + difference 2 5) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5321) := by
    have ha : (tripleCharges (sourceA2561 + difference 5 2) (sourceB2561 + difference 2 5) sourceC2561) = raw35398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35398; decide +kernel
    rw [ha]
    exact (canonical35398 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2561 + difference 5 3) (sourceB2561 + difference 3 5) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5330) := by
    have ha : (tripleCharges (sourceA2561 + difference 5 3) (sourceB2561 + difference 3 5) sourceC2561) = raw35399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35399; decide +kernel
    rw [ha]
    exact (canonical35399 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2561 + difference 5 4) (sourceB2561 + difference 4 5) sourceC2561) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2561 + difference 5 4) (sourceB2561 + difference 4 5) sourceC2561) = raw35277 := by
      apply Matrix.ext; unfold tripleCharges sourceA2561 sourceB2561 sourceC2561 difference raw35277; decide +kernel
    rw [ha]
    exact (canonical35277 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2561 sourceB2561 sourceC2561
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2561, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2562 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2562 : Charge := ![1, 1, 0, -2, 0, 0]
def sourceC2562 : Charge := ![1, 1, 0, 2, -2, -2]
def sourceForm2562 : Integer.Sparse Master := [(Sum.inr 2314, 2), (Sum.inr 3639, 1), (Sum.inr 3661, 1), (Sum.inr 3665, 2), (Sum.inr 4088, -1)]

theorem sourceEq2562 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2562 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2562 + difference 0 3) (sourceB2562 + difference 3 0) sourceC2562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3665) := by
    have ha : (tripleCharges (sourceA2562 + difference 0 3) (sourceB2562 + difference 3 0) sourceC2562) = raw35400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2562 sourceB2562 sourceC2562 difference raw35400; decide +kernel
    rw [ha]
    exact (canonical35400 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2562 + difference 1 3) (sourceB2562 + difference 3 1) sourceC2562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3665) := by
    have ha : (tripleCharges (sourceA2562 + difference 1 3) (sourceB2562 + difference 3 1) sourceC2562) = raw29868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2562 sourceB2562 sourceC2562 difference raw29868; decide +kernel
    rw [ha]
    exact (canonical29868 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2562 + difference 2 3) (sourceB2562 + difference 3 2) sourceC2562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3639) := by
    have ha : (tripleCharges (sourceA2562 + difference 2 3) (sourceB2562 + difference 3 2) sourceC2562) = raw35401 := by
      apply Matrix.ext; unfold tripleCharges sourceA2562 sourceB2562 sourceC2562 difference raw35401; decide +kernel
    rw [ha]
    exact (canonical35401 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2562 + difference 3 3) (sourceB2562 + difference 3 3) sourceC2562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3661) := by
    have ha : (tripleCharges (sourceA2562 + difference 3 3) (sourceB2562 + difference 3 3) sourceC2562) = raw35402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2562 sourceB2562 sourceC2562 difference raw35402; decide +kernel
    rw [ha]
    exact (canonical35402 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2562 + difference 4 3) (sourceB2562 + difference 3 4) sourceC2562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2314) := by
    have ha : (tripleCharges (sourceA2562 + difference 4 3) (sourceB2562 + difference 3 4) sourceC2562) = raw35403 := by
      apply Matrix.ext; unfold tripleCharges sourceA2562 sourceB2562 sourceC2562 difference raw35403; decide +kernel
    rw [ha]
    exact (canonical35403 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2562 + difference 5 3) (sourceB2562 + difference 3 5) sourceC2562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2314) := by
    have ha : (tripleCharges (sourceA2562 + difference 5 3) (sourceB2562 + difference 3 5) sourceC2562) = raw35404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2562 sourceB2562 sourceC2562 difference raw35404; decide +kernel
    rw [ha]
    exact (canonical35404 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2562 + sourceB2562) sourceC2562) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2562 + sourceB2562) sourceC2562) = raw28174 := by
      apply Matrix.ext; unfold doubleCharges sourceA2562 sourceB2562 sourceC2562 raw28174; decide +kernel
    rw [ha]
    exact (canonical28174 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2562 sourceB2562 sourceC2562
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2562, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2563 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2563 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC2563 : Charge := ![1, 1, 1, 1, -2, -2]
def sourceForm2563 : Integer.Sparse Master := [(Sum.inr 2299, 2), (Sum.inr 3642, 1), (Sum.inr 3647, 1), (Sum.inr 3652, 2), (Sum.inr 4087, -1)]

theorem sourceEq2563 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2563 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2563 + difference 0 2) (sourceB2563 + difference 2 0) sourceC2563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3652) := by
    have ha : (tripleCharges (sourceA2563 + difference 0 2) (sourceB2563 + difference 2 0) sourceC2563) = raw35405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2563 sourceB2563 sourceC2563 difference raw35405; decide +kernel
    rw [ha]
    exact (canonical35405 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2563 + difference 1 2) (sourceB2563 + difference 2 1) sourceC2563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3652) := by
    have ha : (tripleCharges (sourceA2563 + difference 1 2) (sourceB2563 + difference 2 1) sourceC2563) = raw29885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2563 sourceB2563 sourceC2563 difference raw29885; decide +kernel
    rw [ha]
    exact (canonical29885 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2563 + difference 2 2) (sourceB2563 + difference 2 2) sourceC2563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3647) := by
    have ha : (tripleCharges (sourceA2563 + difference 2 2) (sourceB2563 + difference 2 2) sourceC2563) = raw29884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2563 sourceB2563 sourceC2563 difference raw29884; decide +kernel
    rw [ha]
    exact (canonical29884 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2563 + difference 3 2) (sourceB2563 + difference 2 3) sourceC2563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3642) := by
    have ha : (tripleCharges (sourceA2563 + difference 3 2) (sourceB2563 + difference 2 3) sourceC2563) = raw35406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2563 sourceB2563 sourceC2563 difference raw35406; decide +kernel
    rw [ha]
    exact (canonical35406 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2563 + difference 4 2) (sourceB2563 + difference 2 4) sourceC2563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2299) := by
    have ha : (tripleCharges (sourceA2563 + difference 4 2) (sourceB2563 + difference 2 4) sourceC2563) = raw35407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2563 sourceB2563 sourceC2563 difference raw35407; decide +kernel
    rw [ha]
    exact (canonical35407 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2563 + difference 5 2) (sourceB2563 + difference 2 5) sourceC2563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2299) := by
    have ha : (tripleCharges (sourceA2563 + difference 5 2) (sourceB2563 + difference 2 5) sourceC2563) = raw35408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2563 sourceB2563 sourceC2563 difference raw35408; decide +kernel
    rw [ha]
    exact (canonical35408 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2563 + sourceB2563) sourceC2563) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA2563 + sourceB2563) sourceC2563) = raw22391 := by
      apply Matrix.ext; unfold doubleCharges sourceA2563 sourceB2563 sourceC2563 raw22391; decide +kernel
    rw [ha]
    exact (canonical22391 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2563 sourceB2563 sourceC2563
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2563, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2564 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2564 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceC2564 : Charge := ![1, 2, -1, 1, -2, -1]
def sourceForm2564 : Integer.Sparse Master := [(Sum.inr 2318, 1), (Sum.inr 2796, 1), (Sum.inr 3667, 1), (Sum.inr 3678, 1), (Sum.inr 3682, 1), (Sum.inr 3683, 1), (Sum.inr 4090, -1)]

theorem sourceEq2564 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2564 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2564 + difference 2 0) (sourceB2564 + difference 0 2) sourceC2564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2796) := by
    have ha : (tripleCharges (sourceA2564 + difference 2 0) (sourceB2564 + difference 0 2) sourceC2564) = raw35409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2564 sourceB2564 sourceC2564 difference raw35409; decide +kernel
    rw [ha]
    exact (canonical35409 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2564 + difference 2 1) (sourceB2564 + difference 1 2) sourceC2564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2318) := by
    have ha : (tripleCharges (sourceA2564 + difference 2 1) (sourceB2564 + difference 1 2) sourceC2564) = raw35410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2564 sourceB2564 sourceC2564 difference raw35410; decide +kernel
    rw [ha]
    exact (canonical35410 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2564 + difference 2 2) (sourceB2564 + difference 2 2) sourceC2564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3678) := by
    have ha : (tripleCharges (sourceA2564 + difference 2 2) (sourceB2564 + difference 2 2) sourceC2564) = raw35411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2564 sourceB2564 sourceC2564 difference raw35411; decide +kernel
    rw [ha]
    exact (canonical35411 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2564 + difference 2 3) (sourceB2564 + difference 3 2) sourceC2564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3667) := by
    have ha : (tripleCharges (sourceA2564 + difference 2 3) (sourceB2564 + difference 3 2) sourceC2564) = raw35412 := by
      apply Matrix.ext; unfold tripleCharges sourceA2564 sourceB2564 sourceC2564 difference raw35412; decide +kernel
    rw [ha]
    exact (canonical35412 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2564 + difference 2 4) (sourceB2564 + difference 4 2) sourceC2564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3683) := by
    have ha : (tripleCharges (sourceA2564 + difference 2 4) (sourceB2564 + difference 4 2) sourceC2564) = raw35413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2564 sourceB2564 sourceC2564 difference raw35413; decide +kernel
    rw [ha]
    exact (canonical35413 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2564 + difference 2 5) (sourceB2564 + difference 5 2) sourceC2564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3682) := by
    have ha : (tripleCharges (sourceA2564 + difference 2 5) (sourceB2564 + difference 5 2) sourceC2564) = raw35414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2564 sourceB2564 sourceC2564 difference raw35414; decide +kernel
    rw [ha]
    exact (canonical35414 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2564 + sourceB2564) sourceC2564) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2564 + sourceB2564) sourceC2564) = raw35415 := by
      apply Matrix.ext; unfold doubleCharges sourceA2564 sourceB2564 sourceC2564 raw35415; decide +kernel
    rw [ha]
    exact (canonical35415 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2564 sourceB2564 sourceC2564
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2564, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2565 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2565 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC2565 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceForm2565 : Integer.Sparse Master := [(Sum.inr 4092, 1), (Sum.inr 4946, 4), (Sum.inr 4952, 1), (Sum.inr 4953, 2), (Sum.inr 4977, 4), (Sum.inr 4979, 1), (Sum.inr 5111, 2), (Sum.inr 5207, 2), (Sum.inr 5335, 2), (Sum.inr 5367, 4), (Sum.inr 5368, 4), (Sum.inr 5413, 2), (Sum.inr 5475, 1)]

theorem sourceEq2565 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2565 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2565 + difference 0 1) (sourceB2565 + difference 1 0) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2565 + difference 0 1) (sourceB2565 + difference 1 0) sourceC2565) = raw35416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35416; decide +kernel
    rw [ha]
    exact (canonical35416 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2565 + difference 0 2) (sourceB2565 + difference 2 0) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2565 + difference 0 2) (sourceB2565 + difference 2 0) sourceC2565) = raw35417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35417; decide +kernel
    rw [ha]
    exact (canonical35417 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2565 + difference 0 3) (sourceB2565 + difference 3 0) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2565 + difference 0 3) (sourceB2565 + difference 3 0) sourceC2565) = raw35418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35418; decide +kernel
    rw [ha]
    exact (canonical35418 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2565 + difference 0 4) (sourceB2565 + difference 4 0) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA2565 + difference 0 4) (sourceB2565 + difference 4 0) sourceC2565) = raw17978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw17978; decide +kernel
    rw [ha]
    exact (canonical17978 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2565 + difference 0 5) (sourceB2565 + difference 5 0) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2565 + difference 0 5) (sourceB2565 + difference 5 0) sourceC2565) = raw35419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35419; decide +kernel
    rw [ha]
    exact (canonical35419 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2565 + difference 1 0) (sourceB2565 + difference 0 1) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2565 + difference 1 0) (sourceB2565 + difference 0 1) sourceC2565) = raw17998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw17998; decide +kernel
    rw [ha]
    exact (canonical17998 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2565 + difference 1 2) (sourceB2565 + difference 2 1) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2565 + difference 1 2) (sourceB2565 + difference 2 1) sourceC2565) = raw18000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw18000; decide +kernel
    rw [ha]
    exact (canonical18000 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2565 + difference 1 3) (sourceB2565 + difference 3 1) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2565 + difference 1 3) (sourceB2565 + difference 3 1) sourceC2565) = raw18001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw18001; decide +kernel
    rw [ha]
    exact (canonical18001 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2565 + difference 1 4) (sourceB2565 + difference 4 1) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5475) := by
    have ha : (tripleCharges (sourceA2565 + difference 1 4) (sourceB2565 + difference 4 1) sourceC2565) = raw29979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw29979; decide +kernel
    rw [ha]
    exact (canonical29979 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2565 + difference 1 5) (sourceB2565 + difference 5 1) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA2565 + difference 1 5) (sourceB2565 + difference 5 1) sourceC2565) = raw18002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw18002; decide +kernel
    rw [ha]
    exact (canonical18002 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2565 + difference 2 0) (sourceB2565 + difference 0 2) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2565 + difference 2 0) (sourceB2565 + difference 0 2) sourceC2565) = raw29985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw29985; decide +kernel
    rw [ha]
    exact (canonical29985 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2565 + difference 2 1) (sourceB2565 + difference 1 2) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2565 + difference 2 1) (sourceB2565 + difference 1 2) sourceC2565) = raw35420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35420; decide +kernel
    rw [ha]
    exact (canonical35420 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2565 + difference 2 3) (sourceB2565 + difference 3 2) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2565 + difference 2 3) (sourceB2565 + difference 3 2) sourceC2565) = raw35421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35421; decide +kernel
    rw [ha]
    exact (canonical35421 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2565 + difference 2 4) (sourceB2565 + difference 4 2) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2565 + difference 2 4) (sourceB2565 + difference 4 2) sourceC2565) = raw17989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw17989; decide +kernel
    rw [ha]
    exact (canonical17989 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2565 + difference 2 5) (sourceB2565 + difference 5 2) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2565 + difference 2 5) (sourceB2565 + difference 5 2) sourceC2565) = raw35422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35422; decide +kernel
    rw [ha]
    exact (canonical35422 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2565 + difference 3 0) (sourceB2565 + difference 0 3) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2565 + difference 3 0) (sourceB2565 + difference 0 3) sourceC2565) = raw29989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw29989; decide +kernel
    rw [ha]
    exact (canonical29989 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2565 + difference 3 1) (sourceB2565 + difference 1 3) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2565 + difference 3 1) (sourceB2565 + difference 1 3) sourceC2565) = raw35423 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35423; decide +kernel
    rw [ha]
    exact (canonical35423 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2565 + difference 3 2) (sourceB2565 + difference 2 3) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2565 + difference 3 2) (sourceB2565 + difference 2 3) sourceC2565) = raw35424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35424; decide +kernel
    rw [ha]
    exact (canonical35424 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2565 + difference 3 4) (sourceB2565 + difference 4 3) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2565 + difference 3 4) (sourceB2565 + difference 4 3) sourceC2565) = raw17994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw17994; decide +kernel
    rw [ha]
    exact (canonical17994 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2565 + difference 3 5) (sourceB2565 + difference 5 3) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2565 + difference 3 5) (sourceB2565 + difference 5 3) sourceC2565) = raw35425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35425; decide +kernel
    rw [ha]
    exact (canonical35425 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2565 + difference 4 0) (sourceB2565 + difference 0 4) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4953) := by
    have ha : (tripleCharges (sourceA2565 + difference 4 0) (sourceB2565 + difference 0 4) sourceC2565) = raw29993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw29993; decide +kernel
    rw [ha]
    exact (canonical29993 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2565 + difference 4 1) (sourceB2565 + difference 1 4) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4952) := by
    have ha : (tripleCharges (sourceA2565 + difference 4 1) (sourceB2565 + difference 1 4) sourceC2565) = raw35426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35426; decide +kernel
    rw [ha]
    exact (canonical35426 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2565 + difference 4 2) (sourceB2565 + difference 2 4) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2565 + difference 4 2) (sourceB2565 + difference 2 4) sourceC2565) = raw35427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35427; decide +kernel
    rw [ha]
    exact (canonical35427 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2565 + difference 4 3) (sourceB2565 + difference 3 4) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2565 + difference 4 3) (sourceB2565 + difference 3 4) sourceC2565) = raw35428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35428; decide +kernel
    rw [ha]
    exact (canonical35428 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2565 + difference 4 5) (sourceB2565 + difference 5 4) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2565 + difference 4 5) (sourceB2565 + difference 5 4) sourceC2565) = raw35429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35429; decide +kernel
    rw [ha]
    exact (canonical35429 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2565 + difference 5 0) (sourceB2565 + difference 0 5) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4979) := by
    have ha : (tripleCharges (sourceA2565 + difference 5 0) (sourceB2565 + difference 0 5) sourceC2565) = raw29998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw29998; decide +kernel
    rw [ha]
    exact (canonical29998 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2565 + difference 5 1) (sourceB2565 + difference 1 5) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4953) := by
    have ha : (tripleCharges (sourceA2565 + difference 5 1) (sourceB2565 + difference 1 5) sourceC2565) = raw35430 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35430; decide +kernel
    rw [ha]
    exact (canonical35430 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2565 + difference 5 2) (sourceB2565 + difference 2 5) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2565 + difference 5 2) (sourceB2565 + difference 2 5) sourceC2565) = raw35431 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35431; decide +kernel
    rw [ha]
    exact (canonical35431 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2565 + difference 5 3) (sourceB2565 + difference 3 5) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2565 + difference 5 3) (sourceB2565 + difference 3 5) sourceC2565) = raw35432 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35432; decide +kernel
    rw [ha]
    exact (canonical35432 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2565 + difference 5 4) (sourceB2565 + difference 4 5) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2565 + difference 5 4) (sourceB2565 + difference 4 5) sourceC2565) = raw18004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw18004; decide +kernel
    rw [ha]
    exact (canonical18004 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2565 sourceB2565 sourceC2565
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2565, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2566 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2566 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC2566 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceForm2566 : Integer.Sparse Master := [(Sum.inr 3412, 4), (Sum.inr 3422, 1), (Sum.inr 3423, 2), (Sum.inr 3485, 2), (Sum.inr 3595, 4), (Sum.inr 3596, 1), (Sum.inr 3631, 2), (Sum.inr 3753, 2), (Sum.inr 3766, 4), (Sum.inr 3767, 4), (Sum.inr 3817, 2), (Sum.inr 3963, 1), (Sum.inr 4092, 1)]

theorem sourceEq2566 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2566 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2566 + difference 0 1) (sourceB2566 + difference 1 0) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA2566 + difference 0 1) (sourceB2566 + difference 1 0) sourceC2566) = raw35433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35433; decide +kernel
    rw [ha]
    exact (canonical35433 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2566 + difference 0 2) (sourceB2566 + difference 2 0) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2566 + difference 0 2) (sourceB2566 + difference 2 0) sourceC2566) = raw35434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35434; decide +kernel
    rw [ha]
    exact (canonical35434 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2566 + difference 0 3) (sourceB2566 + difference 3 0) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2566 + difference 0 3) (sourceB2566 + difference 3 0) sourceC2566) = raw35435 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35435; decide +kernel
    rw [ha]
    exact (canonical35435 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2566 + difference 0 4) (sourceB2566 + difference 4 0) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA2566 + difference 0 4) (sourceB2566 + difference 4 0) sourceC2566) = raw18008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18008; decide +kernel
    rw [ha]
    exact (canonical18008 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2566 + difference 0 5) (sourceB2566 + difference 5 0) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2566 + difference 0 5) (sourceB2566 + difference 5 0) sourceC2566) = raw35436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35436; decide +kernel
    rw [ha]
    exact (canonical35436 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2566 + difference 1 0) (sourceB2566 + difference 0 1) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA2566 + difference 1 0) (sourceB2566 + difference 0 1) sourceC2566) = raw18028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18028; decide +kernel
    rw [ha]
    exact (canonical18028 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2566 + difference 1 2) (sourceB2566 + difference 2 1) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2566 + difference 1 2) (sourceB2566 + difference 2 1) sourceC2566) = raw18030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18030; decide +kernel
    rw [ha]
    exact (canonical18030 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2566 + difference 1 3) (sourceB2566 + difference 3 1) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2566 + difference 1 3) (sourceB2566 + difference 3 1) sourceC2566) = raw18031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18031; decide +kernel
    rw [ha]
    exact (canonical18031 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2566 + difference 1 4) (sourceB2566 + difference 4 1) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA2566 + difference 1 4) (sourceB2566 + difference 4 1) sourceC2566) = raw30001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw30001; decide +kernel
    rw [ha]
    exact (canonical30001 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2566 + difference 1 5) (sourceB2566 + difference 5 1) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA2566 + difference 1 5) (sourceB2566 + difference 5 1) sourceC2566) = raw18032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18032; decide +kernel
    rw [ha]
    exact (canonical18032 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2566 + difference 2 0) (sourceB2566 + difference 0 2) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2566 + difference 2 0) (sourceB2566 + difference 0 2) sourceC2566) = raw30007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw30007; decide +kernel
    rw [ha]
    exact (canonical30007 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2566 + difference 2 1) (sourceB2566 + difference 1 2) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2566 + difference 2 1) (sourceB2566 + difference 1 2) sourceC2566) = raw35437 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35437; decide +kernel
    rw [ha]
    exact (canonical35437 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2566 + difference 2 3) (sourceB2566 + difference 3 2) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3753) := by
    have ha : (tripleCharges (sourceA2566 + difference 2 3) (sourceB2566 + difference 3 2) sourceC2566) = raw35438 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35438; decide +kernel
    rw [ha]
    exact (canonical35438 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2566 + difference 2 4) (sourceB2566 + difference 4 2) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2566 + difference 2 4) (sourceB2566 + difference 4 2) sourceC2566) = raw18019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18019; decide +kernel
    rw [ha]
    exact (canonical18019 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2566 + difference 2 5) (sourceB2566 + difference 5 2) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2566 + difference 2 5) (sourceB2566 + difference 5 2) sourceC2566) = raw35439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35439; decide +kernel
    rw [ha]
    exact (canonical35439 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2566 + difference 3 0) (sourceB2566 + difference 0 3) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2566 + difference 3 0) (sourceB2566 + difference 0 3) sourceC2566) = raw30011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw30011; decide +kernel
    rw [ha]
    exact (canonical30011 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2566 + difference 3 1) (sourceB2566 + difference 1 3) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2566 + difference 3 1) (sourceB2566 + difference 1 3) sourceC2566) = raw35440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35440; decide +kernel
    rw [ha]
    exact (canonical35440 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2566 + difference 3 2) (sourceB2566 + difference 2 3) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3753) := by
    have ha : (tripleCharges (sourceA2566 + difference 3 2) (sourceB2566 + difference 2 3) sourceC2566) = raw35441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35441; decide +kernel
    rw [ha]
    exact (canonical35441 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2566 + difference 3 4) (sourceB2566 + difference 4 3) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2566 + difference 3 4) (sourceB2566 + difference 4 3) sourceC2566) = raw18024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18024; decide +kernel
    rw [ha]
    exact (canonical18024 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2566 + difference 3 5) (sourceB2566 + difference 5 3) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2566 + difference 3 5) (sourceB2566 + difference 5 3) sourceC2566) = raw35442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35442; decide +kernel
    rw [ha]
    exact (canonical35442 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2566 + difference 4 0) (sourceB2566 + difference 0 4) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2566 + difference 4 0) (sourceB2566 + difference 0 4) sourceC2566) = raw30015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw30015; decide +kernel
    rw [ha]
    exact (canonical30015 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2566 + difference 4 1) (sourceB2566 + difference 1 4) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3422) := by
    have ha : (tripleCharges (sourceA2566 + difference 4 1) (sourceB2566 + difference 1 4) sourceC2566) = raw35443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35443; decide +kernel
    rw [ha]
    exact (canonical35443 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2566 + difference 4 2) (sourceB2566 + difference 2 4) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2566 + difference 4 2) (sourceB2566 + difference 2 4) sourceC2566) = raw35444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35444; decide +kernel
    rw [ha]
    exact (canonical35444 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2566 + difference 4 3) (sourceB2566 + difference 3 4) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2566 + difference 4 3) (sourceB2566 + difference 3 4) sourceC2566) = raw35445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35445; decide +kernel
    rw [ha]
    exact (canonical35445 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2566 + difference 4 5) (sourceB2566 + difference 5 4) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA2566 + difference 4 5) (sourceB2566 + difference 5 4) sourceC2566) = raw35446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35446; decide +kernel
    rw [ha]
    exact (canonical35446 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2566 + difference 5 0) (sourceB2566 + difference 0 5) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3596) := by
    have ha : (tripleCharges (sourceA2566 + difference 5 0) (sourceB2566 + difference 0 5) sourceC2566) = raw30020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw30020; decide +kernel
    rw [ha]
    exact (canonical30020 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2566 + difference 5 1) (sourceB2566 + difference 1 5) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2566 + difference 5 1) (sourceB2566 + difference 1 5) sourceC2566) = raw35447 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35447; decide +kernel
    rw [ha]
    exact (canonical35447 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2566 + difference 5 2) (sourceB2566 + difference 2 5) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2566 + difference 5 2) (sourceB2566 + difference 2 5) sourceC2566) = raw35448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35448; decide +kernel
    rw [ha]
    exact (canonical35448 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2566 + difference 5 3) (sourceB2566 + difference 3 5) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2566 + difference 5 3) (sourceB2566 + difference 3 5) sourceC2566) = raw35449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw35449; decide +kernel
    rw [ha]
    exact (canonical35449 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2566 + difference 5 4) (sourceB2566 + difference 4 5) sourceC2566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA2566 + difference 5 4) (sourceB2566 + difference 4 5) sourceC2566) = raw18034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2566 sourceB2566 sourceC2566 difference raw18034; decide +kernel
    rw [ha]
    exact (canonical18034 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2566 sourceB2566 sourceC2566
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2566, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2567 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2567 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC2567 : Charge := ![1, 2, 0, 1, -2, -2]
def sourceForm2567 : Integer.Sparse Master := [(Sum.inr 4088, 1), (Sum.inr 4903, 2), (Sum.inr 4907, 2), (Sum.inr 4908, 2), (Sum.inr 4921, 2), (Sum.inr 4926, 1), (Sum.inr 4937, 1), (Sum.inr 4962, 1), (Sum.inr 4978, 1), (Sum.inr 5003, 2), (Sum.inr 5063, 1), (Sum.inr 5193, 1), (Sum.inr 5314, 1), (Sum.inr 5317, 1), (Sum.inr 5323, 1), (Sum.inr 5324, 1), (Sum.inr 5331, 1), (Sum.inr 5344, 2), (Sum.inr 5364, 2), (Sum.inr 5367, 2), (Sum.inr 5368, 2)]

theorem sourceEq2567 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2567 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2567 + difference 0 1) (sourceB2567 + difference 1 0) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5063) := by
    have ha : (tripleCharges (sourceA2567 + difference 0 1) (sourceB2567 + difference 1 0) sourceC2567) = raw35450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35450; decide +kernel
    rw [ha]
    exact (canonical35450 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2567 + difference 0 2) (sourceB2567 + difference 2 0) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5323) := by
    have ha : (tripleCharges (sourceA2567 + difference 0 2) (sourceB2567 + difference 2 0) sourceC2567) = raw35451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35451; decide +kernel
    rw [ha]
    exact (canonical35451 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2567 + difference 0 3) (sourceB2567 + difference 3 0) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2567 + difference 0 3) (sourceB2567 + difference 3 0) sourceC2567) = raw35452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35452; decide +kernel
    rw [ha]
    exact (canonical35452 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2567 + difference 0 4) (sourceB2567 + difference 4 0) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2567 + difference 0 4) (sourceB2567 + difference 4 0) sourceC2567) = raw35453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35453; decide +kernel
    rw [ha]
    exact (canonical35453 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2567 + difference 0 5) (sourceB2567 + difference 5 0) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2567 + difference 0 5) (sourceB2567 + difference 5 0) sourceC2567) = raw35454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35454; decide +kernel
    rw [ha]
    exact (canonical35454 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2567 + difference 1 0) (sourceB2567 + difference 0 1) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5193) := by
    have ha : (tripleCharges (sourceA2567 + difference 1 0) (sourceB2567 + difference 0 1) sourceC2567) = raw35455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35455; decide +kernel
    rw [ha]
    exact (canonical35455 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2567 + difference 1 2) (sourceB2567 + difference 2 1) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5324) := by
    have ha : (tripleCharges (sourceA2567 + difference 1 2) (sourceB2567 + difference 2 1) sourceC2567) = raw35456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35456; decide +kernel
    rw [ha]
    exact (canonical35456 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2567 + difference 1 3) (sourceB2567 + difference 3 1) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5331) := by
    have ha : (tripleCharges (sourceA2567 + difference 1 3) (sourceB2567 + difference 3 1) sourceC2567) = raw35457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35457; decide +kernel
    rw [ha]
    exact (canonical35457 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2567 + difference 1 4) (sourceB2567 + difference 4 1) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2567 + difference 1 4) (sourceB2567 + difference 4 1) sourceC2567) = raw35458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35458; decide +kernel
    rw [ha]
    exact (canonical35458 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2567 + difference 1 5) (sourceB2567 + difference 5 1) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2567 + difference 1 5) (sourceB2567 + difference 5 1) sourceC2567) = raw35459 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35459; decide +kernel
    rw [ha]
    exact (canonical35459 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2567 + difference 2 0) (sourceB2567 + difference 0 2) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4962) := by
    have ha : (tripleCharges (sourceA2567 + difference 2 0) (sourceB2567 + difference 0 2) sourceC2567) = raw35460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35460; decide +kernel
    rw [ha]
    exact (canonical35460 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2567 + difference 2 1) (sourceB2567 + difference 1 2) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4926) := by
    have ha : (tripleCharges (sourceA2567 + difference 2 1) (sourceB2567 + difference 1 2) sourceC2567) = raw35461 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35461; decide +kernel
    rw [ha]
    exact (canonical35461 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2567 + difference 2 3) (sourceB2567 + difference 3 2) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5314) := by
    have ha : (tripleCharges (sourceA2567 + difference 2 3) (sourceB2567 + difference 3 2) sourceC2567) = raw35462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35462; decide +kernel
    rw [ha]
    exact (canonical35462 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2567 + difference 2 4) (sourceB2567 + difference 4 2) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA2567 + difference 2 4) (sourceB2567 + difference 4 2) sourceC2567) = raw35463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35463; decide +kernel
    rw [ha]
    exact (canonical35463 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2567 + difference 2 5) (sourceB2567 + difference 5 2) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA2567 + difference 2 5) (sourceB2567 + difference 5 2) sourceC2567) = raw35464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35464; decide +kernel
    rw [ha]
    exact (canonical35464 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2567 + difference 3 0) (sourceB2567 + difference 0 3) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4978) := by
    have ha : (tripleCharges (sourceA2567 + difference 3 0) (sourceB2567 + difference 0 3) sourceC2567) = raw35465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35465; decide +kernel
    rw [ha]
    exact (canonical35465 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2567 + difference 3 1) (sourceB2567 + difference 1 3) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4937) := by
    have ha : (tripleCharges (sourceA2567 + difference 3 1) (sourceB2567 + difference 1 3) sourceC2567) = raw35466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35466; decide +kernel
    rw [ha]
    exact (canonical35466 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2567 + difference 3 2) (sourceB2567 + difference 2 3) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5317) := by
    have ha : (tripleCharges (sourceA2567 + difference 3 2) (sourceB2567 + difference 2 3) sourceC2567) = raw35467 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35467; decide +kernel
    rw [ha]
    exact (canonical35467 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2567 + difference 3 4) (sourceB2567 + difference 4 3) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5364) := by
    have ha : (tripleCharges (sourceA2567 + difference 3 4) (sourceB2567 + difference 4 3) sourceC2567) = raw35468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35468; decide +kernel
    rw [ha]
    exact (canonical35468 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2567 + difference 3 5) (sourceB2567 + difference 5 3) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5364) := by
    have ha : (tripleCharges (sourceA2567 + difference 3 5) (sourceB2567 + difference 5 3) sourceC2567) = raw35469 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35469; decide +kernel
    rw [ha]
    exact (canonical35469 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2567 + difference 4 0) (sourceB2567 + difference 0 4) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4908) := by
    have ha : (tripleCharges (sourceA2567 + difference 4 0) (sourceB2567 + difference 0 4) sourceC2567) = raw35470 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35470; decide +kernel
    rw [ha]
    exact (canonical35470 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2567 + difference 4 1) (sourceB2567 + difference 1 4) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4907) := by
    have ha : (tripleCharges (sourceA2567 + difference 4 1) (sourceB2567 + difference 1 4) sourceC2567) = raw35471 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35471; decide +kernel
    rw [ha]
    exact (canonical35471 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2567 + difference 4 2) (sourceB2567 + difference 2 4) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4903) := by
    have ha : (tripleCharges (sourceA2567 + difference 4 2) (sourceB2567 + difference 2 4) sourceC2567) = raw35472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35472; decide +kernel
    rw [ha]
    exact (canonical35472 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2567 + difference 4 3) (sourceB2567 + difference 3 4) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4921) := by
    have ha : (tripleCharges (sourceA2567 + difference 4 3) (sourceB2567 + difference 3 4) sourceC2567) = raw35473 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35473; decide +kernel
    rw [ha]
    exact (canonical35473 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2567 + difference 4 5) (sourceB2567 + difference 5 4) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2567 + difference 4 5) (sourceB2567 + difference 5 4) sourceC2567) = raw35474 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35474; decide +kernel
    rw [ha]
    exact (canonical35474 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2567 + difference 5 0) (sourceB2567 + difference 0 5) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4908) := by
    have ha : (tripleCharges (sourceA2567 + difference 5 0) (sourceB2567 + difference 0 5) sourceC2567) = raw35475 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35475; decide +kernel
    rw [ha]
    exact (canonical35475 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2567 + difference 5 1) (sourceB2567 + difference 1 5) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4907) := by
    have ha : (tripleCharges (sourceA2567 + difference 5 1) (sourceB2567 + difference 1 5) sourceC2567) = raw35476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35476; decide +kernel
    rw [ha]
    exact (canonical35476 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2567 + difference 5 2) (sourceB2567 + difference 2 5) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4903) := by
    have ha : (tripleCharges (sourceA2567 + difference 5 2) (sourceB2567 + difference 2 5) sourceC2567) = raw35477 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35477; decide +kernel
    rw [ha]
    exact (canonical35477 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2567 + difference 5 3) (sourceB2567 + difference 3 5) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4921) := by
    have ha : (tripleCharges (sourceA2567 + difference 5 3) (sourceB2567 + difference 3 5) sourceC2567) = raw35478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35478; decide +kernel
    rw [ha]
    exact (canonical35478 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2567 + difference 5 4) (sourceB2567 + difference 4 5) sourceC2567) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2567 + difference 5 4) (sourceB2567 + difference 4 5) sourceC2567) = raw35479 := by
      apply Matrix.ext; unfold tripleCharges sourceA2567 sourceB2567 sourceC2567 difference raw35479; decide +kernel
    rw [ha]
    exact (canonical35479 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2567 sourceB2567 sourceC2567
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2567, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2568 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2568 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC2568 : Charge := ![1, 2, 0, 1, -2, -2]
def sourceForm2568 : Integer.Sparse Master := [(Sum.inr 3316, 2), (Sum.inr 3325, 2), (Sum.inr 3326, 2), (Sum.inr 3328, 2), (Sum.inr 3354, 2), (Sum.inr 3398, 1), (Sum.inr 3402, 1), (Sum.inr 3439, 1), (Sum.inr 3593, 1), (Sum.inr 3594, 1), (Sum.inr 3630, 1), (Sum.inr 3644, 1), (Sum.inr 3649, 1), (Sum.inr 3650, 1), (Sum.inr 3651, 1), (Sum.inr 3665, 1), (Sum.inr 3681, 2), (Sum.inr 3702, 2), (Sum.inr 3704, 2), (Sum.inr 3705, 2), (Sum.inr 4088, 1)]

theorem sourceEq2568 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2568 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2568 + difference 0 1) (sourceB2568 + difference 1 0) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3439) := by
    have ha : (tripleCharges (sourceA2568 + difference 0 1) (sourceB2568 + difference 1 0) sourceC2568) = raw35480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35480; decide +kernel
    rw [ha]
    exact (canonical35480 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2568 + difference 0 2) (sourceB2568 + difference 2 0) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3650) := by
    have ha : (tripleCharges (sourceA2568 + difference 0 2) (sourceB2568 + difference 2 0) sourceC2568) = raw35481 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35481; decide +kernel
    rw [ha]
    exact (canonical35481 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2568 + difference 0 3) (sourceB2568 + difference 3 0) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2568 + difference 0 3) (sourceB2568 + difference 3 0) sourceC2568) = raw35482 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35482; decide +kernel
    rw [ha]
    exact (canonical35482 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2568 + difference 0 4) (sourceB2568 + difference 4 0) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3704) := by
    have ha : (tripleCharges (sourceA2568 + difference 0 4) (sourceB2568 + difference 4 0) sourceC2568) = raw35483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35483; decide +kernel
    rw [ha]
    exact (canonical35483 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2568 + difference 0 5) (sourceB2568 + difference 5 0) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3704) := by
    have ha : (tripleCharges (sourceA2568 + difference 0 5) (sourceB2568 + difference 5 0) sourceC2568) = raw35484 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35484; decide +kernel
    rw [ha]
    exact (canonical35484 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2568 + difference 1 0) (sourceB2568 + difference 0 1) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3630) := by
    have ha : (tripleCharges (sourceA2568 + difference 1 0) (sourceB2568 + difference 0 1) sourceC2568) = raw35485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35485; decide +kernel
    rw [ha]
    exact (canonical35485 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2568 + difference 1 2) (sourceB2568 + difference 2 1) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3651) := by
    have ha : (tripleCharges (sourceA2568 + difference 1 2) (sourceB2568 + difference 2 1) sourceC2568) = raw35486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35486; decide +kernel
    rw [ha]
    exact (canonical35486 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2568 + difference 1 3) (sourceB2568 + difference 3 1) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3665) := by
    have ha : (tripleCharges (sourceA2568 + difference 1 3) (sourceB2568 + difference 3 1) sourceC2568) = raw35487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35487; decide +kernel
    rw [ha]
    exact (canonical35487 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2568 + difference 1 4) (sourceB2568 + difference 4 1) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3705) := by
    have ha : (tripleCharges (sourceA2568 + difference 1 4) (sourceB2568 + difference 4 1) sourceC2568) = raw35488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35488; decide +kernel
    rw [ha]
    exact (canonical35488 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2568 + difference 1 5) (sourceB2568 + difference 5 1) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3705) := by
    have ha : (tripleCharges (sourceA2568 + difference 1 5) (sourceB2568 + difference 5 1) sourceC2568) = raw35489 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35489; decide +kernel
    rw [ha]
    exact (canonical35489 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2568 + difference 2 0) (sourceB2568 + difference 0 2) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3593) := by
    have ha : (tripleCharges (sourceA2568 + difference 2 0) (sourceB2568 + difference 0 2) sourceC2568) = raw35490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35490; decide +kernel
    rw [ha]
    exact (canonical35490 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2568 + difference 2 1) (sourceB2568 + difference 1 2) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3398) := by
    have ha : (tripleCharges (sourceA2568 + difference 2 1) (sourceB2568 + difference 1 2) sourceC2568) = raw35491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35491; decide +kernel
    rw [ha]
    exact (canonical35491 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2568 + difference 2 3) (sourceB2568 + difference 3 2) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3644) := by
    have ha : (tripleCharges (sourceA2568 + difference 2 3) (sourceB2568 + difference 3 2) sourceC2568) = raw35492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35492; decide +kernel
    rw [ha]
    exact (canonical35492 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2568 + difference 2 4) (sourceB2568 + difference 4 2) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3681) := by
    have ha : (tripleCharges (sourceA2568 + difference 2 4) (sourceB2568 + difference 4 2) sourceC2568) = raw35493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35493; decide +kernel
    rw [ha]
    exact (canonical35493 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2568 + difference 2 5) (sourceB2568 + difference 5 2) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3681) := by
    have ha : (tripleCharges (sourceA2568 + difference 2 5) (sourceB2568 + difference 5 2) sourceC2568) = raw35494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35494; decide +kernel
    rw [ha]
    exact (canonical35494 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2568 + difference 3 0) (sourceB2568 + difference 0 3) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3594) := by
    have ha : (tripleCharges (sourceA2568 + difference 3 0) (sourceB2568 + difference 0 3) sourceC2568) = raw35495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35495; decide +kernel
    rw [ha]
    exact (canonical35495 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2568 + difference 3 1) (sourceB2568 + difference 1 3) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3402) := by
    have ha : (tripleCharges (sourceA2568 + difference 3 1) (sourceB2568 + difference 1 3) sourceC2568) = raw35496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35496; decide +kernel
    rw [ha]
    exact (canonical35496 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2568 + difference 3 2) (sourceB2568 + difference 2 3) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3649) := by
    have ha : (tripleCharges (sourceA2568 + difference 3 2) (sourceB2568 + difference 2 3) sourceC2568) = raw35497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35497; decide +kernel
    rw [ha]
    exact (canonical35497 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2568 + difference 3 4) (sourceB2568 + difference 4 3) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3702) := by
    have ha : (tripleCharges (sourceA2568 + difference 3 4) (sourceB2568 + difference 4 3) sourceC2568) = raw35498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35498; decide +kernel
    rw [ha]
    exact (canonical35498 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2568 + difference 3 5) (sourceB2568 + difference 5 3) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3702) := by
    have ha : (tripleCharges (sourceA2568 + difference 3 5) (sourceB2568 + difference 5 3) sourceC2568) = raw35499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35499; decide +kernel
    rw [ha]
    exact (canonical35499 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2568 + difference 4 0) (sourceB2568 + difference 0 4) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3326) := by
    have ha : (tripleCharges (sourceA2568 + difference 4 0) (sourceB2568 + difference 0 4) sourceC2568) = raw35500 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35500; decide +kernel
    rw [ha]
    exact (canonical35500 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2568 + difference 4 1) (sourceB2568 + difference 1 4) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3325) := by
    have ha : (tripleCharges (sourceA2568 + difference 4 1) (sourceB2568 + difference 1 4) sourceC2568) = raw35501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35501; decide +kernel
    rw [ha]
    exact (canonical35501 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2568 + difference 4 2) (sourceB2568 + difference 2 4) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3316) := by
    have ha : (tripleCharges (sourceA2568 + difference 4 2) (sourceB2568 + difference 2 4) sourceC2568) = raw35502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35502; decide +kernel
    rw [ha]
    exact (canonical35502 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2568 + difference 4 3) (sourceB2568 + difference 3 4) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3328) := by
    have ha : (tripleCharges (sourceA2568 + difference 4 3) (sourceB2568 + difference 3 4) sourceC2568) = raw35503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35503; decide +kernel
    rw [ha]
    exact (canonical35503 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2568 + difference 4 5) (sourceB2568 + difference 5 4) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3354) := by
    have ha : (tripleCharges (sourceA2568 + difference 4 5) (sourceB2568 + difference 5 4) sourceC2568) = raw35504 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35504; decide +kernel
    rw [ha]
    exact (canonical35504 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2568 + difference 5 0) (sourceB2568 + difference 0 5) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3326) := by
    have ha : (tripleCharges (sourceA2568 + difference 5 0) (sourceB2568 + difference 0 5) sourceC2568) = raw35505 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35505; decide +kernel
    rw [ha]
    exact (canonical35505 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2568 + difference 5 1) (sourceB2568 + difference 1 5) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3325) := by
    have ha : (tripleCharges (sourceA2568 + difference 5 1) (sourceB2568 + difference 1 5) sourceC2568) = raw35506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35506; decide +kernel
    rw [ha]
    exact (canonical35506 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2568 + difference 5 2) (sourceB2568 + difference 2 5) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3316) := by
    have ha : (tripleCharges (sourceA2568 + difference 5 2) (sourceB2568 + difference 2 5) sourceC2568) = raw35507 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35507; decide +kernel
    rw [ha]
    exact (canonical35507 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2568 + difference 5 3) (sourceB2568 + difference 3 5) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3328) := by
    have ha : (tripleCharges (sourceA2568 + difference 5 3) (sourceB2568 + difference 3 5) sourceC2568) = raw35508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35508; decide +kernel
    rw [ha]
    exact (canonical35508 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2568 + difference 5 4) (sourceB2568 + difference 4 5) sourceC2568) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3354) := by
    have ha : (tripleCharges (sourceA2568 + difference 5 4) (sourceB2568 + difference 4 5) sourceC2568) = raw35509 := by
      apply Matrix.ext; unfold tripleCharges sourceA2568 sourceB2568 sourceC2568 difference raw35509; decide +kernel
    rw [ha]
    exact (canonical35509 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2568 sourceB2568 sourceC2568
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2568, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2569 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2569 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC2569 : Charge := ![1, 2, 0, 1, -2, -2]
def sourceForm2569 : Integer.Sparse Master := [(Sum.inr 2316, 1), (Sum.inr 2795, 1), (Sum.inr 3637, 1), (Sum.inr 3654, 1), (Sum.inr 3681, 2), (Sum.inr 4088, -1)]

theorem sourceEq2569 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2569 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2569 + difference 2 0) (sourceB2569 + difference 0 2) sourceC2569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2795) := by
    have ha : (tripleCharges (sourceA2569 + difference 2 0) (sourceB2569 + difference 0 2) sourceC2569) = raw30043 := by
      apply Matrix.ext; unfold tripleCharges sourceA2569 sourceB2569 sourceC2569 difference raw30043; decide +kernel
    rw [ha]
    exact (canonical30043 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2569 + difference 2 1) (sourceB2569 + difference 1 2) sourceC2569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2316) := by
    have ha : (tripleCharges (sourceA2569 + difference 2 1) (sourceB2569 + difference 1 2) sourceC2569) = raw35510 := by
      apply Matrix.ext; unfold tripleCharges sourceA2569 sourceB2569 sourceC2569 difference raw35510; decide +kernel
    rw [ha]
    exact (canonical35510 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2569 + difference 2 2) (sourceB2569 + difference 2 2) sourceC2569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3654) := by
    have ha : (tripleCharges (sourceA2569 + difference 2 2) (sourceB2569 + difference 2 2) sourceC2569) = raw30041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2569 sourceB2569 sourceC2569 difference raw30041; decide +kernel
    rw [ha]
    exact (canonical30041 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2569 + difference 2 3) (sourceB2569 + difference 3 2) sourceC2569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3637) := by
    have ha : (tripleCharges (sourceA2569 + difference 2 3) (sourceB2569 + difference 3 2) sourceC2569) = raw35511 := by
      apply Matrix.ext; unfold tripleCharges sourceA2569 sourceB2569 sourceC2569 difference raw35511; decide +kernel
    rw [ha]
    exact (canonical35511 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2569 + difference 2 4) (sourceB2569 + difference 4 2) sourceC2569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3681) := by
    have ha : (tripleCharges (sourceA2569 + difference 2 4) (sourceB2569 + difference 4 2) sourceC2569) = raw35512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2569 sourceB2569 sourceC2569 difference raw35512; decide +kernel
    rw [ha]
    exact (canonical35512 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2569 + difference 2 5) (sourceB2569 + difference 5 2) sourceC2569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3681) := by
    have ha : (tripleCharges (sourceA2569 + difference 2 5) (sourceB2569 + difference 5 2) sourceC2569) = raw35513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2569 sourceB2569 sourceC2569 difference raw35513; decide +kernel
    rw [ha]
    exact (canonical35513 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2569 + sourceB2569) sourceC2569) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2569 + sourceB2569) sourceC2569) = raw30047 := by
      apply Matrix.ext; unfold doubleCharges sourceA2569 sourceB2569 sourceC2569 raw30047; decide +kernel
    rw [ha]
    exact (canonical30047 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2569 sourceB2569 sourceC2569
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2569, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2570 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceB2570 : Charge := ![1, 2, 0, 1, -2, -2]
def sourceC2570 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceForm2570 : Integer.Sparse Master := [(Sum.inr 4089, 1), (Sum.inr 4910, 2), (Sum.inr 4913, 2), (Sum.inr 4915, 2), (Sum.inr 4922, 2), (Sum.inr 4985, 1), (Sum.inr 5015, 2), (Sum.inr 5024, 1), (Sum.inr 5125, 1), (Sum.inr 5313, 1), (Sum.inr 5315, 1), (Sum.inr 5320, 1), (Sum.inr 5321, 1), (Sum.inr 5327, 2), (Sum.inr 5329, 1), (Sum.inr 5330, 1), (Sum.inr 5341, 2), (Sum.inr 5355, 2), (Sum.inr 5356, 2), (Sum.inr 5371, 2)]

theorem sourceEq2570 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2570 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2570 + difference 0 1) (sourceB2570 + difference 1 0) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5125) := by
    have ha : (tripleCharges (sourceA2570 + difference 0 1) (sourceB2570 + difference 1 0) sourceC2570) = raw35514 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35514; decide +kernel
    rw [ha]
    exact (canonical35514 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2570 + difference 0 2) (sourceB2570 + difference 2 0) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5320) := by
    have ha : (tripleCharges (sourceA2570 + difference 0 2) (sourceB2570 + difference 2 0) sourceC2570) = raw35515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35515; decide +kernel
    rw [ha]
    exact (canonical35515 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2570 + difference 0 3) (sourceB2570 + difference 3 0) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5329) := by
    have ha : (tripleCharges (sourceA2570 + difference 0 3) (sourceB2570 + difference 3 0) sourceC2570) = raw35516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35516; decide +kernel
    rw [ha]
    exact (canonical35516 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2570 + difference 0 4) (sourceB2570 + difference 4 0) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2570 + difference 0 4) (sourceB2570 + difference 4 0) sourceC2570) = raw35517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35517; decide +kernel
    rw [ha]
    exact (canonical35517 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2570 + difference 0 5) (sourceB2570 + difference 5 0) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2570 + difference 0 5) (sourceB2570 + difference 5 0) sourceC2570) = raw35380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35380; decide +kernel
    rw [ha]
    exact (canonical35380 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2570 + difference 1 0) (sourceB2570 + difference 0 1) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5327) := by
    have ha : (tripleCharges (sourceA2570 + difference 1 0) (sourceB2570 + difference 0 1) sourceC2570) = raw35396 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35396; decide +kernel
    rw [ha]
    exact (canonical35396 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2570 + difference 1 2) (sourceB2570 + difference 2 1) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5321) := by
    have ha : (tripleCharges (sourceA2570 + difference 1 2) (sourceB2570 + difference 2 1) sourceC2570) = raw35398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35398; decide +kernel
    rw [ha]
    exact (canonical35398 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2570 + difference 1 3) (sourceB2570 + difference 3 1) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5330) := by
    have ha : (tripleCharges (sourceA2570 + difference 1 3) (sourceB2570 + difference 3 1) sourceC2570) = raw35399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35399; decide +kernel
    rw [ha]
    exact (canonical35399 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2570 + difference 1 4) (sourceB2570 + difference 4 1) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2570 + difference 1 4) (sourceB2570 + difference 4 1) sourceC2570) = raw35277 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35277; decide +kernel
    rw [ha]
    exact (canonical35277 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2570 + difference 1 5) (sourceB2570 + difference 5 1) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2570 + difference 1 5) (sourceB2570 + difference 5 1) sourceC2570) = raw35273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35273; decide +kernel
    rw [ha]
    exact (canonical35273 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2570 + difference 2 0) (sourceB2570 + difference 0 2) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5313) := by
    have ha : (tripleCharges (sourceA2570 + difference 2 0) (sourceB2570 + difference 0 2) sourceC2570) = raw35518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35518; decide +kernel
    rw [ha]
    exact (canonical35518 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2570 + difference 2 1) (sourceB2570 + difference 1 2) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4985) := by
    have ha : (tripleCharges (sourceA2570 + difference 2 1) (sourceB2570 + difference 1 2) sourceC2570) = raw35519 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35519; decide +kernel
    rw [ha]
    exact (canonical35519 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2570 + difference 2 3) (sourceB2570 + difference 3 2) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5315) := by
    have ha : (tripleCharges (sourceA2570 + difference 2 3) (sourceB2570 + difference 3 2) sourceC2570) = raw35520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35520; decide +kernel
    rw [ha]
    exact (canonical35520 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2570 + difference 2 4) (sourceB2570 + difference 4 2) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA2570 + difference 2 4) (sourceB2570 + difference 4 2) sourceC2570) = raw35521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35521; decide +kernel
    rw [ha]
    exact (canonical35521 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2570 + difference 2 5) (sourceB2570 + difference 5 2) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA2570 + difference 2 5) (sourceB2570 + difference 5 2) sourceC2570) = raw35388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35388; decide +kernel
    rw [ha]
    exact (canonical35388 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2570 + difference 3 0) (sourceB2570 + difference 0 3) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (tripleCharges (sourceA2570 + difference 3 0) (sourceB2570 + difference 0 3) sourceC2570) = raw35522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35522; decide +kernel
    rw [ha]
    exact (canonical35522 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2570 + difference 3 1) (sourceB2570 + difference 1 3) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5024) := by
    have ha : (tripleCharges (sourceA2570 + difference 3 1) (sourceB2570 + difference 1 3) sourceC2570) = raw35523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35523; decide +kernel
    rw [ha]
    exact (canonical35523 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2570 + difference 3 2) (sourceB2570 + difference 2 3) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5327) := by
    have ha : (tripleCharges (sourceA2570 + difference 3 2) (sourceB2570 + difference 2 3) sourceC2570) = raw35524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35524; decide +kernel
    rw [ha]
    exact (canonical35524 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2570 + difference 3 4) (sourceB2570 + difference 4 3) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2570 + difference 3 4) (sourceB2570 + difference 4 3) sourceC2570) = raw35275 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35275; decide +kernel
    rw [ha]
    exact (canonical35275 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2570 + difference 3 5) (sourceB2570 + difference 5 3) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2570 + difference 3 5) (sourceB2570 + difference 5 3) sourceC2570) = raw35271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35271; decide +kernel
    rw [ha]
    exact (canonical35271 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2570 + difference 4 0) (sourceB2570 + difference 0 4) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4915) := by
    have ha : (tripleCharges (sourceA2570 + difference 4 0) (sourceB2570 + difference 0 4) sourceC2570) = raw35525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35525; decide +kernel
    rw [ha]
    exact (canonical35525 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2570 + difference 4 1) (sourceB2570 + difference 1 4) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2570 + difference 4 1) (sourceB2570 + difference 1 4) sourceC2570) = raw35526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35526; decide +kernel
    rw [ha]
    exact (canonical35526 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2570 + difference 4 2) (sourceB2570 + difference 2 4) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4910) := by
    have ha : (tripleCharges (sourceA2570 + difference 4 2) (sourceB2570 + difference 2 4) sourceC2570) = raw35527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35527; decide +kernel
    rw [ha]
    exact (canonical35527 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2570 + difference 4 3) (sourceB2570 + difference 3 4) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4922) := by
    have ha : (tripleCharges (sourceA2570 + difference 4 3) (sourceB2570 + difference 3 4) sourceC2570) = raw35528 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35528; decide +kernel
    rw [ha]
    exact (canonical35528 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2570 + difference 4 5) (sourceB2570 + difference 5 4) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2570 + difference 4 5) (sourceB2570 + difference 5 4) sourceC2570) = raw35392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35392; decide +kernel
    rw [ha]
    exact (canonical35392 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2570 + difference 5 0) (sourceB2570 + difference 0 5) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4915) := by
    have ha : (tripleCharges (sourceA2570 + difference 5 0) (sourceB2570 + difference 0 5) sourceC2570) = raw35529 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35529; decide +kernel
    rw [ha]
    exact (canonical35529 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2570 + difference 5 1) (sourceB2570 + difference 1 5) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2570 + difference 5 1) (sourceB2570 + difference 1 5) sourceC2570) = raw35530 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35530; decide +kernel
    rw [ha]
    exact (canonical35530 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2570 + difference 5 2) (sourceB2570 + difference 2 5) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4910) := by
    have ha : (tripleCharges (sourceA2570 + difference 5 2) (sourceB2570 + difference 2 5) sourceC2570) = raw35531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35531; decide +kernel
    rw [ha]
    exact (canonical35531 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2570 + difference 5 3) (sourceB2570 + difference 3 5) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4922) := by
    have ha : (tripleCharges (sourceA2570 + difference 5 3) (sourceB2570 + difference 3 5) sourceC2570) = raw35532 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35532; decide +kernel
    rw [ha]
    exact (canonical35532 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2570 + difference 5 4) (sourceB2570 + difference 4 5) sourceC2570) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2570 + difference 5 4) (sourceB2570 + difference 4 5) sourceC2570) = raw35533 := by
      apply Matrix.ext; unfold tripleCharges sourceA2570 sourceB2570 sourceC2570 difference raw35533; decide +kernel
    rw [ha]
    exact (canonical35533 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2570 sourceB2570 sourceC2570
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2570, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2571 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2571 : Charge := ![2, 2, 0, 0, -2, -2]
def sourceC2571 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm2571 : Integer.Sparse Master := [(Sum.inr 4075, 8), (Sum.inr 4076, 4), (Sum.inr 4082, 4), (Sum.inr 4086, 2), (Sum.inr 4088, 8), (Sum.inr 4092, 4)]

theorem sourceEq2571 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2571 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2571 + difference 0 1) (sourceB2571 + difference 1 0) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2571 + difference 0 1) (sourceB2571 + difference 1 0) sourceC2571) = raw35534 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35534; decide +kernel
    rw [ha]
    exact (canonical35534 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2571 + difference 0 2) (sourceB2571 + difference 2 0) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 0 2) (sourceB2571 + difference 2 0) sourceC2571) = raw35535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35535; decide +kernel
    rw [ha]
    exact (canonical35535 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2571 + difference 0 3) (sourceB2571 + difference 3 0) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 0 3) (sourceB2571 + difference 3 0) sourceC2571) = raw35536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35536; decide +kernel
    rw [ha]
    exact (canonical35536 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2571 + difference 0 4) (sourceB2571 + difference 4 0) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2571 + difference 0 4) (sourceB2571 + difference 4 0) sourceC2571) = raw3448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw3448; decide +kernel
    rw [ha]
    exact (canonical3448 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2571 + difference 0 5) (sourceB2571 + difference 5 0) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2571 + difference 0 5) (sourceB2571 + difference 5 0) sourceC2571) = raw3444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw3444; decide +kernel
    rw [ha]
    exact (canonical3444 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2571 + difference 1 0) (sourceB2571 + difference 0 1) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2571 + difference 1 0) (sourceB2571 + difference 0 1) sourceC2571) = raw11541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw11541; decide +kernel
    rw [ha]
    exact (canonical11541 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2571 + difference 1 2) (sourceB2571 + difference 2 1) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 1 2) (sourceB2571 + difference 2 1) sourceC2571) = raw18340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw18340; decide +kernel
    rw [ha]
    exact (canonical18340 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2571 + difference 1 3) (sourceB2571 + difference 3 1) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 1 3) (sourceB2571 + difference 3 1) sourceC2571) = raw18341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw18341; decide +kernel
    rw [ha]
    exact (canonical18341 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2571 + difference 1 4) (sourceB2571 + difference 4 1) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2571 + difference 1 4) (sourceB2571 + difference 4 1) sourceC2571) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2571 + difference 1 5) (sourceB2571 + difference 5 1) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2571 + difference 1 5) (sourceB2571 + difference 5 1) sourceC2571) = raw3336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw3336; decide +kernel
    rw [ha]
    exact (canonical3336 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2571 + difference 2 0) (sourceB2571 + difference 0 2) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 2 0) (sourceB2571 + difference 0 2) sourceC2571) = raw31877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw31877; decide +kernel
    rw [ha]
    exact (canonical31877 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2571 + difference 2 1) (sourceB2571 + difference 1 2) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 2 1) (sourceB2571 + difference 1 2) sourceC2571) = raw35537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35537; decide +kernel
    rw [ha]
    exact (canonical35537 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2571 + difference 2 3) (sourceB2571 + difference 3 2) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2571 + difference 2 3) (sourceB2571 + difference 3 2) sourceC2571) = raw35538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35538; decide +kernel
    rw [ha]
    exact (canonical35538 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2571 + difference 2 4) (sourceB2571 + difference 4 2) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 2 4) (sourceB2571 + difference 4 2) sourceC2571) = raw18335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw18335; decide +kernel
    rw [ha]
    exact (canonical18335 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2571 + difference 2 5) (sourceB2571 + difference 5 2) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 2 5) (sourceB2571 + difference 5 2) sourceC2571) = raw35539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35539; decide +kernel
    rw [ha]
    exact (canonical35539 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2571 + difference 3 0) (sourceB2571 + difference 0 3) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 3 0) (sourceB2571 + difference 0 3) sourceC2571) = raw31880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw31880; decide +kernel
    rw [ha]
    exact (canonical31880 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2571 + difference 3 1) (sourceB2571 + difference 1 3) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 3 1) (sourceB2571 + difference 1 3) sourceC2571) = raw35540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35540; decide +kernel
    rw [ha]
    exact (canonical35540 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2571 + difference 3 2) (sourceB2571 + difference 2 3) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4086) := by
    have ha : (tripleCharges (sourceA2571 + difference 3 2) (sourceB2571 + difference 2 3) sourceC2571) = raw35541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35541; decide +kernel
    rw [ha]
    exact (canonical35541 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2571 + difference 3 4) (sourceB2571 + difference 4 3) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 3 4) (sourceB2571 + difference 4 3) sourceC2571) = raw18337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw18337; decide +kernel
    rw [ha]
    exact (canonical18337 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2571 + difference 3 5) (sourceB2571 + difference 5 3) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2571 + difference 3 5) (sourceB2571 + difference 5 3) sourceC2571) = raw19367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw19367; decide +kernel
    rw [ha]
    exact (canonical19367 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2571 + difference 4 0) (sourceB2571 + difference 0 4) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (tripleCharges (sourceA2571 + difference 4 0) (sourceB2571 + difference 0 4) sourceC2571) = raw31882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw31882; decide +kernel
    rw [ha]
    exact (canonical31882 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2571 + difference 4 1) (sourceB2571 + difference 1 4) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (tripleCharges (sourceA2571 + difference 4 1) (sourceB2571 + difference 1 4) sourceC2571) = raw35542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35542; decide +kernel
    rw [ha]
    exact (canonical35542 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2571 + difference 4 2) (sourceB2571 + difference 2 4) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 4 2) (sourceB2571 + difference 2 4) sourceC2571) = raw35543 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35543; decide +kernel
    rw [ha]
    exact (canonical35543 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2571 + difference 4 3) (sourceB2571 + difference 3 4) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 4 3) (sourceB2571 + difference 3 4) sourceC2571) = raw35544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35544; decide +kernel
    rw [ha]
    exact (canonical35544 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2571 + difference 4 5) (sourceB2571 + difference 5 4) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2571 + difference 4 5) (sourceB2571 + difference 5 4) sourceC2571) = raw35545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35545; decide +kernel
    rw [ha]
    exact (canonical35545 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2571 + difference 5 0) (sourceB2571 + difference 0 5) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (tripleCharges (sourceA2571 + difference 5 0) (sourceB2571 + difference 0 5) sourceC2571) = raw29299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw29299; decide +kernel
    rw [ha]
    exact (canonical29299 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2571 + difference 5 1) (sourceB2571 + difference 1 5) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (tripleCharges (sourceA2571 + difference 5 1) (sourceB2571 + difference 1 5) sourceC2571) = raw35546 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35546; decide +kernel
    rw [ha]
    exact (canonical35546 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2571 + difference 5 2) (sourceB2571 + difference 2 5) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 5 2) (sourceB2571 + difference 2 5) sourceC2571) = raw35547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35547; decide +kernel
    rw [ha]
    exact (canonical35547 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2571 + difference 5 3) (sourceB2571 + difference 3 5) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2571 + difference 5 3) (sourceB2571 + difference 3 5) sourceC2571) = raw35548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw35548; decide +kernel
    rw [ha]
    exact (canonical35548 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2571 + difference 5 4) (sourceB2571 + difference 4 5) sourceC2571) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2571 + difference 5 4) (sourceB2571 + difference 4 5) sourceC2571) = raw18342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2571 sourceB2571 sourceC2571 difference raw18342; decide +kernel
    rw [ha]
    exact (canonical18342 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2571 sourceB2571 sourceC2571
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2571, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2572 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2572 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2572 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm2572 : Integer.Sparse Master := [(Sum.inr 4685, 1), (Sum.inr 4686, 1), (Sum.inr 4688, 2), (Sum.inr 4869, 1), (Sum.inr 4967, 1), (Sum.inr 4970, 1), (Sum.inr 4973, 2), (Sum.inr 5114, 1), (Sum.inr 5168, 1), (Sum.inr 5176, 2), (Sum.inr 5372, 2), (Sum.inr 5383, 1), (Sum.inr 5384, 2), (Sum.inr 5387, 2), (Sum.inr 5389, 2), (Sum.inr 5403, 1), (Sum.inr 5415, 1), (Sum.inr 5439, 1), (Sum.inr 5441, 2), (Sum.inr 5443, 2), (Sum.inr 5448, 1)]

theorem sourceEq2572 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2572 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2572 + difference 0 1) (sourceB2572 + difference 1 0) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2572 + difference 0 1) (sourceB2572 + difference 1 0) sourceC2572) = raw35549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw35549; decide +kernel
    rw [ha]
    exact (canonical35549 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2572 + difference 0 2) (sourceB2572 + difference 2 0) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA2572 + difference 0 2) (sourceB2572 + difference 2 0) sourceC2572) = raw19387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw19387; decide +kernel
    rw [ha]
    exact (canonical19387 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2572 + difference 0 3) (sourceB2572 + difference 3 0) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2572 + difference 0 3) (sourceB2572 + difference 3 0) sourceC2572) = raw18294 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw18294; decide +kernel
    rw [ha]
    exact (canonical18294 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2572 + difference 0 4) (sourceB2572 + difference 4 0) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2572 + difference 0 4) (sourceB2572 + difference 4 0) sourceC2572) = raw35550 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw35550; decide +kernel
    rw [ha]
    exact (canonical35550 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2572 + difference 0 5) (sourceB2572 + difference 5 0) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA2572 + difference 0 5) (sourceB2572 + difference 5 0) sourceC2572) = raw18345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw18345; decide +kernel
    rw [ha]
    exact (canonical18345 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2572 + difference 1 0) (sourceB2572 + difference 0 1) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2572 + difference 1 0) (sourceB2572 + difference 0 1) sourceC2572) = raw10229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw10229; decide +kernel
    rw [ha]
    exact (canonical10229 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2572 + difference 1 2) (sourceB2572 + difference 2 1) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5415) := by
    have ha : (tripleCharges (sourceA2572 + difference 1 2) (sourceB2572 + difference 2 1) sourceC2572) = raw18304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw18304; decide +kernel
    rw [ha]
    exact (canonical18304 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2572 + difference 1 3) (sourceB2572 + difference 3 1) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA2572 + difference 1 3) (sourceB2572 + difference 3 1) sourceC2572) = raw10216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw10216; decide +kernel
    rw [ha]
    exact (canonical10216 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2572 + difference 1 4) (sourceB2572 + difference 4 1) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA2572 + difference 1 4) (sourceB2572 + difference 4 1) sourceC2572) = raw18305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw18305; decide +kernel
    rw [ha]
    exact (canonical18305 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2572 + difference 1 5) (sourceB2572 + difference 5 1) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2572 + difference 1 5) (sourceB2572 + difference 5 1) sourceC2572) = raw12080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw12080; decide +kernel
    rw [ha]
    exact (canonical12080 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2572 + difference 2 0) (sourceB2572 + difference 0 2) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4967) := by
    have ha : (tripleCharges (sourceA2572 + difference 2 0) (sourceB2572 + difference 0 2) sourceC2572) = raw32031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw32031; decide +kernel
    rw [ha]
    exact (canonical32031 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2572 + difference 2 1) (sourceB2572 + difference 1 2) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4685) := by
    have ha : (tripleCharges (sourceA2572 + difference 2 1) (sourceB2572 + difference 1 2) sourceC2572) = raw35551 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw35551; decide +kernel
    rw [ha]
    exact (canonical35551 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2572 + difference 2 3) (sourceB2572 + difference 3 2) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2572 + difference 2 3) (sourceB2572 + difference 3 2) sourceC2572) = raw18299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw18299; decide +kernel
    rw [ha]
    exact (canonical18299 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2572 + difference 2 4) (sourceB2572 + difference 4 2) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2572 + difference 2 4) (sourceB2572 + difference 4 2) sourceC2572) = raw35552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw35552; decide +kernel
    rw [ha]
    exact (canonical35552 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2572 + difference 2 5) (sourceB2572 + difference 5 2) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA2572 + difference 2 5) (sourceB2572 + difference 5 2) sourceC2572) = raw18349 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw18349; decide +kernel
    rw [ha]
    exact (canonical18349 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2572 + difference 3 0) (sourceB2572 + difference 0 3) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2572 + difference 3 0) (sourceB2572 + difference 0 3) sourceC2572) = raw32033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw32033; decide +kernel
    rw [ha]
    exact (canonical32033 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2572 + difference 3 1) (sourceB2572 + difference 1 3) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2572 + difference 3 1) (sourceB2572 + difference 1 3) sourceC2572) = raw35553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw35553; decide +kernel
    rw [ha]
    exact (canonical35553 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2572 + difference 3 2) (sourceB2572 + difference 2 3) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5372) := by
    have ha : (tripleCharges (sourceA2572 + difference 3 2) (sourceB2572 + difference 2 3) sourceC2572) = raw35554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw35554; decide +kernel
    rw [ha]
    exact (canonical35554 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2572 + difference 3 4) (sourceB2572 + difference 4 3) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5389) := by
    have ha : (tripleCharges (sourceA2572 + difference 3 4) (sourceB2572 + difference 4 3) sourceC2572) = raw35555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw35555; decide +kernel
    rw [ha]
    exact (canonical35555 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2572 + difference 3 5) (sourceB2572 + difference 5 3) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2572 + difference 3 5) (sourceB2572 + difference 5 3) sourceC2572) = raw18352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw18352; decide +kernel
    rw [ha]
    exact (canonical18352 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2572 + difference 4 0) (sourceB2572 + difference 0 4) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2572 + difference 4 0) (sourceB2572 + difference 0 4) sourceC2572) = raw29509 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw29509; decide +kernel
    rw [ha]
    exact (canonical29509 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2572 + difference 4 1) (sourceB2572 + difference 1 4) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2572 + difference 4 1) (sourceB2572 + difference 1 4) sourceC2572) = raw34789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw34789; decide +kernel
    rw [ha]
    exact (canonical34789 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2572 + difference 4 2) (sourceB2572 + difference 2 4) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5372) := by
    have ha : (tripleCharges (sourceA2572 + difference 4 2) (sourceB2572 + difference 2 4) sourceC2572) = raw34790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw34790; decide +kernel
    rw [ha]
    exact (canonical34790 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2572 + difference 4 3) (sourceB2572 + difference 3 4) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5389) := by
    have ha : (tripleCharges (sourceA2572 + difference 4 3) (sourceB2572 + difference 3 4) sourceC2572) = raw18306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw18306; decide +kernel
    rw [ha]
    exact (canonical18306 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2572 + difference 4 5) (sourceB2572 + difference 5 4) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2572 + difference 4 5) (sourceB2572 + difference 5 4) sourceC2572) = raw18356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw18356; decide +kernel
    rw [ha]
    exact (canonical18356 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2572 + difference 5 0) (sourceB2572 + difference 0 5) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4970) := by
    have ha : (tripleCharges (sourceA2572 + difference 5 0) (sourceB2572 + difference 0 5) sourceC2572) = raw27560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw27560; decide +kernel
    rw [ha]
    exact (canonical27560 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2572 + difference 5 1) (sourceB2572 + difference 1 5) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4686) := by
    have ha : (tripleCharges (sourceA2572 + difference 5 1) (sourceB2572 + difference 1 5) sourceC2572) = raw35556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw35556; decide +kernel
    rw [ha]
    exact (canonical35556 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2572 + difference 5 2) (sourceB2572 + difference 2 5) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5114) := by
    have ha : (tripleCharges (sourceA2572 + difference 5 2) (sourceB2572 + difference 2 5) sourceC2572) = raw35557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw35557; decide +kernel
    rw [ha]
    exact (canonical35557 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2572 + difference 5 3) (sourceB2572 + difference 3 5) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2572 + difference 5 3) (sourceB2572 + difference 3 5) sourceC2572) = raw18310 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw18310; decide +kernel
    rw [ha]
    exact (canonical18310 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2572 + difference 5 4) (sourceB2572 + difference 4 5) sourceC2572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2572 + difference 5 4) (sourceB2572 + difference 4 5) sourceC2572) = raw35558 := by
      apply Matrix.ext; unfold tripleCharges sourceA2572 sourceB2572 sourceC2572 difference raw35558; decide +kernel
    rw [ha]
    exact (canonical35558 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2572 sourceB2572 sourceC2572
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2572, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2573 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2573 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2573 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceForm2573 : Integer.Sparse Master := [(Sum.inr 4676, 1), (Sum.inr 4678, 1), (Sum.inr 4684, 2), (Sum.inr 4766, 1), (Sum.inr 4770, 1), (Sum.inr 4810, 2), (Sum.inr 4865, 1), (Sum.inr 4971, 1), (Sum.inr 4977, 2), (Sum.inr 5172, 1), (Sum.inr 5336, 2), (Sum.inr 5355, 2), (Sum.inr 5378, 2), (Sum.inr 5386, 1), (Sum.inr 5388, 2), (Sum.inr 5400, 1), (Sum.inr 5417, 1), (Sum.inr 5432, 2), (Sum.inr 5435, 2), (Sum.inr 5440, 1), (Sum.inr 5450, 1)]

theorem sourceEq2573 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2573 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2573 + difference 0 1) (sourceB2573 + difference 1 0) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2573 + difference 0 1) (sourceB2573 + difference 1 0) sourceC2573) = raw35559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35559; decide +kernel
    rw [ha]
    exact (canonical35559 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2573 + difference 0 2) (sourceB2573 + difference 2 0) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5417) := by
    have ha : (tripleCharges (sourceA2573 + difference 0 2) (sourceB2573 + difference 2 0) sourceC2573) = raw35560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35560; decide +kernel
    rw [ha]
    exact (canonical35560 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2573 + difference 0 3) (sourceB2573 + difference 3 0) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2573 + difference 0 3) (sourceB2573 + difference 3 0) sourceC2573) = raw18182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18182; decide +kernel
    rw [ha]
    exact (canonical18182 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2573 + difference 0 4) (sourceB2573 + difference 4 0) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2573 + difference 0 4) (sourceB2573 + difference 4 0) sourceC2573) = raw35561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35561; decide +kernel
    rw [ha]
    exact (canonical35561 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2573 + difference 0 5) (sourceB2573 + difference 5 0) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA2573 + difference 0 5) (sourceB2573 + difference 5 0) sourceC2573) = raw18485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18485; decide +kernel
    rw [ha]
    exact (canonical18485 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2573 + difference 1 0) (sourceB2573 + difference 0 1) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2573 + difference 1 0) (sourceB2573 + difference 0 1) sourceC2573) = raw18197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18197; decide +kernel
    rw [ha]
    exact (canonical18197 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2573 + difference 1 2) (sourceB2573 + difference 2 1) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA2573 + difference 1 2) (sourceB2573 + difference 2 1) sourceC2573) = raw18199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18199; decide +kernel
    rw [ha]
    exact (canonical18199 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2573 + difference 1 3) (sourceB2573 + difference 3 1) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA2573 + difference 1 3) (sourceB2573 + difference 3 1) sourceC2573) = raw18506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18506; decide +kernel
    rw [ha]
    exact (canonical18506 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2573 + difference 1 4) (sourceB2573 + difference 4 1) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA2573 + difference 1 4) (sourceB2573 + difference 4 1) sourceC2573) = raw18200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18200; decide +kernel
    rw [ha]
    exact (canonical18200 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2573 + difference 1 5) (sourceB2573 + difference 5 1) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2573 + difference 1 5) (sourceB2573 + difference 5 1) sourceC2573) = raw18201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18201; decide +kernel
    rw [ha]
    exact (canonical18201 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2573 + difference 2 0) (sourceB2573 + difference 0 2) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4676) := by
    have ha : (tripleCharges (sourceA2573 + difference 2 0) (sourceB2573 + difference 0 2) sourceC2573) = raw33723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw33723; decide +kernel
    rw [ha]
    exact (canonical33723 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2573 + difference 2 1) (sourceB2573 + difference 1 2) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4971) := by
    have ha : (tripleCharges (sourceA2573 + difference 2 1) (sourceB2573 + difference 1 2) sourceC2573) = raw35562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35562; decide +kernel
    rw [ha]
    exact (canonical35562 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2573 + difference 2 3) (sourceB2573 + difference 3 2) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2573 + difference 2 3) (sourceB2573 + difference 3 2) sourceC2573) = raw18193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18193; decide +kernel
    rw [ha]
    exact (canonical18193 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2573 + difference 2 4) (sourceB2573 + difference 4 2) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2573 + difference 2 4) (sourceB2573 + difference 4 2) sourceC2573) = raw35563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35563; decide +kernel
    rw [ha]
    exact (canonical35563 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2573 + difference 2 5) (sourceB2573 + difference 5 2) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5386) := by
    have ha : (tripleCharges (sourceA2573 + difference 2 5) (sourceB2573 + difference 5 2) sourceC2573) = raw18494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18494; decide +kernel
    rw [ha]
    exact (canonical18494 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2573 + difference 3 0) (sourceB2573 + difference 0 3) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2573 + difference 3 0) (sourceB2573 + difference 0 3) sourceC2573) = raw33726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw33726; decide +kernel
    rw [ha]
    exact (canonical33726 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2573 + difference 3 1) (sourceB2573 + difference 1 3) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2573 + difference 3 1) (sourceB2573 + difference 1 3) sourceC2573) = raw35564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35564; decide +kernel
    rw [ha]
    exact (canonical35564 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2573 + difference 3 2) (sourceB2573 + difference 2 3) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5336) := by
    have ha : (tripleCharges (sourceA2573 + difference 3 2) (sourceB2573 + difference 2 3) sourceC2573) = raw35565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35565; decide +kernel
    rw [ha]
    exact (canonical35565 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2573 + difference 3 4) (sourceB2573 + difference 4 3) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2573 + difference 3 4) (sourceB2573 + difference 4 3) sourceC2573) = raw35566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35566; decide +kernel
    rw [ha]
    exact (canonical35566 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2573 + difference 3 5) (sourceB2573 + difference 5 3) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2573 + difference 3 5) (sourceB2573 + difference 5 3) sourceC2573) = raw18498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18498; decide +kernel
    rw [ha]
    exact (canonical18498 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2573 + difference 4 0) (sourceB2573 + difference 0 4) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2573 + difference 4 0) (sourceB2573 + difference 0 4) sourceC2573) = raw33730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw33730; decide +kernel
    rw [ha]
    exact (canonical33730 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2573 + difference 4 1) (sourceB2573 + difference 1 4) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2573 + difference 4 1) (sourceB2573 + difference 1 4) sourceC2573) = raw35567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35567; decide +kernel
    rw [ha]
    exact (canonical35567 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2573 + difference 4 2) (sourceB2573 + difference 2 4) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5336) := by
    have ha : (tripleCharges (sourceA2573 + difference 4 2) (sourceB2573 + difference 2 4) sourceC2573) = raw35568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35568; decide +kernel
    rw [ha]
    exact (canonical35568 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2573 + difference 4 3) (sourceB2573 + difference 3 4) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2573 + difference 4 3) (sourceB2573 + difference 3 4) sourceC2573) = raw18203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18203; decide +kernel
    rw [ha]
    exact (canonical18203 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2573 + difference 4 5) (sourceB2573 + difference 5 4) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2573 + difference 4 5) (sourceB2573 + difference 5 4) sourceC2573) = raw18503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18503; decide +kernel
    rw [ha]
    exact (canonical18503 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2573 + difference 5 0) (sourceB2573 + difference 0 5) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2573 + difference 5 0) (sourceB2573 + difference 0 5) sourceC2573) = raw33733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw33733; decide +kernel
    rw [ha]
    exact (canonical33733 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2573 + difference 5 1) (sourceB2573 + difference 1 5) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA2573 + difference 5 1) (sourceB2573 + difference 1 5) sourceC2573) = raw35569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35569; decide +kernel
    rw [ha]
    exact (canonical35569 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2573 + difference 5 2) (sourceB2573 + difference 2 5) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4766) := by
    have ha : (tripleCharges (sourceA2573 + difference 5 2) (sourceB2573 + difference 2 5) sourceC2573) = raw35570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35570; decide +kernel
    rw [ha]
    exact (canonical35570 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2573 + difference 5 3) (sourceB2573 + difference 3 5) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2573 + difference 5 3) (sourceB2573 + difference 3 5) sourceC2573) = raw18208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18208; decide +kernel
    rw [ha]
    exact (canonical18208 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2573 + difference 5 4) (sourceB2573 + difference 4 5) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2573 + difference 5 4) (sourceB2573 + difference 4 5) sourceC2573) = raw35571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35571; decide +kernel
    rw [ha]
    exact (canonical35571 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2573 sourceB2573 sourceC2573
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2573, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2574 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceB2574 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2574 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceForm2574 : Integer.Sparse Master := [(Sum.inr 5219, 1), (Sum.inr 5222, 1), (Sum.inr 5228, 2), (Sum.inr 5231, 1), (Sum.inr 5233, 2), (Sum.inr 5237, 1), (Sum.inr 5243, 1), (Sum.inr 5248, 1), (Sum.inr 5264, 2), (Sum.inr 5279, 1), (Sum.inr 5351, 1), (Sum.inr 5354, 1), (Sum.inr 5367, 2), (Sum.inr 5369, 1), (Sum.inr 5370, 2), (Sum.inr 5378, 2), (Sum.inr 5380, 1), (Sum.inr 5381, 2), (Sum.inr 5384, 2), (Sum.inr 5388, 2), (Sum.inr 5418, 1)]

theorem sourceEq2574 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2574 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2574 + difference 0 1) (sourceB2574 + difference 1 0) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2574 + difference 0 1) (sourceB2574 + difference 1 0) sourceC2574) = raw35572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35572; decide +kernel
    rw [ha]
    exact (canonical35572 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2574 + difference 0 2) (sourceB2574 + difference 2 0) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2574 + difference 0 2) (sourceB2574 + difference 2 0) sourceC2574) = raw35573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35573; decide +kernel
    rw [ha]
    exact (canonical35573 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2574 + difference 0 3) (sourceB2574 + difference 3 0) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2574 + difference 0 3) (sourceB2574 + difference 3 0) sourceC2574) = raw35574 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35574; decide +kernel
    rw [ha]
    exact (canonical35574 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2574 + difference 0 4) (sourceB2574 + difference 4 0) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2574 + difference 0 4) (sourceB2574 + difference 4 0) sourceC2574) = raw35575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35575; decide +kernel
    rw [ha]
    exact (canonical35575 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2574 + difference 0 5) (sourceB2574 + difference 5 0) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2574 + difference 0 5) (sourceB2574 + difference 5 0) sourceC2574) = raw35576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35576; decide +kernel
    rw [ha]
    exact (canonical35576 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2574 + difference 1 0) (sourceB2574 + difference 0 1) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5279) := by
    have ha : (tripleCharges (sourceA2574 + difference 1 0) (sourceB2574 + difference 0 1) sourceC2574) = raw35577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35577; decide +kernel
    rw [ha]
    exact (canonical35577 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2574 + difference 1 2) (sourceB2574 + difference 2 1) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA2574 + difference 1 2) (sourceB2574 + difference 2 1) sourceC2574) = raw35578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35578; decide +kernel
    rw [ha]
    exact (canonical35578 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2574 + difference 1 3) (sourceB2574 + difference 3 1) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA2574 + difference 1 3) (sourceB2574 + difference 3 1) sourceC2574) = raw35579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35579; decide +kernel
    rw [ha]
    exact (canonical35579 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2574 + difference 1 4) (sourceB2574 + difference 4 1) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA2574 + difference 1 4) (sourceB2574 + difference 4 1) sourceC2574) = raw35580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35580; decide +kernel
    rw [ha]
    exact (canonical35580 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2574 + difference 1 5) (sourceB2574 + difference 5 1) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2574 + difference 1 5) (sourceB2574 + difference 5 1) sourceC2574) = raw35581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35581; decide +kernel
    rw [ha]
    exact (canonical35581 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2574 + difference 2 0) (sourceB2574 + difference 0 2) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA2574 + difference 2 0) (sourceB2574 + difference 0 2) sourceC2574) = raw35582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35582; decide +kernel
    rw [ha]
    exact (canonical35582 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2574 + difference 2 1) (sourceB2574 + difference 1 2) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2574 + difference 2 1) (sourceB2574 + difference 1 2) sourceC2574) = raw35583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35583; decide +kernel
    rw [ha]
    exact (canonical35583 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2574 + difference 2 3) (sourceB2574 + difference 3 2) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA2574 + difference 2 3) (sourceB2574 + difference 3 2) sourceC2574) = raw35584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35584; decide +kernel
    rw [ha]
    exact (canonical35584 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2574 + difference 2 4) (sourceB2574 + difference 4 2) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA2574 + difference 2 4) (sourceB2574 + difference 4 2) sourceC2574) = raw35585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35585; decide +kernel
    rw [ha]
    exact (canonical35585 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2574 + difference 2 5) (sourceB2574 + difference 5 2) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2574 + difference 2 5) (sourceB2574 + difference 5 2) sourceC2574) = raw35586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35586; decide +kernel
    rw [ha]
    exact (canonical35586 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2574 + difference 3 0) (sourceB2574 + difference 0 3) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2574 + difference 3 0) (sourceB2574 + difference 0 3) sourceC2574) = raw35587 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35587; decide +kernel
    rw [ha]
    exact (canonical35587 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2574 + difference 3 1) (sourceB2574 + difference 1 3) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2574 + difference 3 1) (sourceB2574 + difference 1 3) sourceC2574) = raw35588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35588; decide +kernel
    rw [ha]
    exact (canonical35588 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2574 + difference 3 2) (sourceB2574 + difference 2 3) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2574 + difference 3 2) (sourceB2574 + difference 2 3) sourceC2574) = raw35589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35589; decide +kernel
    rw [ha]
    exact (canonical35589 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2574 + difference 3 4) (sourceB2574 + difference 4 3) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2574 + difference 3 4) (sourceB2574 + difference 4 3) sourceC2574) = raw35590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35590; decide +kernel
    rw [ha]
    exact (canonical35590 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2574 + difference 3 5) (sourceB2574 + difference 5 3) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2574 + difference 3 5) (sourceB2574 + difference 5 3) sourceC2574) = raw35591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35591; decide +kernel
    rw [ha]
    exact (canonical35591 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2574 + difference 4 0) (sourceB2574 + difference 0 4) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2574 + difference 4 0) (sourceB2574 + difference 0 4) sourceC2574) = raw35592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35592; decide +kernel
    rw [ha]
    exact (canonical35592 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2574 + difference 4 1) (sourceB2574 + difference 1 4) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2574 + difference 4 1) (sourceB2574 + difference 1 4) sourceC2574) = raw35593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35593; decide +kernel
    rw [ha]
    exact (canonical35593 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2574 + difference 4 2) (sourceB2574 + difference 2 4) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2574 + difference 4 2) (sourceB2574 + difference 2 4) sourceC2574) = raw35594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35594; decide +kernel
    rw [ha]
    exact (canonical35594 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2574 + difference 4 3) (sourceB2574 + difference 3 4) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2574 + difference 4 3) (sourceB2574 + difference 3 4) sourceC2574) = raw35595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35595; decide +kernel
    rw [ha]
    exact (canonical35595 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2574 + difference 4 5) (sourceB2574 + difference 5 4) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2574 + difference 4 5) (sourceB2574 + difference 5 4) sourceC2574) = raw35596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35596; decide +kernel
    rw [ha]
    exact (canonical35596 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2574 + difference 5 0) (sourceB2574 + difference 0 5) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA2574 + difference 5 0) (sourceB2574 + difference 0 5) sourceC2574) = raw35597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35597; decide +kernel
    rw [ha]
    exact (canonical35597 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2574 + difference 5 1) (sourceB2574 + difference 1 5) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2574 + difference 5 1) (sourceB2574 + difference 1 5) sourceC2574) = raw35598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35598; decide +kernel
    rw [ha]
    exact (canonical35598 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2574 + difference 5 2) (sourceB2574 + difference 2 5) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5243) := by
    have ha : (tripleCharges (sourceA2574 + difference 5 2) (sourceB2574 + difference 2 5) sourceC2574) = raw35599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35599; decide +kernel
    rw [ha]
    exact (canonical35599 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2574 + difference 5 3) (sourceB2574 + difference 3 5) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA2574 + difference 5 3) (sourceB2574 + difference 3 5) sourceC2574) = raw35600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35600; decide +kernel
    rw [ha]
    exact (canonical35600 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2574 + difference 5 4) (sourceB2574 + difference 4 5) sourceC2574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA2574 + difference 5 4) (sourceB2574 + difference 4 5) sourceC2574) = raw35601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2574 sourceB2574 sourceC2574 difference raw35601; decide +kernel
    rw [ha]
    exact (canonical35601 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2574 sourceB2574 sourceC2574
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2574, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2575 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2575 : Charge := ![0, 2, 0, -1, 0, -1]
def sourceC2575 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm2575 : Integer.Sparse Master := [(Sum.inr 4679, 1), (Sum.inr 4681, 1), (Sum.inr 4684, 1), (Sum.inr 4689, 1), (Sum.inr 4866, 1), (Sum.inr 4968, 1), (Sum.inr 4972, 1), (Sum.inr 4974, 1), (Sum.inr 4977, 1), (Sum.inr 5038, 1), (Sum.inr 5080, 1), (Sum.inr 5169, 1), (Sum.inr 5176, 1), (Sum.inr 5336, 1), (Sum.inr 5355, 1), (Sum.inr 5373, 1), (Sum.inr 5380, 1), (Sum.inr 5386, 1), (Sum.inr 5387, 1), (Sum.inr 5388, 2), (Sum.inr 5390, 1), (Sum.inr 5401, 1), (Sum.inr 5416, 1), (Sum.inr 5434, 1), (Sum.inr 5438, 1), (Sum.inr 5440, 1), (Sum.inr 5442, 1), (Sum.inr 5450, 1), (Sum.inr 5451, 1)]

theorem sourceEq2575 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2575 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2575 + difference 0 1) (sourceB2575 + difference 1 0) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2575 + difference 0 1) (sourceB2575 + difference 1 0) sourceC2575) = raw35602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw35602; decide +kernel
    rw [ha]
    exact (canonical35602 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2575 + difference 0 2) (sourceB2575 + difference 2 0) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA2575 + difference 0 2) (sourceB2575 + difference 2 0) sourceC2575) = raw35603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw35603; decide +kernel
    rw [ha]
    exact (canonical35603 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2575 + difference 0 3) (sourceB2575 + difference 3 0) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2575 + difference 0 3) (sourceB2575 + difference 3 0) sourceC2575) = raw34850 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw34850; decide +kernel
    rw [ha]
    exact (canonical34850 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2575 + difference 0 4) (sourceB2575 + difference 4 0) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2575 + difference 0 4) (sourceB2575 + difference 4 0) sourceC2575) = raw35604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw35604; decide +kernel
    rw [ha]
    exact (canonical35604 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2575 + difference 0 5) (sourceB2575 + difference 5 0) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2575 + difference 0 5) (sourceB2575 + difference 5 0) sourceC2575) = raw35605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw35605; decide +kernel
    rw [ha]
    exact (canonical35605 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2575 + difference 1 0) (sourceB2575 + difference 0 1) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2575 + difference 1 0) (sourceB2575 + difference 0 1) sourceC2575) = raw10207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw10207; decide +kernel
    rw [ha]
    exact (canonical10207 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2575 + difference 1 2) (sourceB2575 + difference 2 1) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2575 + difference 1 2) (sourceB2575 + difference 2 1) sourceC2575) = raw32067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw32067; decide +kernel
    rw [ha]
    exact (canonical32067 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2575 + difference 1 3) (sourceB2575 + difference 3 1) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA2575 + difference 1 3) (sourceB2575 + difference 3 1) sourceC2575) = raw10194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw10194; decide +kernel
    rw [ha]
    exact (canonical10194 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2575 + difference 1 4) (sourceB2575 + difference 4 1) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2575 + difference 1 4) (sourceB2575 + difference 4 1) sourceC2575) = raw32068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw32068; decide +kernel
    rw [ha]
    exact (canonical32068 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2575 + difference 1 5) (sourceB2575 + difference 5 1) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA2575 + difference 1 5) (sourceB2575 + difference 5 1) sourceC2575) = raw32069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw32069; decide +kernel
    rw [ha]
    exact (canonical32069 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2575 + difference 2 0) (sourceB2575 + difference 0 2) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4968) := by
    have ha : (tripleCharges (sourceA2575 + difference 2 0) (sourceB2575 + difference 0 2) sourceC2575) = raw32070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw32070; decide +kernel
    rw [ha]
    exact (canonical32070 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2575 + difference 2 1) (sourceB2575 + difference 1 2) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2575 + difference 2 1) (sourceB2575 + difference 1 2) sourceC2575) = raw35606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw35606; decide +kernel
    rw [ha]
    exact (canonical35606 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2575 + difference 2 3) (sourceB2575 + difference 3 2) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2575 + difference 2 3) (sourceB2575 + difference 3 2) sourceC2575) = raw34854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw34854; decide +kernel
    rw [ha]
    exact (canonical34854 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2575 + difference 2 4) (sourceB2575 + difference 4 2) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2575 + difference 2 4) (sourceB2575 + difference 4 2) sourceC2575) = raw35607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw35607; decide +kernel
    rw [ha]
    exact (canonical35607 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2575 + difference 2 5) (sourceB2575 + difference 5 2) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5386) := by
    have ha : (tripleCharges (sourceA2575 + difference 2 5) (sourceB2575 + difference 5 2) sourceC2575) = raw34426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw34426; decide +kernel
    rw [ha]
    exact (canonical34426 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2575 + difference 3 0) (sourceB2575 + difference 0 3) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2575 + difference 3 0) (sourceB2575 + difference 0 3) sourceC2575) = raw32072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw32072; decide +kernel
    rw [ha]
    exact (canonical32072 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2575 + difference 3 1) (sourceB2575 + difference 1 3) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2575 + difference 3 1) (sourceB2575 + difference 1 3) sourceC2575) = raw35608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw35608; decide +kernel
    rw [ha]
    exact (canonical35608 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2575 + difference 3 2) (sourceB2575 + difference 2 3) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5336) := by
    have ha : (tripleCharges (sourceA2575 + difference 3 2) (sourceB2575 + difference 2 3) sourceC2575) = raw35609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw35609; decide +kernel
    rw [ha]
    exact (canonical35609 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2575 + difference 3 4) (sourceB2575 + difference 4 3) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2575 + difference 3 4) (sourceB2575 + difference 4 3) sourceC2575) = raw35610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw35610; decide +kernel
    rw [ha]
    exact (canonical35610 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2575 + difference 3 5) (sourceB2575 + difference 5 3) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2575 + difference 3 5) (sourceB2575 + difference 5 3) sourceC2575) = raw35611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw35611; decide +kernel
    rw [ha]
    exact (canonical35611 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2575 + difference 4 0) (sourceB2575 + difference 0 4) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4974) := by
    have ha : (tripleCharges (sourceA2575 + difference 4 0) (sourceB2575 + difference 0 4) sourceC2575) = raw29629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw29629; decide +kernel
    rw [ha]
    exact (canonical29629 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2575 + difference 4 1) (sourceB2575 + difference 1 4) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4689) := by
    have ha : (tripleCharges (sourceA2575 + difference 4 1) (sourceB2575 + difference 1 4) sourceC2575) = raw34856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw34856; decide +kernel
    rw [ha]
    exact (canonical34856 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2575 + difference 4 2) (sourceB2575 + difference 2 4) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5373) := by
    have ha : (tripleCharges (sourceA2575 + difference 4 2) (sourceB2575 + difference 2 4) sourceC2575) = raw34857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw34857; decide +kernel
    rw [ha]
    exact (canonical34857 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2575 + difference 4 3) (sourceB2575 + difference 3 4) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2575 + difference 4 3) (sourceB2575 + difference 3 4) sourceC2575) = raw29622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw29622; decide +kernel
    rw [ha]
    exact (canonical29622 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2575 + difference 4 5) (sourceB2575 + difference 5 4) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2575 + difference 4 5) (sourceB2575 + difference 5 4) sourceC2575) = raw34858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw34858; decide +kernel
    rw [ha]
    exact (canonical34858 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2575 + difference 5 0) (sourceB2575 + difference 0 5) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA2575 + difference 5 0) (sourceB2575 + difference 0 5) sourceC2575) = raw27615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw27615; decide +kernel
    rw [ha]
    exact (canonical27615 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2575 + difference 5 1) (sourceB2575 + difference 1 5) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2575 + difference 5 1) (sourceB2575 + difference 1 5) sourceC2575) = raw35612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw35612; decide +kernel
    rw [ha]
    exact (canonical35612 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2575 + difference 5 2) (sourceB2575 + difference 2 5) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5038) := by
    have ha : (tripleCharges (sourceA2575 + difference 5 2) (sourceB2575 + difference 2 5) sourceC2575) = raw35613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw35613; decide +kernel
    rw [ha]
    exact (canonical35613 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2575 + difference 5 3) (sourceB2575 + difference 3 5) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2575 + difference 5 3) (sourceB2575 + difference 3 5) sourceC2575) = raw27610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw27610; decide +kernel
    rw [ha]
    exact (canonical27610 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2575 + difference 5 4) (sourceB2575 + difference 4 5) sourceC2575) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2575 + difference 5 4) (sourceB2575 + difference 4 5) sourceC2575) = raw35614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2575 sourceB2575 sourceC2575 difference raw35614; decide +kernel
    rw [ha]
    exact (canonical35614 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2575 sourceB2575 sourceC2575
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2575, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2576 : Charge := ![0, 2, 0, -1, 0, -1]
def sourceB2576 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2576 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceForm2576 : Integer.Sparse Master := [(Sum.inr 5226, 2), (Sum.inr 5228, 2), (Sum.inr 5229, 2), (Sum.inr 5237, 2), (Sum.inr 5288, 1), (Sum.inr 5352, 2), (Sum.inr 5367, 2), (Sum.inr 5368, 2), (Sum.inr 5369, 2), (Sum.inr 5378, 2), (Sum.inr 5379, 2), (Sum.inr 5380, 2), (Sum.inr 5384, 2), (Sum.inr 5385, 1), (Sum.inr 5387, 2), (Sum.inr 5388, 1), (Sum.inr 5465, 1)]

theorem sourceEq2576 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2576 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2576 + difference 0 1) (sourceB2576 + difference 1 0) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2576 + difference 0 1) (sourceB2576 + difference 1 0) sourceC2576) = raw35615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35615; decide +kernel
    rw [ha]
    exact (canonical35615 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2576 + difference 0 2) (sourceB2576 + difference 2 0) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2576 + difference 0 2) (sourceB2576 + difference 2 0) sourceC2576) = raw35616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35616; decide +kernel
    rw [ha]
    exact (canonical35616 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2576 + difference 0 3) (sourceB2576 + difference 3 0) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2576 + difference 0 3) (sourceB2576 + difference 3 0) sourceC2576) = raw35617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35617; decide +kernel
    rw [ha]
    exact (canonical35617 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2576 + difference 0 4) (sourceB2576 + difference 4 0) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2576 + difference 0 4) (sourceB2576 + difference 4 0) sourceC2576) = raw35576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35576; decide +kernel
    rw [ha]
    exact (canonical35576 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2576 + difference 0 5) (sourceB2576 + difference 5 0) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2576 + difference 0 5) (sourceB2576 + difference 5 0) sourceC2576) = raw35618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35618; decide +kernel
    rw [ha]
    exact (canonical35618 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2576 + difference 1 0) (sourceB2576 + difference 0 1) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5288) := by
    have ha : (tripleCharges (sourceA2576 + difference 1 0) (sourceB2576 + difference 0 1) sourceC2576) = raw35619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35619; decide +kernel
    rw [ha]
    exact (canonical35619 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2576 + difference 1 2) (sourceB2576 + difference 2 1) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2576 + difference 1 2) (sourceB2576 + difference 2 1) sourceC2576) = raw35620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35620; decide +kernel
    rw [ha]
    exact (canonical35620 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2576 + difference 1 3) (sourceB2576 + difference 3 1) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA2576 + difference 1 3) (sourceB2576 + difference 3 1) sourceC2576) = raw35621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35621; decide +kernel
    rw [ha]
    exact (canonical35621 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2576 + difference 1 4) (sourceB2576 + difference 4 1) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2576 + difference 1 4) (sourceB2576 + difference 4 1) sourceC2576) = raw35581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35581; decide +kernel
    rw [ha]
    exact (canonical35581 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2576 + difference 1 5) (sourceB2576 + difference 5 1) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2576 + difference 1 5) (sourceB2576 + difference 5 1) sourceC2576) = raw35622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35622; decide +kernel
    rw [ha]
    exact (canonical35622 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2576 + difference 2 0) (sourceB2576 + difference 0 2) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2576 + difference 2 0) (sourceB2576 + difference 0 2) sourceC2576) = raw35623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35623; decide +kernel
    rw [ha]
    exact (canonical35623 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2576 + difference 2 1) (sourceB2576 + difference 1 2) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2576 + difference 2 1) (sourceB2576 + difference 1 2) sourceC2576) = raw35624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35624; decide +kernel
    rw [ha]
    exact (canonical35624 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2576 + difference 2 3) (sourceB2576 + difference 3 2) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2576 + difference 2 3) (sourceB2576 + difference 3 2) sourceC2576) = raw35625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35625; decide +kernel
    rw [ha]
    exact (canonical35625 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2576 + difference 2 4) (sourceB2576 + difference 4 2) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2576 + difference 2 4) (sourceB2576 + difference 4 2) sourceC2576) = raw35586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35586; decide +kernel
    rw [ha]
    exact (canonical35586 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2576 + difference 2 5) (sourceB2576 + difference 5 2) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2576 + difference 2 5) (sourceB2576 + difference 5 2) sourceC2576) = raw35626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35626; decide +kernel
    rw [ha]
    exact (canonical35626 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2576 + difference 3 0) (sourceB2576 + difference 0 3) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2576 + difference 3 0) (sourceB2576 + difference 0 3) sourceC2576) = raw35627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35627; decide +kernel
    rw [ha]
    exact (canonical35627 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2576 + difference 3 1) (sourceB2576 + difference 1 3) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2576 + difference 3 1) (sourceB2576 + difference 1 3) sourceC2576) = raw35628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35628; decide +kernel
    rw [ha]
    exact (canonical35628 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2576 + difference 3 2) (sourceB2576 + difference 2 3) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2576 + difference 3 2) (sourceB2576 + difference 2 3) sourceC2576) = raw35629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35629; decide +kernel
    rw [ha]
    exact (canonical35629 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2576 + difference 3 4) (sourceB2576 + difference 4 3) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2576 + difference 3 4) (sourceB2576 + difference 4 3) sourceC2576) = raw35591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35591; decide +kernel
    rw [ha]
    exact (canonical35591 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2576 + difference 3 5) (sourceB2576 + difference 5 3) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2576 + difference 3 5) (sourceB2576 + difference 5 3) sourceC2576) = raw35630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35630; decide +kernel
    rw [ha]
    exact (canonical35630 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2576 + difference 4 0) (sourceB2576 + difference 0 4) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA2576 + difference 4 0) (sourceB2576 + difference 0 4) sourceC2576) = raw35631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35631; decide +kernel
    rw [ha]
    exact (canonical35631 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2576 + difference 4 1) (sourceB2576 + difference 1 4) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2576 + difference 4 1) (sourceB2576 + difference 1 4) sourceC2576) = raw35632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35632; decide +kernel
    rw [ha]
    exact (canonical35632 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2576 + difference 4 2) (sourceB2576 + difference 2 4) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2576 + difference 4 2) (sourceB2576 + difference 2 4) sourceC2576) = raw35633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35633; decide +kernel
    rw [ha]
    exact (canonical35633 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2576 + difference 4 3) (sourceB2576 + difference 3 4) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5385) := by
    have ha : (tripleCharges (sourceA2576 + difference 4 3) (sourceB2576 + difference 3 4) sourceC2576) = raw35634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35634; decide +kernel
    rw [ha]
    exact (canonical35634 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2576 + difference 4 5) (sourceB2576 + difference 5 4) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2576 + difference 4 5) (sourceB2576 + difference 5 4) sourceC2576) = raw35635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35635; decide +kernel
    rw [ha]
    exact (canonical35635 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2576 + difference 5 0) (sourceB2576 + difference 0 5) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2576 + difference 5 0) (sourceB2576 + difference 0 5) sourceC2576) = raw35592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35592; decide +kernel
    rw [ha]
    exact (canonical35592 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2576 + difference 5 1) (sourceB2576 + difference 1 5) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2576 + difference 5 1) (sourceB2576 + difference 1 5) sourceC2576) = raw35593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35593; decide +kernel
    rw [ha]
    exact (canonical35593 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2576 + difference 5 2) (sourceB2576 + difference 2 5) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2576 + difference 5 2) (sourceB2576 + difference 2 5) sourceC2576) = raw35594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35594; decide +kernel
    rw [ha]
    exact (canonical35594 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2576 + difference 5 3) (sourceB2576 + difference 3 5) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2576 + difference 5 3) (sourceB2576 + difference 3 5) sourceC2576) = raw35595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35595; decide +kernel
    rw [ha]
    exact (canonical35595 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2576 + difference 5 4) (sourceB2576 + difference 4 5) sourceC2576) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2576 + difference 5 4) (sourceB2576 + difference 4 5) sourceC2576) = raw35636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2576 sourceB2576 sourceC2576 difference raw35636; decide +kernel
    rw [ha]
    exact (canonical35636 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2576 sourceB2576 sourceC2576
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2576, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2577 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2577 : Charge := ![0, 2, 0, -1, 1, -2]
def sourceC2577 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm2577 : Integer.Sparse Master := [(Sum.inr 4672, 1), (Sum.inr 4673, 1), (Sum.inr 4674, 1), (Sum.inr 4688, 1), (Sum.inr 4724, 1), (Sum.inr 4727, 1), (Sum.inr 4749, 1), (Sum.inr 4860, 1), (Sum.inr 4874, 1), (Sum.inr 4969, 1), (Sum.inr 4973, 1), (Sum.inr 4978, 1), (Sum.inr 5170, 1), (Sum.inr 5318, 1), (Sum.inr 5329, 1), (Sum.inr 5372, 1), (Sum.inr 5374, 1), (Sum.inr 5383, 1), (Sum.inr 5384, 3), (Sum.inr 5387, 1), (Sum.inr 5389, 1), (Sum.inr 5398, 1), (Sum.inr 5403, 1), (Sum.inr 5412, 1), (Sum.inr 5439, 1), (Sum.inr 5443, 1), (Sum.inr 5448, 1), (Sum.inr 5449, 1)]

theorem sourceEq2577 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2577 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2577 + difference 0 1) (sourceB2577 + difference 1 0) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2577 + difference 0 1) (sourceB2577 + difference 1 0) sourceC2577) = raw35637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35637; decide +kernel
    rw [ha]
    exact (canonical35637 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2577 + difference 0 2) (sourceB2577 + difference 2 0) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5398) := by
    have ha : (tripleCharges (sourceA2577 + difference 0 2) (sourceB2577 + difference 2 0) sourceC2577) = raw35638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35638; decide +kernel
    rw [ha]
    exact (canonical35638 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2577 + difference 0 3) (sourceB2577 + difference 3 0) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5449) := by
    have ha : (tripleCharges (sourceA2577 + difference 0 3) (sourceB2577 + difference 3 0) sourceC2577) = raw14876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw14876; decide +kernel
    rw [ha]
    exact (canonical14876 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2577 + difference 0 4) (sourceB2577 + difference 4 0) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2577 + difference 0 4) (sourceB2577 + difference 4 0) sourceC2577) = raw35639 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35639; decide +kernel
    rw [ha]
    exact (canonical35639 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2577 + difference 0 5) (sourceB2577 + difference 5 0) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA2577 + difference 0 5) (sourceB2577 + difference 5 0) sourceC2577) = raw35640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35640; decide +kernel
    rw [ha]
    exact (canonical35640 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2577 + difference 1 0) (sourceB2577 + difference 0 1) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2577 + difference 1 0) (sourceB2577 + difference 0 1) sourceC2577) = raw7567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw7567; decide +kernel
    rw [ha]
    exact (canonical7567 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2577 + difference 1 2) (sourceB2577 + difference 2 1) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA2577 + difference 1 2) (sourceB2577 + difference 2 1) sourceC2577) = raw14884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw14884; decide +kernel
    rw [ha]
    exact (canonical14884 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2577 + difference 1 3) (sourceB2577 + difference 3 1) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2577 + difference 1 3) (sourceB2577 + difference 3 1) sourceC2577) = raw2652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw2652; decide +kernel
    rw [ha]
    exact (canonical2652 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2577 + difference 1 4) (sourceB2577 + difference 4 1) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA2577 + difference 1 4) (sourceB2577 + difference 4 1) sourceC2577) = raw2647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw2647; decide +kernel
    rw [ha]
    exact (canonical2647 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2577 + difference 1 5) (sourceB2577 + difference 5 1) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2577 + difference 1 5) (sourceB2577 + difference 5 1) sourceC2577) = raw14885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw14885; decide +kernel
    rw [ha]
    exact (canonical14885 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2577 + difference 2 0) (sourceB2577 + difference 0 2) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4969) := by
    have ha : (tripleCharges (sourceA2577 + difference 2 0) (sourceB2577 + difference 0 2) sourceC2577) = raw32104 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw32104; decide +kernel
    rw [ha]
    exact (canonical32104 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2577 + difference 2 1) (sourceB2577 + difference 1 2) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4672) := by
    have ha : (tripleCharges (sourceA2577 + difference 2 1) (sourceB2577 + difference 1 2) sourceC2577) = raw35641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35641; decide +kernel
    rw [ha]
    exact (canonical35641 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2577 + difference 2 3) (sourceB2577 + difference 3 2) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2577 + difference 2 3) (sourceB2577 + difference 3 2) sourceC2577) = raw14880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw14880; decide +kernel
    rw [ha]
    exact (canonical14880 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2577 + difference 2 4) (sourceB2577 + difference 4 2) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA2577 + difference 2 4) (sourceB2577 + difference 4 2) sourceC2577) = raw35642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35642; decide +kernel
    rw [ha]
    exact (canonical35642 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2577 + difference 2 5) (sourceB2577 + difference 5 2) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA2577 + difference 2 5) (sourceB2577 + difference 5 2) sourceC2577) = raw35643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35643; decide +kernel
    rw [ha]
    exact (canonical35643 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2577 + difference 3 0) (sourceB2577 + difference 0 3) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4978) := by
    have ha : (tripleCharges (sourceA2577 + difference 3 0) (sourceB2577 + difference 0 3) sourceC2577) = raw32107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw32107; decide +kernel
    rw [ha]
    exact (canonical32107 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2577 + difference 3 1) (sourceB2577 + difference 1 3) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4674) := by
    have ha : (tripleCharges (sourceA2577 + difference 3 1) (sourceB2577 + difference 1 3) sourceC2577) = raw35644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35644; decide +kernel
    rw [ha]
    exact (canonical35644 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2577 + difference 3 2) (sourceB2577 + difference 2 3) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5318) := by
    have ha : (tripleCharges (sourceA2577 + difference 3 2) (sourceB2577 + difference 2 3) sourceC2577) = raw35645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35645; decide +kernel
    rw [ha]
    exact (canonical35645 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2577 + difference 3 4) (sourceB2577 + difference 4 3) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5329) := by
    have ha : (tripleCharges (sourceA2577 + difference 3 4) (sourceB2577 + difference 4 3) sourceC2577) = raw35646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35646; decide +kernel
    rw [ha]
    exact (canonical35646 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2577 + difference 3 5) (sourceB2577 + difference 5 3) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2577 + difference 3 5) (sourceB2577 + difference 5 3) sourceC2577) = raw35647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35647; decide +kernel
    rw [ha]
    exact (canonical35647 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2577 + difference 4 0) (sourceB2577 + difference 0 4) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2577 + difference 4 0) (sourceB2577 + difference 0 4) sourceC2577) = raw32111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw32111; decide +kernel
    rw [ha]
    exact (canonical32111 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2577 + difference 4 1) (sourceB2577 + difference 1 4) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2577 + difference 4 1) (sourceB2577 + difference 1 4) sourceC2577) = raw35648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35648; decide +kernel
    rw [ha]
    exact (canonical35648 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2577 + difference 4 2) (sourceB2577 + difference 2 4) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5372) := by
    have ha : (tripleCharges (sourceA2577 + difference 4 2) (sourceB2577 + difference 2 4) sourceC2577) = raw35649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35649; decide +kernel
    rw [ha]
    exact (canonical35649 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2577 + difference 4 3) (sourceB2577 + difference 3 4) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5389) := by
    have ha : (tripleCharges (sourceA2577 + difference 4 3) (sourceB2577 + difference 3 4) sourceC2577) = raw14886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw14886; decide +kernel
    rw [ha]
    exact (canonical14886 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2577 + difference 4 5) (sourceB2577 + difference 5 4) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2577 + difference 4 5) (sourceB2577 + difference 5 4) sourceC2577) = raw35650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35650; decide +kernel
    rw [ha]
    exact (canonical35650 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2577 + difference 5 0) (sourceB2577 + difference 0 5) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4727) := by
    have ha : (tripleCharges (sourceA2577 + difference 5 0) (sourceB2577 + difference 0 5) sourceC2577) = raw27670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw27670; decide +kernel
    rw [ha]
    exact (canonical27670 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2577 + difference 5 1) (sourceB2577 + difference 1 5) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4673) := by
    have ha : (tripleCharges (sourceA2577 + difference 5 1) (sourceB2577 + difference 1 5) sourceC2577) = raw35651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35651; decide +kernel
    rw [ha]
    exact (canonical35651 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2577 + difference 5 2) (sourceB2577 + difference 2 5) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4724) := by
    have ha : (tripleCharges (sourceA2577 + difference 5 2) (sourceB2577 + difference 2 5) sourceC2577) = raw35652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35652; decide +kernel
    rw [ha]
    exact (canonical35652 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2577 + difference 5 3) (sourceB2577 + difference 3 5) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2577 + difference 5 3) (sourceB2577 + difference 3 5) sourceC2577) = raw14890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw14890; decide +kernel
    rw [ha]
    exact (canonical14890 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2577 + difference 5 4) (sourceB2577 + difference 4 5) sourceC2577) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4749) := by
    have ha : (tripleCharges (sourceA2577 + difference 5 4) (sourceB2577 + difference 4 5) sourceC2577) = raw35653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2577 sourceB2577 sourceC2577 difference raw35653; decide +kernel
    rw [ha]
    exact (canonical35653 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2577 sourceB2577 sourceC2577
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2577, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2578 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2578 : Charge := ![0, 2, 0, -1, 1, -2]
def sourceC2578 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm2578 : Integer.Sparse Master := [(Sum.inr 1798, 1), (Sum.inr 1799, 1), (Sum.inr 1800, 1), (Sum.inr 1814, 1), (Sum.inr 1878, 1), (Sum.inr 1881, 1), (Sum.inr 1928, 1), (Sum.inr 2101, 1), (Sum.inr 2115, 1), (Sum.inr 2804, 1), (Sum.inr 2805, 1), (Sum.inr 2817, 1), (Sum.inr 2954, 1), (Sum.inr 3641, 1), (Sum.inr 3660, 1), (Sum.inr 3708, 1), (Sum.inr 3713, 1), (Sum.inr 3731, 1), (Sum.inr 3732, 2), (Sum.inr 3739, 1), (Sum.inr 3740, 1), (Sum.inr 3784, 1), (Sum.inr 3789, 1), (Sum.inr 3811, 1), (Sum.inr 3814, 1), (Sum.inr 3885, 1), (Sum.inr 3886, 1), (Sum.inr 3889, 1), (Sum.inr 4012, 1)]

theorem sourceEq2578 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2578 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2578 + difference 0 1) (sourceB2578 + difference 1 0) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2101) := by
    have ha : (tripleCharges (sourceA2578 + difference 0 1) (sourceB2578 + difference 1 0) sourceC2578) = raw35654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35654; decide +kernel
    rw [ha]
    exact (canonical35654 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2578 + difference 0 2) (sourceB2578 + difference 2 0) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3784) := by
    have ha : (tripleCharges (sourceA2578 + difference 0 2) (sourceB2578 + difference 2 0) sourceC2578) = raw35655 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35655; decide +kernel
    rw [ha]
    exact (canonical35655 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2578 + difference 0 3) (sourceB2578 + difference 3 0) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA2578 + difference 0 3) (sourceB2578 + difference 3 0) sourceC2578) = raw14893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw14893; decide +kernel
    rw [ha]
    exact (canonical14893 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2578 + difference 0 4) (sourceB2578 + difference 4 0) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA2578 + difference 0 4) (sourceB2578 + difference 4 0) sourceC2578) = raw35656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35656; decide +kernel
    rw [ha]
    exact (canonical35656 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2578 + difference 0 5) (sourceB2578 + difference 5 0) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA2578 + difference 0 5) (sourceB2578 + difference 5 0) sourceC2578) = raw35657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35657; decide +kernel
    rw [ha]
    exact (canonical35657 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2578 + difference 1 0) (sourceB2578 + difference 0 1) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2578 + difference 1 0) (sourceB2578 + difference 0 1) sourceC2578) = raw7588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw7588; decide +kernel
    rw [ha]
    exact (canonical7588 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2578 + difference 1 2) (sourceB2578 + difference 2 1) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3789) := by
    have ha : (tripleCharges (sourceA2578 + difference 1 2) (sourceB2578 + difference 2 1) sourceC2578) = raw14903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw14903; decide +kernel
    rw [ha]
    exact (canonical14903 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2578 + difference 1 3) (sourceB2578 + difference 3 1) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA2578 + difference 1 3) (sourceB2578 + difference 3 1) sourceC2578) = raw7575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw7575; decide +kernel
    rw [ha]
    exact (canonical7575 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2578 + difference 1 4) (sourceB2578 + difference 4 1) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA2578 + difference 1 4) (sourceB2578 + difference 4 1) sourceC2578) = raw14904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw14904; decide +kernel
    rw [ha]
    exact (canonical14904 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2578 + difference 1 5) (sourceB2578 + difference 5 1) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA2578 + difference 1 5) (sourceB2578 + difference 5 1) sourceC2578) = raw14905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw14905; decide +kernel
    rw [ha]
    exact (canonical14905 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2578 + difference 2 0) (sourceB2578 + difference 0 2) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2804) := by
    have ha : (tripleCharges (sourceA2578 + difference 2 0) (sourceB2578 + difference 0 2) sourceC2578) = raw32114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw32114; decide +kernel
    rw [ha]
    exact (canonical32114 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2578 + difference 2 1) (sourceB2578 + difference 1 2) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1798) := by
    have ha : (tripleCharges (sourceA2578 + difference 2 1) (sourceB2578 + difference 1 2) sourceC2578) = raw35658 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35658; decide +kernel
    rw [ha]
    exact (canonical35658 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2578 + difference 2 3) (sourceB2578 + difference 3 2) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA2578 + difference 2 3) (sourceB2578 + difference 3 2) sourceC2578) = raw14898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw14898; decide +kernel
    rw [ha]
    exact (canonical14898 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2578 + difference 2 4) (sourceB2578 + difference 4 2) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3713) := by
    have ha : (tripleCharges (sourceA2578 + difference 2 4) (sourceB2578 + difference 4 2) sourceC2578) = raw35659 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35659; decide +kernel
    rw [ha]
    exact (canonical35659 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2578 + difference 2 5) (sourceB2578 + difference 5 2) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3731) := by
    have ha : (tripleCharges (sourceA2578 + difference 2 5) (sourceB2578 + difference 5 2) sourceC2578) = raw35660 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35660; decide +kernel
    rw [ha]
    exact (canonical35660 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2578 + difference 3 0) (sourceB2578 + difference 0 3) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2805) := by
    have ha : (tripleCharges (sourceA2578 + difference 3 0) (sourceB2578 + difference 0 3) sourceC2578) = raw32117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw32117; decide +kernel
    rw [ha]
    exact (canonical32117 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2578 + difference 3 1) (sourceB2578 + difference 1 3) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1800) := by
    have ha : (tripleCharges (sourceA2578 + difference 3 1) (sourceB2578 + difference 1 3) sourceC2578) = raw35661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35661; decide +kernel
    rw [ha]
    exact (canonical35661 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2578 + difference 3 2) (sourceB2578 + difference 2 3) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3641) := by
    have ha : (tripleCharges (sourceA2578 + difference 3 2) (sourceB2578 + difference 2 3) sourceC2578) = raw35662 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35662; decide +kernel
    rw [ha]
    exact (canonical35662 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2578 + difference 3 4) (sourceB2578 + difference 4 3) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3660) := by
    have ha : (tripleCharges (sourceA2578 + difference 3 4) (sourceB2578 + difference 4 3) sourceC2578) = raw35663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35663; decide +kernel
    rw [ha]
    exact (canonical35663 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2578 + difference 3 5) (sourceB2578 + difference 5 3) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA2578 + difference 3 5) (sourceB2578 + difference 5 3) sourceC2578) = raw35664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35664; decide +kernel
    rw [ha]
    exact (canonical35664 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2578 + difference 4 0) (sourceB2578 + difference 0 4) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2817) := by
    have ha : (tripleCharges (sourceA2578 + difference 4 0) (sourceB2578 + difference 0 4) sourceC2578) = raw32121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw32121; decide +kernel
    rw [ha]
    exact (canonical32121 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2578 + difference 4 1) (sourceB2578 + difference 1 4) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1814) := by
    have ha : (tripleCharges (sourceA2578 + difference 4 1) (sourceB2578 + difference 1 4) sourceC2578) = raw35665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35665; decide +kernel
    rw [ha]
    exact (canonical35665 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2578 + difference 4 2) (sourceB2578 + difference 2 4) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3708) := by
    have ha : (tripleCharges (sourceA2578 + difference 4 2) (sourceB2578 + difference 2 4) sourceC2578) = raw35666 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35666; decide +kernel
    rw [ha]
    exact (canonical35666 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2578 + difference 4 3) (sourceB2578 + difference 3 4) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3740) := by
    have ha : (tripleCharges (sourceA2578 + difference 4 3) (sourceB2578 + difference 3 4) sourceC2578) = raw14906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw14906; decide +kernel
    rw [ha]
    exact (canonical14906 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2578 + difference 4 5) (sourceB2578 + difference 5 4) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3739) := by
    have ha : (tripleCharges (sourceA2578 + difference 4 5) (sourceB2578 + difference 5 4) sourceC2578) = raw35667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35667; decide +kernel
    rw [ha]
    exact (canonical35667 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2578 + difference 5 0) (sourceB2578 + difference 0 5) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1881) := by
    have ha : (tripleCharges (sourceA2578 + difference 5 0) (sourceB2578 + difference 0 5) sourceC2578) = raw27680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw27680; decide +kernel
    rw [ha]
    exact (canonical27680 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2578 + difference 5 1) (sourceB2578 + difference 1 5) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1799) := by
    have ha : (tripleCharges (sourceA2578 + difference 5 1) (sourceB2578 + difference 1 5) sourceC2578) = raw35668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35668; decide +kernel
    rw [ha]
    exact (canonical35668 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2578 + difference 5 2) (sourceB2578 + difference 2 5) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1878) := by
    have ha : (tripleCharges (sourceA2578 + difference 5 2) (sourceB2578 + difference 2 5) sourceC2578) = raw35669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35669; decide +kernel
    rw [ha]
    exact (canonical35669 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2578 + difference 5 3) (sourceB2578 + difference 3 5) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA2578 + difference 5 3) (sourceB2578 + difference 3 5) sourceC2578) = raw14910 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw14910; decide +kernel
    rw [ha]
    exact (canonical14910 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2578 + difference 5 4) (sourceB2578 + difference 4 5) sourceC2578) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1928) := by
    have ha : (tripleCharges (sourceA2578 + difference 5 4) (sourceB2578 + difference 4 5) sourceC2578) = raw35670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2578 sourceB2578 sourceC2578 difference raw35670; decide +kernel
    rw [ha]
    exact (canonical35670 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2578 sourceB2578 sourceC2578
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2578, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2579 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2579 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2579 : Charge := ![0, 2, 0, -1, 1, -2]
def sourceForm2579 : Integer.Sparse Master := [(Sum.inr 4680, 1), (Sum.inr 4682, 1), (Sum.inr 4683, 1), (Sum.inr 4690, 1), (Sum.inr 4867, 1), (Sum.inr 4963, 1), (Sum.inr 4965, 1), (Sum.inr 4966, 1), (Sum.inr 4976, 1), (Sum.inr 5042, 1), (Sum.inr 5080, 1), (Sum.inr 5163, 1), (Sum.inr 5188, 1), (Sum.inr 5216, 1), (Sum.inr 5232, 1), (Sum.inr 5264, 1), (Sum.inr 5339, 1), (Sum.inr 5355, 1), (Sum.inr 5378, 1), (Sum.inr 5381, 1), (Sum.inr 5382, 1), (Sum.inr 5385, 1), (Sum.inr 5400, 1), (Sum.inr 5402, 1), (Sum.inr 5409, 1), (Sum.inr 5411, 1), (Sum.inr 5432, 1), (Sum.inr 5436, 1), (Sum.inr 5438, 1), (Sum.inr 5446, 1)]

theorem sourceEq2579 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2579 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2579 + difference 0 1) (sourceB2579 + difference 1 0) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2579 + difference 0 1) (sourceB2579 + difference 1 0) sourceC2579) = raw35671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35671; decide +kernel
    rw [ha]
    exact (canonical35671 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2579 + difference 0 2) (sourceB2579 + difference 2 0) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA2579 + difference 0 2) (sourceB2579 + difference 2 0) sourceC2579) = raw35672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35672; decide +kernel
    rw [ha]
    exact (canonical35672 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2579 + difference 0 3) (sourceB2579 + difference 3 0) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA2579 + difference 0 3) (sourceB2579 + difference 3 0) sourceC2579) = raw35673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35673; decide +kernel
    rw [ha]
    exact (canonical35673 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2579 + difference 0 4) (sourceB2579 + difference 4 0) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2579 + difference 0 4) (sourceB2579 + difference 4 0) sourceC2579) = raw35674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35674; decide +kernel
    rw [ha]
    exact (canonical35674 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2579 + difference 0 5) (sourceB2579 + difference 5 0) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2579 + difference 0 5) (sourceB2579 + difference 5 0) sourceC2579) = raw35675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35675; decide +kernel
    rw [ha]
    exact (canonical35675 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2579 + difference 1 0) (sourceB2579 + difference 0 1) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA2579 + difference 1 0) (sourceB2579 + difference 0 1) sourceC2579) = raw35676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35676; decide +kernel
    rw [ha]
    exact (canonical35676 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2579 + difference 1 2) (sourceB2579 + difference 2 1) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5402) := by
    have ha : (tripleCharges (sourceA2579 + difference 1 2) (sourceB2579 + difference 2 1) sourceC2579) = raw35677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35677; decide +kernel
    rw [ha]
    exact (canonical35677 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2579 + difference 1 3) (sourceB2579 + difference 3 1) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA2579 + difference 1 3) (sourceB2579 + difference 3 1) sourceC2579) = raw35678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35678; decide +kernel
    rw [ha]
    exact (canonical35678 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2579 + difference 1 4) (sourceB2579 + difference 4 1) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA2579 + difference 1 4) (sourceB2579 + difference 4 1) sourceC2579) = raw35679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35679; decide +kernel
    rw [ha]
    exact (canonical35679 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2579 + difference 1 5) (sourceB2579 + difference 5 1) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA2579 + difference 1 5) (sourceB2579 + difference 5 1) sourceC2579) = raw35680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35680; decide +kernel
    rw [ha]
    exact (canonical35680 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2579 + difference 2 0) (sourceB2579 + difference 0 2) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4680) := by
    have ha : (tripleCharges (sourceA2579 + difference 2 0) (sourceB2579 + difference 0 2) sourceC2579) = raw35681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35681; decide +kernel
    rw [ha]
    exact (canonical35681 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2579 + difference 2 1) (sourceB2579 + difference 1 2) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4963) := by
    have ha : (tripleCharges (sourceA2579 + difference 2 1) (sourceB2579 + difference 1 2) sourceC2579) = raw35682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35682; decide +kernel
    rw [ha]
    exact (canonical35682 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2579 + difference 2 3) (sourceB2579 + difference 3 2) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA2579 + difference 2 3) (sourceB2579 + difference 3 2) sourceC2579) = raw35683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35683; decide +kernel
    rw [ha]
    exact (canonical35683 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2579 + difference 2 4) (sourceB2579 + difference 4 2) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2579 + difference 2 4) (sourceB2579 + difference 4 2) sourceC2579) = raw35684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35684; decide +kernel
    rw [ha]
    exact (canonical35684 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2579 + difference 2 5) (sourceB2579 + difference 5 2) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5382) := by
    have ha : (tripleCharges (sourceA2579 + difference 2 5) (sourceB2579 + difference 5 2) sourceC2579) = raw35685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35685; decide +kernel
    rw [ha]
    exact (canonical35685 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2579 + difference 3 0) (sourceB2579 + difference 0 3) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4690) := by
    have ha : (tripleCharges (sourceA2579 + difference 3 0) (sourceB2579 + difference 0 3) sourceC2579) = raw35686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35686; decide +kernel
    rw [ha]
    exact (canonical35686 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2579 + difference 3 1) (sourceB2579 + difference 1 3) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4966) := by
    have ha : (tripleCharges (sourceA2579 + difference 3 1) (sourceB2579 + difference 1 3) sourceC2579) = raw35687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35687; decide +kernel
    rw [ha]
    exact (canonical35687 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2579 + difference 3 2) (sourceB2579 + difference 2 3) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5339) := by
    have ha : (tripleCharges (sourceA2579 + difference 3 2) (sourceB2579 + difference 2 3) sourceC2579) = raw35688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35688; decide +kernel
    rw [ha]
    exact (canonical35688 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2579 + difference 3 4) (sourceB2579 + difference 4 3) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2579 + difference 3 4) (sourceB2579 + difference 4 3) sourceC2579) = raw35689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35689; decide +kernel
    rw [ha]
    exact (canonical35689 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2579 + difference 3 5) (sourceB2579 + difference 5 3) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5385) := by
    have ha : (tripleCharges (sourceA2579 + difference 3 5) (sourceB2579 + difference 5 3) sourceC2579) = raw35690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35690; decide +kernel
    rw [ha]
    exact (canonical35690 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2579 + difference 4 0) (sourceB2579 + difference 0 4) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4683) := by
    have ha : (tripleCharges (sourceA2579 + difference 4 0) (sourceB2579 + difference 0 4) sourceC2579) = raw35691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35691; decide +kernel
    rw [ha]
    exact (canonical35691 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2579 + difference 4 1) (sourceB2579 + difference 1 4) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4976) := by
    have ha : (tripleCharges (sourceA2579 + difference 4 1) (sourceB2579 + difference 1 4) sourceC2579) = raw35692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35692; decide +kernel
    rw [ha]
    exact (canonical35692 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2579 + difference 4 2) (sourceB2579 + difference 2 4) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5216) := by
    have ha : (tripleCharges (sourceA2579 + difference 4 2) (sourceB2579 + difference 2 4) sourceC2579) = raw35693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35693; decide +kernel
    rw [ha]
    exact (canonical35693 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2579 + difference 4 3) (sourceB2579 + difference 3 4) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2579 + difference 4 3) (sourceB2579 + difference 3 4) sourceC2579) = raw35694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35694; decide +kernel
    rw [ha]
    exact (canonical35694 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2579 + difference 4 5) (sourceB2579 + difference 5 4) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA2579 + difference 4 5) (sourceB2579 + difference 5 4) sourceC2579) = raw35695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35695; decide +kernel
    rw [ha]
    exact (canonical35695 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2579 + difference 5 0) (sourceB2579 + difference 0 5) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4682) := by
    have ha : (tripleCharges (sourceA2579 + difference 5 0) (sourceB2579 + difference 0 5) sourceC2579) = raw35696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35696; decide +kernel
    rw [ha]
    exact (canonical35696 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2579 + difference 5 1) (sourceB2579 + difference 1 5) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4965) := by
    have ha : (tripleCharges (sourceA2579 + difference 5 1) (sourceB2579 + difference 1 5) sourceC2579) = raw35697 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35697; decide +kernel
    rw [ha]
    exact (canonical35697 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2579 + difference 5 2) (sourceB2579 + difference 2 5) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5042) := by
    have ha : (tripleCharges (sourceA2579 + difference 5 2) (sourceB2579 + difference 2 5) sourceC2579) = raw35698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35698; decide +kernel
    rw [ha]
    exact (canonical35698 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2579 + difference 5 3) (sourceB2579 + difference 3 5) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA2579 + difference 5 3) (sourceB2579 + difference 3 5) sourceC2579) = raw35699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35699; decide +kernel
    rw [ha]
    exact (canonical35699 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2579 + difference 5 4) (sourceB2579 + difference 4 5) sourceC2579) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2579 + difference 5 4) (sourceB2579 + difference 4 5) sourceC2579) = raw35700 := by
      apply Matrix.ext; unfold tripleCharges sourceA2579 sourceB2579 sourceC2579 difference raw35700; decide +kernel
    rw [ha]
    exact (canonical35700 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2579 sourceB2579 sourceC2579
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2579, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2580 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2580 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2580 : Charge := ![0, 2, 0, -1, 1, -2]
def sourceForm2580 : Integer.Sparse Master := [(Sum.inr 2145, 1), (Sum.inr 2146, 1), (Sum.inr 2153, 1), (Sum.inr 2158, 1), (Sum.inr 2251, 1), (Sum.inr 2654, 1), (Sum.inr 2659, 1), (Sum.inr 2677, 1), (Sum.inr 2729, 1), (Sum.inr 3462, 1), (Sum.inr 3475, 1), (Sum.inr 3478, 1), (Sum.inr 3538, 1), (Sum.inr 3553, 1), (Sum.inr 3555, 1), (Sum.inr 3564, 1), (Sum.inr 3760, 1), (Sum.inr 3770, 1), (Sum.inr 3795, 1), (Sum.inr 3799, 1), (Sum.inr 3802, 1), (Sum.inr 3807, 1), (Sum.inr 3813, 1), (Sum.inr 3834, 1), (Sum.inr 3850, 1), (Sum.inr 3854, 1), (Sum.inr 3866, 1), (Sum.inr 3868, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1)]

theorem sourceEq2580 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2580 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2580 + difference 0 1) (sourceB2580 + difference 1 0) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2580 + difference 0 1) (sourceB2580 + difference 1 0) sourceC2580) = raw35701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35701; decide +kernel
    rw [ha]
    exact (canonical35701 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2580 + difference 0 2) (sourceB2580 + difference 2 0) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA2580 + difference 0 2) (sourceB2580 + difference 2 0) sourceC2580) = raw35702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35702; decide +kernel
    rw [ha]
    exact (canonical35702 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2580 + difference 0 3) (sourceB2580 + difference 3 0) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA2580 + difference 0 3) (sourceB2580 + difference 3 0) sourceC2580) = raw35703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35703; decide +kernel
    rw [ha]
    exact (canonical35703 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2580 + difference 0 4) (sourceB2580 + difference 4 0) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2580 + difference 0 4) (sourceB2580 + difference 4 0) sourceC2580) = raw35704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35704; decide +kernel
    rw [ha]
    exact (canonical35704 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2580 + difference 0 5) (sourceB2580 + difference 5 0) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA2580 + difference 0 5) (sourceB2580 + difference 5 0) sourceC2580) = raw35705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35705; decide +kernel
    rw [ha]
    exact (canonical35705 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2580 + difference 1 0) (sourceB2580 + difference 0 1) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA2580 + difference 1 0) (sourceB2580 + difference 0 1) sourceC2580) = raw35706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35706; decide +kernel
    rw [ha]
    exact (canonical35706 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2580 + difference 1 2) (sourceB2580 + difference 2 1) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA2580 + difference 1 2) (sourceB2580 + difference 2 1) sourceC2580) = raw35707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35707; decide +kernel
    rw [ha]
    exact (canonical35707 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2580 + difference 1 3) (sourceB2580 + difference 3 1) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA2580 + difference 1 3) (sourceB2580 + difference 3 1) sourceC2580) = raw35708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35708; decide +kernel
    rw [ha]
    exact (canonical35708 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2580 + difference 1 4) (sourceB2580 + difference 4 1) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA2580 + difference 1 4) (sourceB2580 + difference 4 1) sourceC2580) = raw35709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35709; decide +kernel
    rw [ha]
    exact (canonical35709 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2580 + difference 1 5) (sourceB2580 + difference 5 1) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA2580 + difference 1 5) (sourceB2580 + difference 5 1) sourceC2580) = raw35710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35710; decide +kernel
    rw [ha]
    exact (canonical35710 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2580 + difference 2 0) (sourceB2580 + difference 0 2) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2145) := by
    have ha : (tripleCharges (sourceA2580 + difference 2 0) (sourceB2580 + difference 0 2) sourceC2580) = raw35711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35711; decide +kernel
    rw [ha]
    exact (canonical35711 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2580 + difference 2 1) (sourceB2580 + difference 1 2) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3553) := by
    have ha : (tripleCharges (sourceA2580 + difference 2 1) (sourceB2580 + difference 1 2) sourceC2580) = raw35712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35712; decide +kernel
    rw [ha]
    exact (canonical35712 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2580 + difference 2 3) (sourceB2580 + difference 3 2) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA2580 + difference 2 3) (sourceB2580 + difference 3 2) sourceC2580) = raw35713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35713; decide +kernel
    rw [ha]
    exact (canonical35713 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2580 + difference 2 4) (sourceB2580 + difference 4 2) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA2580 + difference 2 4) (sourceB2580 + difference 4 2) sourceC2580) = raw35714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35714; decide +kernel
    rw [ha]
    exact (canonical35714 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2580 + difference 2 5) (sourceB2580 + difference 5 2) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA2580 + difference 2 5) (sourceB2580 + difference 5 2) sourceC2580) = raw35715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35715; decide +kernel
    rw [ha]
    exact (canonical35715 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2580 + difference 3 0) (sourceB2580 + difference 0 3) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2158) := by
    have ha : (tripleCharges (sourceA2580 + difference 3 0) (sourceB2580 + difference 0 3) sourceC2580) = raw35716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35716; decide +kernel
    rw [ha]
    exact (canonical35716 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2580 + difference 3 1) (sourceB2580 + difference 1 3) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3555) := by
    have ha : (tripleCharges (sourceA2580 + difference 3 1) (sourceB2580 + difference 1 3) sourceC2580) = raw35717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35717; decide +kernel
    rw [ha]
    exact (canonical35717 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2580 + difference 3 2) (sourceB2580 + difference 2 3) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3760) := by
    have ha : (tripleCharges (sourceA2580 + difference 3 2) (sourceB2580 + difference 2 3) sourceC2580) = raw35718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35718; decide +kernel
    rw [ha]
    exact (canonical35718 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2580 + difference 3 4) (sourceB2580 + difference 4 3) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2580 + difference 3 4) (sourceB2580 + difference 4 3) sourceC2580) = raw35719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35719; decide +kernel
    rw [ha]
    exact (canonical35719 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2580 + difference 3 5) (sourceB2580 + difference 5 3) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3868) := by
    have ha : (tripleCharges (sourceA2580 + difference 3 5) (sourceB2580 + difference 5 3) sourceC2580) = raw35720 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35720; decide +kernel
    rw [ha]
    exact (canonical35720 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2580 + difference 4 0) (sourceB2580 + difference 0 4) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2146) := by
    have ha : (tripleCharges (sourceA2580 + difference 4 0) (sourceB2580 + difference 0 4) sourceC2580) = raw35721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35721; decide +kernel
    rw [ha]
    exact (canonical35721 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2580 + difference 4 1) (sourceB2580 + difference 1 4) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2659) := by
    have ha : (tripleCharges (sourceA2580 + difference 4 1) (sourceB2580 + difference 1 4) sourceC2580) = raw35722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35722; decide +kernel
    rw [ha]
    exact (canonical35722 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2580 + difference 4 2) (sourceB2580 + difference 2 4) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2654) := by
    have ha : (tripleCharges (sourceA2580 + difference 4 2) (sourceB2580 + difference 2 4) sourceC2580) = raw35723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35723; decide +kernel
    rw [ha]
    exact (canonical35723 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2580 + difference 4 3) (sourceB2580 + difference 3 4) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA2580 + difference 4 3) (sourceB2580 + difference 3 4) sourceC2580) = raw35724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35724; decide +kernel
    rw [ha]
    exact (canonical35724 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2580 + difference 4 5) (sourceB2580 + difference 5 4) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA2580 + difference 4 5) (sourceB2580 + difference 5 4) sourceC2580) = raw35725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35725; decide +kernel
    rw [ha]
    exact (canonical35725 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2580 + difference 5 0) (sourceB2580 + difference 0 5) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2153) := by
    have ha : (tripleCharges (sourceA2580 + difference 5 0) (sourceB2580 + difference 0 5) sourceC2580) = raw35726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35726; decide +kernel
    rw [ha]
    exact (canonical35726 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2580 + difference 5 1) (sourceB2580 + difference 1 5) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3475) := by
    have ha : (tripleCharges (sourceA2580 + difference 5 1) (sourceB2580 + difference 1 5) sourceC2580) = raw35727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35727; decide +kernel
    rw [ha]
    exact (canonical35727 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2580 + difference 5 2) (sourceB2580 + difference 2 5) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3462) := by
    have ha : (tripleCharges (sourceA2580 + difference 5 2) (sourceB2580 + difference 2 5) sourceC2580) = raw35728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35728; decide +kernel
    rw [ha]
    exact (canonical35728 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2580 + difference 5 3) (sourceB2580 + difference 3 5) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2580 + difference 5 3) (sourceB2580 + difference 3 5) sourceC2580) = raw35729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35729; decide +kernel
    rw [ha]
    exact (canonical35729 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2580 + difference 5 4) (sourceB2580 + difference 4 5) sourceC2580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2580 + difference 5 4) (sourceB2580 + difference 4 5) sourceC2580) = raw35730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2580 sourceB2580 sourceC2580 difference raw35730; decide +kernel
    rw [ha]
    exact (canonical35730 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2580 sourceB2580 sourceC2580
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2580, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2581 : Charge := ![0, 2, 0, -1, 1, -2]
def sourceB2581 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2581 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceForm2581 : Integer.Sparse Master := [(Sum.inr 5082, 1), (Sum.inr 5084, 1), (Sum.inr 5089, 1), (Sum.inr 5095, 1), (Sum.inr 5178, 1), (Sum.inr 5180, 1), (Sum.inr 5195, 1), (Sum.inr 5223, 1), (Sum.inr 5224, 1), (Sum.inr 5225, 1), (Sum.inr 5228, 1), (Sum.inr 5229, 1), (Sum.inr 5233, 1), (Sum.inr 5234, 1), (Sum.inr 5264, 1), (Sum.inr 5287, 1), (Sum.inr 5349, 1), (Sum.inr 5353, 1), (Sum.inr 5357, 1), (Sum.inr 5364, 1), (Sum.inr 5367, 1), (Sum.inr 5368, 1), (Sum.inr 5370, 1), (Sum.inr 5378, 1), (Sum.inr 5379, 1), (Sum.inr 5381, 1), (Sum.inr 5385, 1), (Sum.inr 5387, 1), (Sum.inr 5388, 1), (Sum.inr 5404, 1)]

theorem sourceEq2581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2581 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2581 + difference 0 1) (sourceB2581 + difference 1 0) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2581 + difference 0 1) (sourceB2581 + difference 1 0) sourceC2581) = raw35731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35731; decide +kernel
    rw [ha]
    exact (canonical35731 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2581 + difference 0 2) (sourceB2581 + difference 2 0) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA2581 + difference 0 2) (sourceB2581 + difference 2 0) sourceC2581) = raw35732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35732; decide +kernel
    rw [ha]
    exact (canonical35732 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2581 + difference 0 3) (sourceB2581 + difference 3 0) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5364) := by
    have ha : (tripleCharges (sourceA2581 + difference 0 3) (sourceB2581 + difference 3 0) sourceC2581) = raw35733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35733; decide +kernel
    rw [ha]
    exact (canonical35733 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2581 + difference 0 4) (sourceB2581 + difference 4 0) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2581 + difference 0 4) (sourceB2581 + difference 4 0) sourceC2581) = raw35618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35618; decide +kernel
    rw [ha]
    exact (canonical35618 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2581 + difference 0 5) (sourceB2581 + difference 5 0) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA2581 + difference 0 5) (sourceB2581 + difference 5 0) sourceC2581) = raw35734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35734; decide +kernel
    rw [ha]
    exact (canonical35734 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2581 + difference 1 0) (sourceB2581 + difference 0 1) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5195) := by
    have ha : (tripleCharges (sourceA2581 + difference 1 0) (sourceB2581 + difference 0 1) sourceC2581) = raw35735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35735; decide +kernel
    rw [ha]
    exact (canonical35735 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2581 + difference 1 2) (sourceB2581 + difference 2 1) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5178) := by
    have ha : (tripleCharges (sourceA2581 + difference 1 2) (sourceB2581 + difference 2 1) sourceC2581) = raw35736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35736; decide +kernel
    rw [ha]
    exact (canonical35736 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2581 + difference 1 3) (sourceB2581 + difference 3 1) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5180) := by
    have ha : (tripleCharges (sourceA2581 + difference 1 3) (sourceB2581 + difference 3 1) sourceC2581) = raw35737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35737; decide +kernel
    rw [ha]
    exact (canonical35737 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2581 + difference 1 4) (sourceB2581 + difference 4 1) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2581 + difference 1 4) (sourceB2581 + difference 4 1) sourceC2581) = raw35622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35622; decide +kernel
    rw [ha]
    exact (canonical35622 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2581 + difference 1 5) (sourceB2581 + difference 5 1) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5084) := by
    have ha : (tripleCharges (sourceA2581 + difference 1 5) (sourceB2581 + difference 5 1) sourceC2581) = raw35738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35738; decide +kernel
    rw [ha]
    exact (canonical35738 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2581 + difference 2 0) (sourceB2581 + difference 0 2) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5223) := by
    have ha : (tripleCharges (sourceA2581 + difference 2 0) (sourceB2581 + difference 0 2) sourceC2581) = raw35739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35739; decide +kernel
    rw [ha]
    exact (canonical35739 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2581 + difference 2 1) (sourceB2581 + difference 1 2) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA2581 + difference 2 1) (sourceB2581 + difference 1 2) sourceC2581) = raw35740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35740; decide +kernel
    rw [ha]
    exact (canonical35740 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2581 + difference 2 3) (sourceB2581 + difference 3 2) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5357) := by
    have ha : (tripleCharges (sourceA2581 + difference 2 3) (sourceB2581 + difference 3 2) sourceC2581) = raw35741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35741; decide +kernel
    rw [ha]
    exact (canonical35741 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2581 + difference 2 4) (sourceB2581 + difference 4 2) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2581 + difference 2 4) (sourceB2581 + difference 4 2) sourceC2581) = raw35626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35626; decide +kernel
    rw [ha]
    exact (canonical35626 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2581 + difference 2 5) (sourceB2581 + difference 5 2) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5082) := by
    have ha : (tripleCharges (sourceA2581 + difference 2 5) (sourceB2581 + difference 5 2) sourceC2581) = raw35742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35742; decide +kernel
    rw [ha]
    exact (canonical35742 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2581 + difference 3 0) (sourceB2581 + difference 0 3) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA2581 + difference 3 0) (sourceB2581 + difference 0 3) sourceC2581) = raw35743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35743; decide +kernel
    rw [ha]
    exact (canonical35743 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2581 + difference 3 1) (sourceB2581 + difference 1 3) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2581 + difference 3 1) (sourceB2581 + difference 1 3) sourceC2581) = raw35744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35744; decide +kernel
    rw [ha]
    exact (canonical35744 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2581 + difference 3 2) (sourceB2581 + difference 2 3) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA2581 + difference 3 2) (sourceB2581 + difference 2 3) sourceC2581) = raw35745 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35745; decide +kernel
    rw [ha]
    exact (canonical35745 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2581 + difference 3 4) (sourceB2581 + difference 4 3) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2581 + difference 3 4) (sourceB2581 + difference 4 3) sourceC2581) = raw35630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35630; decide +kernel
    rw [ha]
    exact (canonical35630 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2581 + difference 3 5) (sourceB2581 + difference 5 3) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA2581 + difference 3 5) (sourceB2581 + difference 5 3) sourceC2581) = raw35746 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35746; decide +kernel
    rw [ha]
    exact (canonical35746 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2581 + difference 4 0) (sourceB2581 + difference 0 4) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5225) := by
    have ha : (tripleCharges (sourceA2581 + difference 4 0) (sourceB2581 + difference 0 4) sourceC2581) = raw35747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35747; decide +kernel
    rw [ha]
    exact (canonical35747 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2581 + difference 4 1) (sourceB2581 + difference 1 4) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA2581 + difference 4 1) (sourceB2581 + difference 1 4) sourceC2581) = raw35748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35748; decide +kernel
    rw [ha]
    exact (canonical35748 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2581 + difference 4 2) (sourceB2581 + difference 2 4) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5224) := by
    have ha : (tripleCharges (sourceA2581 + difference 4 2) (sourceB2581 + difference 2 4) sourceC2581) = raw35749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35749; decide +kernel
    rw [ha]
    exact (canonical35749 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2581 + difference 4 3) (sourceB2581 + difference 3 4) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5234) := by
    have ha : (tripleCharges (sourceA2581 + difference 4 3) (sourceB2581 + difference 3 4) sourceC2581) = raw35750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35750; decide +kernel
    rw [ha]
    exact (canonical35750 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2581 + difference 4 5) (sourceB2581 + difference 5 4) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5089) := by
    have ha : (tripleCharges (sourceA2581 + difference 4 5) (sourceB2581 + difference 5 4) sourceC2581) = raw35751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35751; decide +kernel
    rw [ha]
    exact (canonical35751 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2581 + difference 5 0) (sourceB2581 + difference 0 5) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA2581 + difference 5 0) (sourceB2581 + difference 0 5) sourceC2581) = raw35631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35631; decide +kernel
    rw [ha]
    exact (canonical35631 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2581 + difference 5 1) (sourceB2581 + difference 1 5) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2581 + difference 5 1) (sourceB2581 + difference 1 5) sourceC2581) = raw35632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35632; decide +kernel
    rw [ha]
    exact (canonical35632 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2581 + difference 5 2) (sourceB2581 + difference 2 5) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2581 + difference 5 2) (sourceB2581 + difference 2 5) sourceC2581) = raw35633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35633; decide +kernel
    rw [ha]
    exact (canonical35633 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2581 + difference 5 3) (sourceB2581 + difference 3 5) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5385) := by
    have ha : (tripleCharges (sourceA2581 + difference 5 3) (sourceB2581 + difference 3 5) sourceC2581) = raw35634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35634; decide +kernel
    rw [ha]
    exact (canonical35634 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2581 + difference 5 4) (sourceB2581 + difference 4 5) sourceC2581) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2581 + difference 5 4) (sourceB2581 + difference 4 5) sourceC2581) = raw35596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2581 sourceB2581 sourceC2581 difference raw35596; decide +kernel
    rw [ha]
    exact (canonical35596 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2581 sourceB2581 sourceC2581
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2581, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2582 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2582 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceC2582 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceForm2582 : Integer.Sparse Master := [(Sum.inr 4660, 1), (Sum.inr 4661, 2), (Sum.inr 4679, 1), (Sum.inr 4826, 1), (Sum.inr 4960, 1), (Sum.inr 4961, 2), (Sum.inr 4968, 1), (Sum.inr 5030, 1), (Sum.inr 5080, 2), (Sum.inr 5148, 1), (Sum.inr 5333, 2), (Sum.inr 5355, 2), (Sum.inr 5363, 1), (Sum.inr 5378, 2), (Sum.inr 5386, 1), (Sum.inr 5388, 2), (Sum.inr 5422, 1), (Sum.inr 5431, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 2), (Sum.inr 5438, 2)]

theorem sourceEq2582 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2582 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2582 + difference 0 1) (sourceB2582 + difference 1 0) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA2582 + difference 0 1) (sourceB2582 + difference 1 0) sourceC2582) = raw35752 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35752; decide +kernel
    rw [ha]
    exact (canonical35752 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2582 + difference 0 2) (sourceB2582 + difference 2 0) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5363) := by
    have ha : (tripleCharges (sourceA2582 + difference 0 2) (sourceB2582 + difference 2 0) sourceC2582) = raw35753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35753; decide +kernel
    rw [ha]
    exact (canonical35753 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2582 + difference 0 3) (sourceB2582 + difference 3 0) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2582 + difference 0 3) (sourceB2582 + difference 3 0) sourceC2582) = raw35754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35754; decide +kernel
    rw [ha]
    exact (canonical35754 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2582 + difference 0 4) (sourceB2582 + difference 4 0) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2582 + difference 0 4) (sourceB2582 + difference 4 0) sourceC2582) = raw35755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35755; decide +kernel
    rw [ha]
    exact (canonical35755 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2582 + difference 0 5) (sourceB2582 + difference 5 0) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA2582 + difference 0 5) (sourceB2582 + difference 5 0) sourceC2582) = raw18359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw18359; decide +kernel
    rw [ha]
    exact (canonical18359 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2582 + difference 1 0) (sourceB2582 + difference 0 1) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA2582 + difference 1 0) (sourceB2582 + difference 0 1) sourceC2582) = raw12557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw12557; decide +kernel
    rw [ha]
    exact (canonical12557 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2582 + difference 1 2) (sourceB2582 + difference 2 1) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA2582 + difference 1 2) (sourceB2582 + difference 2 1) sourceC2582) = raw18378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw18378; decide +kernel
    rw [ha]
    exact (canonical18378 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2582 + difference 1 3) (sourceB2582 + difference 3 1) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2582 + difference 1 3) (sourceB2582 + difference 3 1) sourceC2582) = raw18379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw18379; decide +kernel
    rw [ha]
    exact (canonical18379 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2582 + difference 1 4) (sourceB2582 + difference 4 1) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2582 + difference 1 4) (sourceB2582 + difference 4 1) sourceC2582) = raw18380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw18380; decide +kernel
    rw [ha]
    exact (canonical18380 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2582 + difference 1 5) (sourceB2582 + difference 5 1) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2582 + difference 1 5) (sourceB2582 + difference 5 1) sourceC2582) = raw12531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw12531; decide +kernel
    rw [ha]
    exact (canonical12531 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2582 + difference 2 0) (sourceB2582 + difference 0 2) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4968) := by
    have ha : (tripleCharges (sourceA2582 + difference 2 0) (sourceB2582 + difference 0 2) sourceC2582) = raw32282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw32282; decide +kernel
    rw [ha]
    exact (canonical32282 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2582 + difference 2 1) (sourceB2582 + difference 1 2) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2582 + difference 2 1) (sourceB2582 + difference 1 2) sourceC2582) = raw35756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35756; decide +kernel
    rw [ha]
    exact (canonical35756 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2582 + difference 2 3) (sourceB2582 + difference 3 2) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2582 + difference 2 3) (sourceB2582 + difference 3 2) sourceC2582) = raw35757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35757; decide +kernel
    rw [ha]
    exact (canonical35757 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2582 + difference 2 4) (sourceB2582 + difference 4 2) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2582 + difference 2 4) (sourceB2582 + difference 4 2) sourceC2582) = raw35758 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35758; decide +kernel
    rw [ha]
    exact (canonical35758 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2582 + difference 2 5) (sourceB2582 + difference 5 2) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5386) := by
    have ha : (tripleCharges (sourceA2582 + difference 2 5) (sourceB2582 + difference 5 2) sourceC2582) = raw18365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw18365; decide +kernel
    rw [ha]
    exact (canonical18365 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2582 + difference 3 0) (sourceB2582 + difference 0 3) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4961) := by
    have ha : (tripleCharges (sourceA2582 + difference 3 0) (sourceB2582 + difference 0 3) sourceC2582) = raw32285 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw32285; decide +kernel
    rw [ha]
    exact (canonical32285 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2582 + difference 3 1) (sourceB2582 + difference 1 3) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4661) := by
    have ha : (tripleCharges (sourceA2582 + difference 3 1) (sourceB2582 + difference 1 3) sourceC2582) = raw35759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35759; decide +kernel
    rw [ha]
    exact (canonical35759 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2582 + difference 3 2) (sourceB2582 + difference 2 3) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5333) := by
    have ha : (tripleCharges (sourceA2582 + difference 3 2) (sourceB2582 + difference 2 3) sourceC2582) = raw35760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35760; decide +kernel
    rw [ha]
    exact (canonical35760 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2582 + difference 3 4) (sourceB2582 + difference 4 3) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2582 + difference 3 4) (sourceB2582 + difference 4 3) sourceC2582) = raw35761 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35761; decide +kernel
    rw [ha]
    exact (canonical35761 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2582 + difference 3 5) (sourceB2582 + difference 5 3) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2582 + difference 3 5) (sourceB2582 + difference 5 3) sourceC2582) = raw18369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw18369; decide +kernel
    rw [ha]
    exact (canonical18369 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2582 + difference 4 0) (sourceB2582 + difference 0 4) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4961) := by
    have ha : (tripleCharges (sourceA2582 + difference 4 0) (sourceB2582 + difference 0 4) sourceC2582) = raw32288 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw32288; decide +kernel
    rw [ha]
    exact (canonical32288 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2582 + difference 4 1) (sourceB2582 + difference 1 4) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4661) := by
    have ha : (tripleCharges (sourceA2582 + difference 4 1) (sourceB2582 + difference 1 4) sourceC2582) = raw35762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35762; decide +kernel
    rw [ha]
    exact (canonical35762 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2582 + difference 4 2) (sourceB2582 + difference 2 4) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5333) := by
    have ha : (tripleCharges (sourceA2582 + difference 4 2) (sourceB2582 + difference 2 4) sourceC2582) = raw35763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35763; decide +kernel
    rw [ha]
    exact (canonical35763 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2582 + difference 4 3) (sourceB2582 + difference 3 4) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2582 + difference 4 3) (sourceB2582 + difference 3 4) sourceC2582) = raw35764 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35764; decide +kernel
    rw [ha]
    exact (canonical35764 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2582 + difference 4 5) (sourceB2582 + difference 5 4) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2582 + difference 4 5) (sourceB2582 + difference 5 4) sourceC2582) = raw18373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw18373; decide +kernel
    rw [ha]
    exact (canonical18373 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2582 + difference 5 0) (sourceB2582 + difference 0 5) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4960) := by
    have ha : (tripleCharges (sourceA2582 + difference 5 0) (sourceB2582 + difference 0 5) sourceC2582) = raw32291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw32291; decide +kernel
    rw [ha]
    exact (canonical32291 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2582 + difference 5 1) (sourceB2582 + difference 1 5) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4660) := by
    have ha : (tripleCharges (sourceA2582 + difference 5 1) (sourceB2582 + difference 1 5) sourceC2582) = raw35765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35765; decide +kernel
    rw [ha]
    exact (canonical35765 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2582 + difference 5 2) (sourceB2582 + difference 2 5) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5030) := by
    have ha : (tripleCharges (sourceA2582 + difference 5 2) (sourceB2582 + difference 2 5) sourceC2582) = raw35766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35766; decide +kernel
    rw [ha]
    exact (canonical35766 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2582 + difference 5 3) (sourceB2582 + difference 3 5) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2582 + difference 5 3) (sourceB2582 + difference 3 5) sourceC2582) = raw35767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35767; decide +kernel
    rw [ha]
    exact (canonical35767 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2582 + difference 5 4) (sourceB2582 + difference 4 5) sourceC2582) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2582 + difference 5 4) (sourceB2582 + difference 4 5) sourceC2582) = raw35768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2582 sourceB2582 sourceC2582 difference raw35768; decide +kernel
    rw [ha]
    exact (canonical35768 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2582 sourceB2582 sourceC2582
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2582, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2583 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2583 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC2583 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceForm2583 : Integer.Sparse Master := [(Sum.inr 4663, 1), (Sum.inr 4666, 2), (Sum.inr 4677, 1), (Sum.inr 4851, 1), (Sum.inr 4956, 1), (Sum.inr 4958, 2), (Sum.inr 4964, 1), (Sum.inr 5114, 1), (Sum.inr 5129, 2), (Sum.inr 5137, 1), (Sum.inr 5373, 2), (Sum.inr 5377, 2), (Sum.inr 5379, 2), (Sum.inr 5380, 2), (Sum.inr 5383, 1), (Sum.inr 5396, 1), (Sum.inr 5422, 1), (Sum.inr 5424, 2), (Sum.inr 5427, 1), (Sum.inr 5430, 2), (Sum.inr 5447, 1)]

theorem sourceEq2583 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2583 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2583 + difference 0 1) (sourceB2583 + difference 1 0) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2583 + difference 0 1) (sourceB2583 + difference 1 0) sourceC2583) = raw35769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35769; decide +kernel
    rw [ha]
    exact (canonical35769 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2583 + difference 0 2) (sourceB2583 + difference 2 0) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA2583 + difference 0 2) (sourceB2583 + difference 2 0) sourceC2583) = raw35770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35770; decide +kernel
    rw [ha]
    exact (canonical35770 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2583 + difference 0 3) (sourceB2583 + difference 3 0) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2583 + difference 0 3) (sourceB2583 + difference 3 0) sourceC2583) = raw35771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35771; decide +kernel
    rw [ha]
    exact (canonical35771 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2583 + difference 0 4) (sourceB2583 + difference 4 0) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2583 + difference 0 4) (sourceB2583 + difference 4 0) sourceC2583) = raw35772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35772; decide +kernel
    rw [ha]
    exact (canonical35772 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2583 + difference 0 5) (sourceB2583 + difference 5 0) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5427) := by
    have ha : (tripleCharges (sourceA2583 + difference 0 5) (sourceB2583 + difference 5 0) sourceC2583) = raw18573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18573; decide +kernel
    rw [ha]
    exact (canonical18573 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2583 + difference 1 0) (sourceB2583 + difference 0 1) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA2583 + difference 1 0) (sourceB2583 + difference 0 1) sourceC2583) = raw18598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18598; decide +kernel
    rw [ha]
    exact (canonical18598 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2583 + difference 1 2) (sourceB2583 + difference 2 1) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA2583 + difference 1 2) (sourceB2583 + difference 2 1) sourceC2583) = raw18600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18600; decide +kernel
    rw [ha]
    exact (canonical18600 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2583 + difference 1 3) (sourceB2583 + difference 3 1) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA2583 + difference 1 3) (sourceB2583 + difference 3 1) sourceC2583) = raw18601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18601; decide +kernel
    rw [ha]
    exact (canonical18601 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2583 + difference 1 4) (sourceB2583 + difference 4 1) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA2583 + difference 1 4) (sourceB2583 + difference 4 1) sourceC2583) = raw18602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18602; decide +kernel
    rw [ha]
    exact (canonical18602 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2583 + difference 1 5) (sourceB2583 + difference 5 1) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA2583 + difference 1 5) (sourceB2583 + difference 5 1) sourceC2583) = raw35773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35773; decide +kernel
    rw [ha]
    exact (canonical35773 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2583 + difference 2 0) (sourceB2583 + difference 0 2) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4677) := by
    have ha : (tripleCharges (sourceA2583 + difference 2 0) (sourceB2583 + difference 0 2) sourceC2583) = raw35774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35774; decide +kernel
    rw [ha]
    exact (canonical35774 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2583 + difference 2 1) (sourceB2583 + difference 1 2) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4964) := by
    have ha : (tripleCharges (sourceA2583 + difference 2 1) (sourceB2583 + difference 1 2) sourceC2583) = raw35775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35775; decide +kernel
    rw [ha]
    exact (canonical35775 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2583 + difference 2 3) (sourceB2583 + difference 3 2) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2583 + difference 2 3) (sourceB2583 + difference 3 2) sourceC2583) = raw35776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35776; decide +kernel
    rw [ha]
    exact (canonical35776 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2583 + difference 2 4) (sourceB2583 + difference 4 2) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2583 + difference 2 4) (sourceB2583 + difference 4 2) sourceC2583) = raw35777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35777; decide +kernel
    rw [ha]
    exact (canonical35777 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2583 + difference 2 5) (sourceB2583 + difference 5 2) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA2583 + difference 2 5) (sourceB2583 + difference 5 2) sourceC2583) = raw18584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18584; decide +kernel
    rw [ha]
    exact (canonical18584 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2583 + difference 3 0) (sourceB2583 + difference 0 3) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4666) := by
    have ha : (tripleCharges (sourceA2583 + difference 3 0) (sourceB2583 + difference 0 3) sourceC2583) = raw35778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35778; decide +kernel
    rw [ha]
    exact (canonical35778 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2583 + difference 3 1) (sourceB2583 + difference 1 3) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4958) := by
    have ha : (tripleCharges (sourceA2583 + difference 3 1) (sourceB2583 + difference 1 3) sourceC2583) = raw35779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35779; decide +kernel
    rw [ha]
    exact (canonical35779 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2583 + difference 3 2) (sourceB2583 + difference 2 3) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5373) := by
    have ha : (tripleCharges (sourceA2583 + difference 3 2) (sourceB2583 + difference 2 3) sourceC2583) = raw35780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35780; decide +kernel
    rw [ha]
    exact (canonical35780 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2583 + difference 3 4) (sourceB2583 + difference 4 3) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5377) := by
    have ha : (tripleCharges (sourceA2583 + difference 3 4) (sourceB2583 + difference 4 3) sourceC2583) = raw35781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35781; decide +kernel
    rw [ha]
    exact (canonical35781 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2583 + difference 3 5) (sourceB2583 + difference 5 3) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2583 + difference 3 5) (sourceB2583 + difference 5 3) sourceC2583) = raw18589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18589; decide +kernel
    rw [ha]
    exact (canonical18589 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2583 + difference 4 0) (sourceB2583 + difference 0 4) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4666) := by
    have ha : (tripleCharges (sourceA2583 + difference 4 0) (sourceB2583 + difference 0 4) sourceC2583) = raw35782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35782; decide +kernel
    rw [ha]
    exact (canonical35782 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2583 + difference 4 1) (sourceB2583 + difference 1 4) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4958) := by
    have ha : (tripleCharges (sourceA2583 + difference 4 1) (sourceB2583 + difference 1 4) sourceC2583) = raw35783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35783; decide +kernel
    rw [ha]
    exact (canonical35783 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2583 + difference 4 2) (sourceB2583 + difference 2 4) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5373) := by
    have ha : (tripleCharges (sourceA2583 + difference 4 2) (sourceB2583 + difference 2 4) sourceC2583) = raw35784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35784; decide +kernel
    rw [ha]
    exact (canonical35784 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2583 + difference 4 3) (sourceB2583 + difference 3 4) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5377) := by
    have ha : (tripleCharges (sourceA2583 + difference 4 3) (sourceB2583 + difference 3 4) sourceC2583) = raw35785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35785; decide +kernel
    rw [ha]
    exact (canonical35785 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2583 + difference 4 5) (sourceB2583 + difference 5 4) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2583 + difference 4 5) (sourceB2583 + difference 5 4) sourceC2583) = raw18594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18594; decide +kernel
    rw [ha]
    exact (canonical18594 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2583 + difference 5 0) (sourceB2583 + difference 0 5) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4663) := by
    have ha : (tripleCharges (sourceA2583 + difference 5 0) (sourceB2583 + difference 0 5) sourceC2583) = raw35786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35786; decide +kernel
    rw [ha]
    exact (canonical35786 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2583 + difference 5 1) (sourceB2583 + difference 1 5) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4956) := by
    have ha : (tripleCharges (sourceA2583 + difference 5 1) (sourceB2583 + difference 1 5) sourceC2583) = raw35787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35787; decide +kernel
    rw [ha]
    exact (canonical35787 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2583 + difference 5 2) (sourceB2583 + difference 2 5) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5114) := by
    have ha : (tripleCharges (sourceA2583 + difference 5 2) (sourceB2583 + difference 2 5) sourceC2583) = raw35788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35788; decide +kernel
    rw [ha]
    exact (canonical35788 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2583 + difference 5 3) (sourceB2583 + difference 3 5) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA2583 + difference 5 3) (sourceB2583 + difference 3 5) sourceC2583) = raw35789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35789; decide +kernel
    rw [ha]
    exact (canonical35789 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2583 + difference 5 4) (sourceB2583 + difference 4 5) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA2583 + difference 5 4) (sourceB2583 + difference 4 5) sourceC2583) = raw35790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35790; decide +kernel
    rw [ha]
    exact (canonical35790 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2583 sourceB2583 sourceC2583
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2583, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2584 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2584 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC2584 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceForm2584 : Integer.Sparse Master := [(Sum.inr 2140, 1), (Sum.inr 2142, 1), (Sum.inr 2148, 2), (Sum.inr 2240, 1), (Sum.inr 3510, 1), (Sum.inr 3511, 2), (Sum.inr 3516, 2), (Sum.inr 3521, 1), (Sum.inr 3554, 1), (Sum.inr 3597, 1), (Sum.inr 3792, 2), (Sum.inr 3798, 1), (Sum.inr 3832, 2), (Sum.inr 3835, 2), (Sum.inr 3836, 2), (Sum.inr 3843, 2), (Sum.inr 3844, 1), (Sum.inr 3848, 2), (Sum.inr 3867, 1), (Sum.inr 3900, 1), (Sum.inr 3909, 1)]

theorem sourceEq2584 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2584 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2584 + difference 0 1) (sourceB2584 + difference 1 0) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3521) := by
    have ha : (tripleCharges (sourceA2584 + difference 0 1) (sourceB2584 + difference 1 0) sourceC2584) = raw35791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35791; decide +kernel
    rw [ha]
    exact (canonical35791 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2584 + difference 0 2) (sourceB2584 + difference 2 0) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3798) := by
    have ha : (tripleCharges (sourceA2584 + difference 0 2) (sourceB2584 + difference 2 0) sourceC2584) = raw35792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35792; decide +kernel
    rw [ha]
    exact (canonical35792 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2584 + difference 0 3) (sourceB2584 + difference 3 0) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA2584 + difference 0 3) (sourceB2584 + difference 3 0) sourceC2584) = raw35793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35793; decide +kernel
    rw [ha]
    exact (canonical35793 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2584 + difference 0 4) (sourceB2584 + difference 4 0) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA2584 + difference 0 4) (sourceB2584 + difference 4 0) sourceC2584) = raw35794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35794; decide +kernel
    rw [ha]
    exact (canonical35794 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2584 + difference 0 5) (sourceB2584 + difference 5 0) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3844) := by
    have ha : (tripleCharges (sourceA2584 + difference 0 5) (sourceB2584 + difference 5 0) sourceC2584) = raw35795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35795; decide +kernel
    rw [ha]
    exact (canonical35795 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2584 + difference 1 0) (sourceB2584 + difference 0 1) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA2584 + difference 1 0) (sourceB2584 + difference 0 1) sourceC2584) = raw35796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35796; decide +kernel
    rw [ha]
    exact (canonical35796 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2584 + difference 1 2) (sourceB2584 + difference 2 1) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3900) := by
    have ha : (tripleCharges (sourceA2584 + difference 1 2) (sourceB2584 + difference 2 1) sourceC2584) = raw35797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35797; decide +kernel
    rw [ha]
    exact (canonical35797 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2584 + difference 1 3) (sourceB2584 + difference 3 1) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA2584 + difference 1 3) (sourceB2584 + difference 3 1) sourceC2584) = raw35798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35798; decide +kernel
    rw [ha]
    exact (canonical35798 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2584 + difference 1 4) (sourceB2584 + difference 4 1) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA2584 + difference 1 4) (sourceB2584 + difference 4 1) sourceC2584) = raw35799 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35799; decide +kernel
    rw [ha]
    exact (canonical35799 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2584 + difference 1 5) (sourceB2584 + difference 5 1) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA2584 + difference 1 5) (sourceB2584 + difference 5 1) sourceC2584) = raw35800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35800; decide +kernel
    rw [ha]
    exact (canonical35800 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2584 + difference 2 0) (sourceB2584 + difference 0 2) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2142) := by
    have ha : (tripleCharges (sourceA2584 + difference 2 0) (sourceB2584 + difference 0 2) sourceC2584) = raw35801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35801; decide +kernel
    rw [ha]
    exact (canonical35801 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2584 + difference 2 1) (sourceB2584 + difference 1 2) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3554) := by
    have ha : (tripleCharges (sourceA2584 + difference 2 1) (sourceB2584 + difference 1 2) sourceC2584) = raw35802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35802; decide +kernel
    rw [ha]
    exact (canonical35802 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2584 + difference 2 3) (sourceB2584 + difference 3 2) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2584 + difference 2 3) (sourceB2584 + difference 3 2) sourceC2584) = raw35803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35803; decide +kernel
    rw [ha]
    exact (canonical35803 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2584 + difference 2 4) (sourceB2584 + difference 4 2) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2584 + difference 2 4) (sourceB2584 + difference 4 2) sourceC2584) = raw35804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35804; decide +kernel
    rw [ha]
    exact (canonical35804 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2584 + difference 2 5) (sourceB2584 + difference 5 2) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3867) := by
    have ha : (tripleCharges (sourceA2584 + difference 2 5) (sourceB2584 + difference 5 2) sourceC2584) = raw35805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35805; decide +kernel
    rw [ha]
    exact (canonical35805 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2584 + difference 3 0) (sourceB2584 + difference 0 3) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2148) := by
    have ha : (tripleCharges (sourceA2584 + difference 3 0) (sourceB2584 + difference 0 3) sourceC2584) = raw35806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35806; decide +kernel
    rw [ha]
    exact (canonical35806 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2584 + difference 3 1) (sourceB2584 + difference 1 3) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3511) := by
    have ha : (tripleCharges (sourceA2584 + difference 3 1) (sourceB2584 + difference 1 3) sourceC2584) = raw35807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35807; decide +kernel
    rw [ha]
    exact (canonical35807 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2584 + difference 3 2) (sourceB2584 + difference 2 3) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3792) := by
    have ha : (tripleCharges (sourceA2584 + difference 3 2) (sourceB2584 + difference 2 3) sourceC2584) = raw35808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35808; decide +kernel
    rw [ha]
    exact (canonical35808 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2584 + difference 3 4) (sourceB2584 + difference 4 3) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3835) := by
    have ha : (tripleCharges (sourceA2584 + difference 3 4) (sourceB2584 + difference 4 3) sourceC2584) = raw35809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35809; decide +kernel
    rw [ha]
    exact (canonical35809 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2584 + difference 3 5) (sourceB2584 + difference 5 3) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3836) := by
    have ha : (tripleCharges (sourceA2584 + difference 3 5) (sourceB2584 + difference 5 3) sourceC2584) = raw35810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35810; decide +kernel
    rw [ha]
    exact (canonical35810 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2584 + difference 4 0) (sourceB2584 + difference 0 4) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2148) := by
    have ha : (tripleCharges (sourceA2584 + difference 4 0) (sourceB2584 + difference 0 4) sourceC2584) = raw35811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35811; decide +kernel
    rw [ha]
    exact (canonical35811 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2584 + difference 4 1) (sourceB2584 + difference 1 4) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3511) := by
    have ha : (tripleCharges (sourceA2584 + difference 4 1) (sourceB2584 + difference 1 4) sourceC2584) = raw35812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35812; decide +kernel
    rw [ha]
    exact (canonical35812 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2584 + difference 4 2) (sourceB2584 + difference 2 4) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3792) := by
    have ha : (tripleCharges (sourceA2584 + difference 4 2) (sourceB2584 + difference 2 4) sourceC2584) = raw35813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35813; decide +kernel
    rw [ha]
    exact (canonical35813 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2584 + difference 4 3) (sourceB2584 + difference 3 4) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3835) := by
    have ha : (tripleCharges (sourceA2584 + difference 4 3) (sourceB2584 + difference 3 4) sourceC2584) = raw35814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35814; decide +kernel
    rw [ha]
    exact (canonical35814 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2584 + difference 4 5) (sourceB2584 + difference 5 4) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3836) := by
    have ha : (tripleCharges (sourceA2584 + difference 4 5) (sourceB2584 + difference 5 4) sourceC2584) = raw35815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35815; decide +kernel
    rw [ha]
    exact (canonical35815 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2584 + difference 5 0) (sourceB2584 + difference 0 5) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2140) := by
    have ha : (tripleCharges (sourceA2584 + difference 5 0) (sourceB2584 + difference 0 5) sourceC2584) = raw35816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35816; decide +kernel
    rw [ha]
    exact (canonical35816 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2584 + difference 5 1) (sourceB2584 + difference 1 5) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3510) := by
    have ha : (tripleCharges (sourceA2584 + difference 5 1) (sourceB2584 + difference 1 5) sourceC2584) = raw35817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35817; decide +kernel
    rw [ha]
    exact (canonical35817 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2584 + difference 5 2) (sourceB2584 + difference 2 5) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3597) := by
    have ha : (tripleCharges (sourceA2584 + difference 5 2) (sourceB2584 + difference 2 5) sourceC2584) = raw35818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35818; decide +kernel
    rw [ha]
    exact (canonical35818 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2584 + difference 5 3) (sourceB2584 + difference 3 5) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2584 + difference 5 3) (sourceB2584 + difference 3 5) sourceC2584) = raw35819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35819; decide +kernel
    rw [ha]
    exact (canonical35819 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2584 + difference 5 4) (sourceB2584 + difference 4 5) sourceC2584) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2584 + difference 5 4) (sourceB2584 + difference 4 5) sourceC2584) = raw35820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2584 sourceB2584 sourceC2584 difference raw35820; decide +kernel
    rw [ha]
    exact (canonical35820 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2584 sourceB2584 sourceC2584
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2584, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2585 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceB2585 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC2585 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceForm2585 : Integer.Sparse Master := [(Sum.inr 5123, 1), (Sum.inr 5124, 2), (Sum.inr 5157, 1), (Sum.inr 5219, 1), (Sum.inr 5221, 1), (Sum.inr 5226, 2), (Sum.inr 5237, 1), (Sum.inr 5345, 1), (Sum.inr 5346, 2), (Sum.inr 5351, 1), (Sum.inr 5352, 2), (Sum.inr 5359, 1), (Sum.inr 5369, 1), (Sum.inr 5374, 1), (Sum.inr 5375, 2), (Sum.inr 5378, 2), (Sum.inr 5379, 2), (Sum.inr 5381, 2), (Sum.inr 5387, 1), (Sum.inr 5388, 2), (Sum.inr 5460, 1)]

theorem sourceEq2585 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2585 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2585 + difference 0 1) (sourceB2585 + difference 1 0) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA2585 + difference 0 1) (sourceB2585 + difference 1 0) sourceC2585) = raw35821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35821; decide +kernel
    rw [ha]
    exact (canonical35821 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2585 + difference 0 2) (sourceB2585 + difference 2 0) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2585 + difference 0 2) (sourceB2585 + difference 2 0) sourceC2585) = raw35576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35576; decide +kernel
    rw [ha]
    exact (canonical35576 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2585 + difference 0 3) (sourceB2585 + difference 3 0) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2585 + difference 0 3) (sourceB2585 + difference 3 0) sourceC2585) = raw35822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35822; decide +kernel
    rw [ha]
    exact (canonical35822 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2585 + difference 0 4) (sourceB2585 + difference 4 0) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2585 + difference 0 4) (sourceB2585 + difference 4 0) sourceC2585) = raw35823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35823; decide +kernel
    rw [ha]
    exact (canonical35823 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2585 + difference 0 5) (sourceB2585 + difference 5 0) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5345) := by
    have ha : (tripleCharges (sourceA2585 + difference 0 5) (sourceB2585 + difference 5 0) sourceC2585) = raw35824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35824; decide +kernel
    rw [ha]
    exact (canonical35824 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2585 + difference 1 0) (sourceB2585 + difference 0 1) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5157) := by
    have ha : (tripleCharges (sourceA2585 + difference 1 0) (sourceB2585 + difference 0 1) sourceC2585) = raw35825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35825; decide +kernel
    rw [ha]
    exact (canonical35825 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2585 + difference 1 2) (sourceB2585 + difference 2 1) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2585 + difference 1 2) (sourceB2585 + difference 2 1) sourceC2585) = raw35581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35581; decide +kernel
    rw [ha]
    exact (canonical35581 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2585 + difference 1 3) (sourceB2585 + difference 3 1) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5124) := by
    have ha : (tripleCharges (sourceA2585 + difference 1 3) (sourceB2585 + difference 3 1) sourceC2585) = raw35826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35826; decide +kernel
    rw [ha]
    exact (canonical35826 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2585 + difference 1 4) (sourceB2585 + difference 4 1) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5124) := by
    have ha : (tripleCharges (sourceA2585 + difference 1 4) (sourceB2585 + difference 4 1) sourceC2585) = raw35827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35827; decide +kernel
    rw [ha]
    exact (canonical35827 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2585 + difference 1 5) (sourceB2585 + difference 5 1) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2585 + difference 1 5) (sourceB2585 + difference 5 1) sourceC2585) = raw35828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35828; decide +kernel
    rw [ha]
    exact (canonical35828 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2585 + difference 2 0) (sourceB2585 + difference 0 2) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5221) := by
    have ha : (tripleCharges (sourceA2585 + difference 2 0) (sourceB2585 + difference 0 2) sourceC2585) = raw35829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35829; decide +kernel
    rw [ha]
    exact (canonical35829 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2585 + difference 2 1) (sourceB2585 + difference 1 2) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA2585 + difference 2 1) (sourceB2585 + difference 1 2) sourceC2585) = raw35830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35830; decide +kernel
    rw [ha]
    exact (canonical35830 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2585 + difference 2 3) (sourceB2585 + difference 3 2) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5375) := by
    have ha : (tripleCharges (sourceA2585 + difference 2 3) (sourceB2585 + difference 3 2) sourceC2585) = raw35831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35831; decide +kernel
    rw [ha]
    exact (canonical35831 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2585 + difference 2 4) (sourceB2585 + difference 4 2) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5375) := by
    have ha : (tripleCharges (sourceA2585 + difference 2 4) (sourceB2585 + difference 4 2) sourceC2585) = raw35832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35832; decide +kernel
    rw [ha]
    exact (canonical35832 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2585 + difference 2 5) (sourceB2585 + difference 5 2) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA2585 + difference 2 5) (sourceB2585 + difference 5 2) sourceC2585) = raw35833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35833; decide +kernel
    rw [ha]
    exact (canonical35833 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2585 + difference 3 0) (sourceB2585 + difference 0 3) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2585 + difference 3 0) (sourceB2585 + difference 0 3) sourceC2585) = raw35834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35834; decide +kernel
    rw [ha]
    exact (canonical35834 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2585 + difference 3 1) (sourceB2585 + difference 1 3) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2585 + difference 3 1) (sourceB2585 + difference 1 3) sourceC2585) = raw35835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35835; decide +kernel
    rw [ha]
    exact (canonical35835 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2585 + difference 3 2) (sourceB2585 + difference 2 3) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2585 + difference 3 2) (sourceB2585 + difference 2 3) sourceC2585) = raw35591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35591; decide +kernel
    rw [ha]
    exact (canonical35591 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2585 + difference 3 4) (sourceB2585 + difference 4 3) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2585 + difference 3 4) (sourceB2585 + difference 4 3) sourceC2585) = raw35836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35836; decide +kernel
    rw [ha]
    exact (canonical35836 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2585 + difference 3 5) (sourceB2585 + difference 5 3) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2585 + difference 3 5) (sourceB2585 + difference 5 3) sourceC2585) = raw35837 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35837; decide +kernel
    rw [ha]
    exact (canonical35837 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2585 + difference 4 0) (sourceB2585 + difference 0 4) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2585 + difference 4 0) (sourceB2585 + difference 0 4) sourceC2585) = raw35623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35623; decide +kernel
    rw [ha]
    exact (canonical35623 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2585 + difference 4 1) (sourceB2585 + difference 1 4) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2585 + difference 4 1) (sourceB2585 + difference 1 4) sourceC2585) = raw35624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35624; decide +kernel
    rw [ha]
    exact (canonical35624 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2585 + difference 4 2) (sourceB2585 + difference 2 4) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2585 + difference 4 2) (sourceB2585 + difference 2 4) sourceC2585) = raw35596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35596; decide +kernel
    rw [ha]
    exact (canonical35596 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2585 + difference 4 3) (sourceB2585 + difference 3 4) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2585 + difference 4 3) (sourceB2585 + difference 3 4) sourceC2585) = raw35625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35625; decide +kernel
    rw [ha]
    exact (canonical35625 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2585 + difference 4 5) (sourceB2585 + difference 5 4) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2585 + difference 4 5) (sourceB2585 + difference 5 4) sourceC2585) = raw35626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35626; decide +kernel
    rw [ha]
    exact (canonical35626 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2585 + difference 5 0) (sourceB2585 + difference 0 5) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA2585 + difference 5 0) (sourceB2585 + difference 0 5) sourceC2585) = raw35582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35582; decide +kernel
    rw [ha]
    exact (canonical35582 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2585 + difference 5 1) (sourceB2585 + difference 1 5) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2585 + difference 5 1) (sourceB2585 + difference 1 5) sourceC2585) = raw35583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35583; decide +kernel
    rw [ha]
    exact (canonical35583 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2585 + difference 5 2) (sourceB2585 + difference 2 5) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2585 + difference 5 2) (sourceB2585 + difference 2 5) sourceC2585) = raw35636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35636; decide +kernel
    rw [ha]
    exact (canonical35636 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2585 + difference 5 3) (sourceB2585 + difference 3 5) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA2585 + difference 5 3) (sourceB2585 + difference 3 5) sourceC2585) = raw35584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35584; decide +kernel
    rw [ha]
    exact (canonical35584 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2585 + difference 5 4) (sourceB2585 + difference 4 5) sourceC2585) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA2585 + difference 5 4) (sourceB2585 + difference 4 5) sourceC2585) = raw35585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2585 sourceB2585 sourceC2585 difference raw35585; decide +kernel
    rw [ha]
    exact (canonical35585 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2585 sourceB2585 sourceC2585
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2585, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2586 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2586 : Charge := ![0, 2, 1, -1, 0, -2]
def sourceC2586 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceForm2586 : Integer.Sparse Master := [(Sum.inr 4658, 1), (Sum.inr 4659, 1), (Sum.inr 4661, 1), (Sum.inr 4676, 1), (Sum.inr 4707, 1), (Sum.inr 4716, 1), (Sum.inr 4731, 1), (Sum.inr 4798, 1), (Sum.inr 4810, 1), (Sum.inr 4961, 1), (Sum.inr 4962, 1), (Sum.inr 4971, 1), (Sum.inr 5149, 1), (Sum.inr 5315, 1), (Sum.inr 5320, 1), (Sum.inr 5333, 1), (Sum.inr 5349, 1), (Sum.inr 5355, 1), (Sum.inr 5378, 2), (Sum.inr 5380, 1), (Sum.inr 5386, 1), (Sum.inr 5387, 1), (Sum.inr 5397, 1), (Sum.inr 5400, 1), (Sum.inr 5406, 1), (Sum.inr 5431, 1), (Sum.inr 5432, 1), (Sum.inr 5433, 1), (Sum.inr 5435, 1)]

theorem sourceEq2586 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2586 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2586 + difference 0 1) (sourceB2586 + difference 1 0) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2586 + difference 0 1) (sourceB2586 + difference 1 0) sourceC2586) = raw35838 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35838; decide +kernel
    rw [ha]
    exact (canonical35838 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2586 + difference 0 2) (sourceB2586 + difference 2 0) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA2586 + difference 0 2) (sourceB2586 + difference 2 0) sourceC2586) = raw35839 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35839; decide +kernel
    rw [ha]
    exact (canonical35839 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2586 + difference 0 3) (sourceB2586 + difference 3 0) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA2586 + difference 0 3) (sourceB2586 + difference 3 0) sourceC2586) = raw35840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35840; decide +kernel
    rw [ha]
    exact (canonical35840 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2586 + difference 0 4) (sourceB2586 + difference 4 0) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA2586 + difference 0 4) (sourceB2586 + difference 4 0) sourceC2586) = raw35841 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35841; decide +kernel
    rw [ha]
    exact (canonical35841 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2586 + difference 0 5) (sourceB2586 + difference 5 0) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA2586 + difference 0 5) (sourceB2586 + difference 5 0) sourceC2586) = raw35842 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35842; decide +kernel
    rw [ha]
    exact (canonical35842 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2586 + difference 1 0) (sourceB2586 + difference 0 1) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2586 + difference 1 0) (sourceB2586 + difference 0 1) sourceC2586) = raw24752 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw24752; decide +kernel
    rw [ha]
    exact (canonical24752 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2586 + difference 1 2) (sourceB2586 + difference 2 1) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA2586 + difference 1 2) (sourceB2586 + difference 2 1) sourceC2586) = raw32339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw32339; decide +kernel
    rw [ha]
    exact (canonical32339 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2586 + difference 1 3) (sourceB2586 + difference 3 1) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2586 + difference 1 3) (sourceB2586 + difference 3 1) sourceC2586) = raw32340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw32340; decide +kernel
    rw [ha]
    exact (canonical32340 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2586 + difference 1 4) (sourceB2586 + difference 4 1) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA2586 + difference 1 4) (sourceB2586 + difference 4 1) sourceC2586) = raw32341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw32341; decide +kernel
    rw [ha]
    exact (canonical32341 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2586 + difference 1 5) (sourceB2586 + difference 5 1) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2586 + difference 1 5) (sourceB2586 + difference 5 1) sourceC2586) = raw32342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw32342; decide +kernel
    rw [ha]
    exact (canonical32342 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2586 + difference 2 0) (sourceB2586 + difference 0 2) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4971) := by
    have ha : (tripleCharges (sourceA2586 + difference 2 0) (sourceB2586 + difference 0 2) sourceC2586) = raw32344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw32344; decide +kernel
    rw [ha]
    exact (canonical32344 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2586 + difference 2 1) (sourceB2586 + difference 1 2) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4676) := by
    have ha : (tripleCharges (sourceA2586 + difference 2 1) (sourceB2586 + difference 1 2) sourceC2586) = raw35843 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35843; decide +kernel
    rw [ha]
    exact (canonical35843 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2586 + difference 2 3) (sourceB2586 + difference 3 2) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2586 + difference 2 3) (sourceB2586 + difference 3 2) sourceC2586) = raw35844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35844; decide +kernel
    rw [ha]
    exact (canonical35844 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2586 + difference 2 4) (sourceB2586 + difference 4 2) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2586 + difference 2 4) (sourceB2586 + difference 4 2) sourceC2586) = raw35845 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35845; decide +kernel
    rw [ha]
    exact (canonical35845 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2586 + difference 2 5) (sourceB2586 + difference 5 2) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5386) := by
    have ha : (tripleCharges (sourceA2586 + difference 2 5) (sourceB2586 + difference 5 2) sourceC2586) = raw35846 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35846; decide +kernel
    rw [ha]
    exact (canonical35846 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2586 + difference 3 0) (sourceB2586 + difference 0 3) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4962) := by
    have ha : (tripleCharges (sourceA2586 + difference 3 0) (sourceB2586 + difference 0 3) sourceC2586) = raw32348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw32348; decide +kernel
    rw [ha]
    exact (canonical32348 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2586 + difference 3 1) (sourceB2586 + difference 1 3) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4659) := by
    have ha : (tripleCharges (sourceA2586 + difference 3 1) (sourceB2586 + difference 1 3) sourceC2586) = raw35847 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35847; decide +kernel
    rw [ha]
    exact (canonical35847 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2586 + difference 3 2) (sourceB2586 + difference 2 3) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5315) := by
    have ha : (tripleCharges (sourceA2586 + difference 3 2) (sourceB2586 + difference 2 3) sourceC2586) = raw35848 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35848; decide +kernel
    rw [ha]
    exact (canonical35848 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2586 + difference 3 4) (sourceB2586 + difference 4 3) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5320) := by
    have ha : (tripleCharges (sourceA2586 + difference 3 4) (sourceB2586 + difference 4 3) sourceC2586) = raw35849 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35849; decide +kernel
    rw [ha]
    exact (canonical35849 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2586 + difference 3 5) (sourceB2586 + difference 5 3) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2586 + difference 3 5) (sourceB2586 + difference 5 3) sourceC2586) = raw35850 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35850; decide +kernel
    rw [ha]
    exact (canonical35850 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2586 + difference 4 0) (sourceB2586 + difference 0 4) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4961) := by
    have ha : (tripleCharges (sourceA2586 + difference 4 0) (sourceB2586 + difference 0 4) sourceC2586) = raw32352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw32352; decide +kernel
    rw [ha]
    exact (canonical32352 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2586 + difference 4 1) (sourceB2586 + difference 1 4) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4661) := by
    have ha : (tripleCharges (sourceA2586 + difference 4 1) (sourceB2586 + difference 1 4) sourceC2586) = raw35851 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35851; decide +kernel
    rw [ha]
    exact (canonical35851 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2586 + difference 4 2) (sourceB2586 + difference 2 4) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5333) := by
    have ha : (tripleCharges (sourceA2586 + difference 4 2) (sourceB2586 + difference 2 4) sourceC2586) = raw35852 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35852; decide +kernel
    rw [ha]
    exact (canonical35852 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2586 + difference 4 3) (sourceB2586 + difference 3 4) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2586 + difference 4 3) (sourceB2586 + difference 3 4) sourceC2586) = raw35853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35853; decide +kernel
    rw [ha]
    exact (canonical35853 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2586 + difference 4 5) (sourceB2586 + difference 5 4) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2586 + difference 4 5) (sourceB2586 + difference 5 4) sourceC2586) = raw35854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35854; decide +kernel
    rw [ha]
    exact (canonical35854 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2586 + difference 5 0) (sourceB2586 + difference 0 5) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4707) := by
    have ha : (tripleCharges (sourceA2586 + difference 5 0) (sourceB2586 + difference 0 5) sourceC2586) = raw32356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw32356; decide +kernel
    rw [ha]
    exact (canonical32356 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2586 + difference 5 1) (sourceB2586 + difference 1 5) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4658) := by
    have ha : (tripleCharges (sourceA2586 + difference 5 1) (sourceB2586 + difference 1 5) sourceC2586) = raw35855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35855; decide +kernel
    rw [ha]
    exact (canonical35855 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2586 + difference 5 2) (sourceB2586 + difference 2 5) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4716) := by
    have ha : (tripleCharges (sourceA2586 + difference 5 2) (sourceB2586 + difference 2 5) sourceC2586) = raw35856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35856; decide +kernel
    rw [ha]
    exact (canonical35856 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2586 + difference 5 3) (sourceB2586 + difference 3 5) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2586 + difference 5 3) (sourceB2586 + difference 3 5) sourceC2586) = raw35857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35857; decide +kernel
    rw [ha]
    exact (canonical35857 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2586 + difference 5 4) (sourceB2586 + difference 4 5) sourceC2586) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4731) := by
    have ha : (tripleCharges (sourceA2586 + difference 5 4) (sourceB2586 + difference 4 5) sourceC2586) = raw35858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2586 sourceB2586 sourceC2586 difference raw35858; decide +kernel
    rw [ha]
    exact (canonical35858 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2586 sourceB2586 sourceC2586
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2586, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2587 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2587 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2587 : Charge := ![0, 2, 1, -1, 0, -2]
def sourceForm2587 : Integer.Sparse Master := [(Sum.inr 4664, 1), (Sum.inr 4665, 1), (Sum.inr 4668, 1), (Sum.inr 4680, 1), (Sum.inr 4852, 1), (Sum.inr 4954, 1), (Sum.inr 4955, 1), (Sum.inr 4957, 1), (Sum.inr 4963, 1), (Sum.inr 5038, 1), (Sum.inr 5080, 1), (Sum.inr 5129, 1), (Sum.inr 5134, 1), (Sum.inr 5336, 1), (Sum.inr 5355, 1), (Sum.inr 5372, 1), (Sum.inr 5376, 1), (Sum.inr 5379, 1), (Sum.inr 5381, 2), (Sum.inr 5382, 1), (Sum.inr 5384, 1), (Sum.inr 5394, 1), (Sum.inr 5397, 1), (Sum.inr 5409, 1), (Sum.inr 5411, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 1), (Sum.inr 5425, 1), (Sum.inr 5445, 1)]

theorem sourceEq2587 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2587 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2587 + difference 0 1) (sourceB2587 + difference 1 0) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2587 + difference 0 1) (sourceB2587 + difference 1 0) sourceC2587) = raw35859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35859; decide +kernel
    rw [ha]
    exact (canonical35859 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2587 + difference 0 2) (sourceB2587 + difference 2 0) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA2587 + difference 0 2) (sourceB2587 + difference 2 0) sourceC2587) = raw35860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35860; decide +kernel
    rw [ha]
    exact (canonical35860 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2587 + difference 0 3) (sourceB2587 + difference 3 0) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA2587 + difference 0 3) (sourceB2587 + difference 3 0) sourceC2587) = raw35861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35861; decide +kernel
    rw [ha]
    exact (canonical35861 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2587 + difference 0 4) (sourceB2587 + difference 4 0) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2587 + difference 0 4) (sourceB2587 + difference 4 0) sourceC2587) = raw35862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35862; decide +kernel
    rw [ha]
    exact (canonical35862 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2587 + difference 0 5) (sourceB2587 + difference 5 0) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2587 + difference 0 5) (sourceB2587 + difference 5 0) sourceC2587) = raw35863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35863; decide +kernel
    rw [ha]
    exact (canonical35863 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2587 + difference 1 0) (sourceB2587 + difference 0 1) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA2587 + difference 1 0) (sourceB2587 + difference 0 1) sourceC2587) = raw35864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35864; decide +kernel
    rw [ha]
    exact (canonical35864 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2587 + difference 1 2) (sourceB2587 + difference 2 1) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA2587 + difference 1 2) (sourceB2587 + difference 2 1) sourceC2587) = raw35865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35865; decide +kernel
    rw [ha]
    exact (canonical35865 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2587 + difference 1 3) (sourceB2587 + difference 3 1) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA2587 + difference 1 3) (sourceB2587 + difference 3 1) sourceC2587) = raw35866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35866; decide +kernel
    rw [ha]
    exact (canonical35866 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2587 + difference 1 4) (sourceB2587 + difference 4 1) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA2587 + difference 1 4) (sourceB2587 + difference 4 1) sourceC2587) = raw35867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35867; decide +kernel
    rw [ha]
    exact (canonical35867 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2587 + difference 1 5) (sourceB2587 + difference 5 1) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA2587 + difference 1 5) (sourceB2587 + difference 5 1) sourceC2587) = raw35868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35868; decide +kernel
    rw [ha]
    exact (canonical35868 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2587 + difference 2 0) (sourceB2587 + difference 0 2) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4680) := by
    have ha : (tripleCharges (sourceA2587 + difference 2 0) (sourceB2587 + difference 0 2) sourceC2587) = raw35869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35869; decide +kernel
    rw [ha]
    exact (canonical35869 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2587 + difference 2 1) (sourceB2587 + difference 1 2) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4963) := by
    have ha : (tripleCharges (sourceA2587 + difference 2 1) (sourceB2587 + difference 1 2) sourceC2587) = raw35870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35870; decide +kernel
    rw [ha]
    exact (canonical35870 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2587 + difference 2 3) (sourceB2587 + difference 3 2) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA2587 + difference 2 3) (sourceB2587 + difference 3 2) sourceC2587) = raw35871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35871; decide +kernel
    rw [ha]
    exact (canonical35871 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2587 + difference 2 4) (sourceB2587 + difference 4 2) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2587 + difference 2 4) (sourceB2587 + difference 4 2) sourceC2587) = raw35872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35872; decide +kernel
    rw [ha]
    exact (canonical35872 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2587 + difference 2 5) (sourceB2587 + difference 5 2) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5382) := by
    have ha : (tripleCharges (sourceA2587 + difference 2 5) (sourceB2587 + difference 5 2) sourceC2587) = raw35873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35873; decide +kernel
    rw [ha]
    exact (canonical35873 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2587 + difference 3 0) (sourceB2587 + difference 0 3) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4668) := by
    have ha : (tripleCharges (sourceA2587 + difference 3 0) (sourceB2587 + difference 0 3) sourceC2587) = raw35874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35874; decide +kernel
    rw [ha]
    exact (canonical35874 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2587 + difference 3 1) (sourceB2587 + difference 1 3) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4955) := by
    have ha : (tripleCharges (sourceA2587 + difference 3 1) (sourceB2587 + difference 1 3) sourceC2587) = raw35875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35875; decide +kernel
    rw [ha]
    exact (canonical35875 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2587 + difference 3 2) (sourceB2587 + difference 2 3) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5336) := by
    have ha : (tripleCharges (sourceA2587 + difference 3 2) (sourceB2587 + difference 2 3) sourceC2587) = raw35876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35876; decide +kernel
    rw [ha]
    exact (canonical35876 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2587 + difference 3 4) (sourceB2587 + difference 4 3) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2587 + difference 3 4) (sourceB2587 + difference 4 3) sourceC2587) = raw35877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35877; decide +kernel
    rw [ha]
    exact (canonical35877 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2587 + difference 3 5) (sourceB2587 + difference 5 3) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2587 + difference 3 5) (sourceB2587 + difference 5 3) sourceC2587) = raw35878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35878; decide +kernel
    rw [ha]
    exact (canonical35878 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2587 + difference 4 0) (sourceB2587 + difference 0 4) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4665) := by
    have ha : (tripleCharges (sourceA2587 + difference 4 0) (sourceB2587 + difference 0 4) sourceC2587) = raw35879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35879; decide +kernel
    rw [ha]
    exact (canonical35879 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2587 + difference 4 1) (sourceB2587 + difference 1 4) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4957) := by
    have ha : (tripleCharges (sourceA2587 + difference 4 1) (sourceB2587 + difference 1 4) sourceC2587) = raw35880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35880; decide +kernel
    rw [ha]
    exact (canonical35880 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2587 + difference 4 2) (sourceB2587 + difference 2 4) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5372) := by
    have ha : (tripleCharges (sourceA2587 + difference 4 2) (sourceB2587 + difference 2 4) sourceC2587) = raw35881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35881; decide +kernel
    rw [ha]
    exact (canonical35881 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2587 + difference 4 3) (sourceB2587 + difference 3 4) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5376) := by
    have ha : (tripleCharges (sourceA2587 + difference 4 3) (sourceB2587 + difference 3 4) sourceC2587) = raw35882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35882; decide +kernel
    rw [ha]
    exact (canonical35882 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2587 + difference 4 5) (sourceB2587 + difference 5 4) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA2587 + difference 4 5) (sourceB2587 + difference 5 4) sourceC2587) = raw35883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35883; decide +kernel
    rw [ha]
    exact (canonical35883 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2587 + difference 5 0) (sourceB2587 + difference 0 5) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4664) := by
    have ha : (tripleCharges (sourceA2587 + difference 5 0) (sourceB2587 + difference 0 5) sourceC2587) = raw35884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35884; decide +kernel
    rw [ha]
    exact (canonical35884 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2587 + difference 5 1) (sourceB2587 + difference 1 5) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4954) := by
    have ha : (tripleCharges (sourceA2587 + difference 5 1) (sourceB2587 + difference 1 5) sourceC2587) = raw35885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35885; decide +kernel
    rw [ha]
    exact (canonical35885 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2587 + difference 5 2) (sourceB2587 + difference 2 5) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5038) := by
    have ha : (tripleCharges (sourceA2587 + difference 5 2) (sourceB2587 + difference 2 5) sourceC2587) = raw35886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35886; decide +kernel
    rw [ha]
    exact (canonical35886 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2587 + difference 5 3) (sourceB2587 + difference 3 5) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA2587 + difference 5 3) (sourceB2587 + difference 3 5) sourceC2587) = raw35887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35887; decide +kernel
    rw [ha]
    exact (canonical35887 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2587 + difference 5 4) (sourceB2587 + difference 4 5) sourceC2587) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2587 + difference 5 4) (sourceB2587 + difference 4 5) sourceC2587) = raw35888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2587 sourceB2587 sourceC2587 difference raw35888; decide +kernel
    rw [ha]
    exact (canonical35888 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2587 sourceB2587 sourceC2587
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2587, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2588 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2588 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2588 : Charge := ![0, 2, 1, -1, 0, -2]
def sourceForm2588 : Integer.Sparse Master := [(Sum.inr 2144, 1), (Sum.inr 2145, 1), (Sum.inr 2147, 1), (Sum.inr 2154, 1), (Sum.inr 2250, 1), (Sum.inr 3452, 1), (Sum.inr 3453, 1), (Sum.inr 3478, 1), (Sum.inr 3508, 1), (Sum.inr 3509, 1), (Sum.inr 3514, 1), (Sum.inr 3516, 1), (Sum.inr 3553, 1), (Sum.inr 3754, 1), (Sum.inr 3770, 1), (Sum.inr 3791, 1), (Sum.inr 3793, 1), (Sum.inr 3796, 1), (Sum.inr 3807, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1), (Sum.inr 3832, 1), (Sum.inr 3833, 1), (Sum.inr 3834, 2), (Sum.inr 3837, 1), (Sum.inr 3838, 1), (Sum.inr 3840, 1), (Sum.inr 3866, 1), (Sum.inr 3880, 1)]

theorem sourceEq2588 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2588 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2588 + difference 0 1) (sourceB2588 + difference 1 0) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA2588 + difference 0 1) (sourceB2588 + difference 1 0) sourceC2588) = raw35889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35889; decide +kernel
    rw [ha]
    exact (canonical35889 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2588 + difference 0 2) (sourceB2588 + difference 2 0) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3793) := by
    have ha : (tripleCharges (sourceA2588 + difference 0 2) (sourceB2588 + difference 2 0) sourceC2588) = raw35890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35890; decide +kernel
    rw [ha]
    exact (canonical35890 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2588 + difference 0 3) (sourceB2588 + difference 3 0) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA2588 + difference 0 3) (sourceB2588 + difference 3 0) sourceC2588) = raw35891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35891; decide +kernel
    rw [ha]
    exact (canonical35891 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2588 + difference 0 4) (sourceB2588 + difference 4 0) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2588 + difference 0 4) (sourceB2588 + difference 4 0) sourceC2588) = raw35892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35892; decide +kernel
    rw [ha]
    exact (canonical35892 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2588 + difference 0 5) (sourceB2588 + difference 5 0) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA2588 + difference 0 5) (sourceB2588 + difference 5 0) sourceC2588) = raw35893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35893; decide +kernel
    rw [ha]
    exact (canonical35893 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2588 + difference 1 0) (sourceB2588 + difference 0 1) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA2588 + difference 1 0) (sourceB2588 + difference 0 1) sourceC2588) = raw35894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35894; decide +kernel
    rw [ha]
    exact (canonical35894 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2588 + difference 1 2) (sourceB2588 + difference 2 1) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA2588 + difference 1 2) (sourceB2588 + difference 2 1) sourceC2588) = raw35895 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35895; decide +kernel
    rw [ha]
    exact (canonical35895 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2588 + difference 1 3) (sourceB2588 + difference 3 1) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA2588 + difference 1 3) (sourceB2588 + difference 3 1) sourceC2588) = raw35896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35896; decide +kernel
    rw [ha]
    exact (canonical35896 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2588 + difference 1 4) (sourceB2588 + difference 4 1) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA2588 + difference 1 4) (sourceB2588 + difference 4 1) sourceC2588) = raw35897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35897; decide +kernel
    rw [ha]
    exact (canonical35897 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2588 + difference 1 5) (sourceB2588 + difference 5 1) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA2588 + difference 1 5) (sourceB2588 + difference 5 1) sourceC2588) = raw35898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35898; decide +kernel
    rw [ha]
    exact (canonical35898 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2588 + difference 2 0) (sourceB2588 + difference 0 2) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2145) := by
    have ha : (tripleCharges (sourceA2588 + difference 2 0) (sourceB2588 + difference 0 2) sourceC2588) = raw35899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35899; decide +kernel
    rw [ha]
    exact (canonical35899 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2588 + difference 2 1) (sourceB2588 + difference 1 2) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3553) := by
    have ha : (tripleCharges (sourceA2588 + difference 2 1) (sourceB2588 + difference 1 2) sourceC2588) = raw35900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35900; decide +kernel
    rw [ha]
    exact (canonical35900 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2588 + difference 2 3) (sourceB2588 + difference 3 2) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA2588 + difference 2 3) (sourceB2588 + difference 3 2) sourceC2588) = raw35901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35901; decide +kernel
    rw [ha]
    exact (canonical35901 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2588 + difference 2 4) (sourceB2588 + difference 4 2) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA2588 + difference 2 4) (sourceB2588 + difference 4 2) sourceC2588) = raw35902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35902; decide +kernel
    rw [ha]
    exact (canonical35902 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2588 + difference 2 5) (sourceB2588 + difference 5 2) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA2588 + difference 2 5) (sourceB2588 + difference 5 2) sourceC2588) = raw35903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35903; decide +kernel
    rw [ha]
    exact (canonical35903 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2588 + difference 3 0) (sourceB2588 + difference 0 3) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2154) := by
    have ha : (tripleCharges (sourceA2588 + difference 3 0) (sourceB2588 + difference 0 3) sourceC2588) = raw35904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35904; decide +kernel
    rw [ha]
    exact (canonical35904 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2588 + difference 3 1) (sourceB2588 + difference 1 3) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3508) := by
    have ha : (tripleCharges (sourceA2588 + difference 3 1) (sourceB2588 + difference 1 3) sourceC2588) = raw35905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35905; decide +kernel
    rw [ha]
    exact (canonical35905 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2588 + difference 3 2) (sourceB2588 + difference 2 3) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3754) := by
    have ha : (tripleCharges (sourceA2588 + difference 3 2) (sourceB2588 + difference 2 3) sourceC2588) = raw35906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35906; decide +kernel
    rw [ha]
    exact (canonical35906 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2588 + difference 3 4) (sourceB2588 + difference 4 3) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2588 + difference 3 4) (sourceB2588 + difference 4 3) sourceC2588) = raw35907 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35907; decide +kernel
    rw [ha]
    exact (canonical35907 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2588 + difference 3 5) (sourceB2588 + difference 5 3) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2588 + difference 3 5) (sourceB2588 + difference 5 3) sourceC2588) = raw35908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35908; decide +kernel
    rw [ha]
    exact (canonical35908 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2588 + difference 4 0) (sourceB2588 + difference 0 4) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2144) := by
    have ha : (tripleCharges (sourceA2588 + difference 4 0) (sourceB2588 + difference 0 4) sourceC2588) = raw35909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35909; decide +kernel
    rw [ha]
    exact (canonical35909 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2588 + difference 4 1) (sourceB2588 + difference 1 4) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3509) := by
    have ha : (tripleCharges (sourceA2588 + difference 4 1) (sourceB2588 + difference 1 4) sourceC2588) = raw35910 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35910; decide +kernel
    rw [ha]
    exact (canonical35910 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2588 + difference 4 2) (sourceB2588 + difference 2 4) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3791) := by
    have ha : (tripleCharges (sourceA2588 + difference 4 2) (sourceB2588 + difference 2 4) sourceC2588) = raw35911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35911; decide +kernel
    rw [ha]
    exact (canonical35911 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2588 + difference 4 3) (sourceB2588 + difference 3 4) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3833) := by
    have ha : (tripleCharges (sourceA2588 + difference 4 3) (sourceB2588 + difference 3 4) sourceC2588) = raw35912 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35912; decide +kernel
    rw [ha]
    exact (canonical35912 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2588 + difference 4 5) (sourceB2588 + difference 5 4) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA2588 + difference 4 5) (sourceB2588 + difference 5 4) sourceC2588) = raw35913 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35913; decide +kernel
    rw [ha]
    exact (canonical35913 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2588 + difference 5 0) (sourceB2588 + difference 0 5) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2147) := by
    have ha : (tripleCharges (sourceA2588 + difference 5 0) (sourceB2588 + difference 0 5) sourceC2588) = raw35914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35914; decide +kernel
    rw [ha]
    exact (canonical35914 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2588 + difference 5 1) (sourceB2588 + difference 1 5) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3452) := by
    have ha : (tripleCharges (sourceA2588 + difference 5 1) (sourceB2588 + difference 1 5) sourceC2588) = raw35915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35915; decide +kernel
    rw [ha]
    exact (canonical35915 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2588 + difference 5 2) (sourceB2588 + difference 2 5) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3453) := by
    have ha : (tripleCharges (sourceA2588 + difference 5 2) (sourceB2588 + difference 2 5) sourceC2588) = raw35916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35916; decide +kernel
    rw [ha]
    exact (canonical35916 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2588 + difference 5 3) (sourceB2588 + difference 3 5) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2588 + difference 5 3) (sourceB2588 + difference 3 5) sourceC2588) = raw35917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35917; decide +kernel
    rw [ha]
    exact (canonical35917 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2588 + difference 5 4) (sourceB2588 + difference 4 5) sourceC2588) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2588 + difference 5 4) (sourceB2588 + difference 4 5) sourceC2588) = raw35918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2588 sourceB2588 sourceC2588 difference raw35918; decide +kernel
    rw [ha]
    exact (canonical35918 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2588 sourceB2588 sourceC2588
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2588, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2589 : Charge := ![0, 2, 1, -1, 0, -2]
def sourceB2589 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2589 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceForm2589 : Integer.Sparse Master := [(Sum.inr 5051, 1), (Sum.inr 5053, 1), (Sum.inr 5056, 1), (Sum.inr 5082, 1), (Sum.inr 5121, 1), (Sum.inr 5123, 1), (Sum.inr 5143, 1), (Sum.inr 5223, 1), (Sum.inr 5224, 1), (Sum.inr 5226, 1), (Sum.inr 5228, 1), (Sum.inr 5231, 1), (Sum.inr 5243, 1), (Sum.inr 5342, 1), (Sum.inr 5344, 1), (Sum.inr 5345, 1), (Sum.inr 5352, 1), (Sum.inr 5353, 1), (Sum.inr 5354, 1), (Sum.inr 5357, 1), (Sum.inr 5360, 1), (Sum.inr 5367, 1), (Sum.inr 5374, 1), (Sum.inr 5378, 1), (Sum.inr 5379, 1), (Sum.inr 5380, 1), (Sum.inr 5384, 1), (Sum.inr 5387, 1), (Sum.inr 5388, 1), (Sum.inr 5393, 1)]

theorem sourceEq2589 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2589 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2589 + difference 0 1) (sourceB2589 + difference 1 0) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2589 + difference 0 1) (sourceB2589 + difference 1 0) sourceC2589) = raw35919 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35919; decide +kernel
    rw [ha]
    exact (canonical35919 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2589 + difference 0 2) (sourceB2589 + difference 2 0) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2589 + difference 0 2) (sourceB2589 + difference 2 0) sourceC2589) = raw35618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35618; decide +kernel
    rw [ha]
    exact (canonical35618 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2589 + difference 0 3) (sourceB2589 + difference 3 0) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA2589 + difference 0 3) (sourceB2589 + difference 3 0) sourceC2589) = raw35920 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35920; decide +kernel
    rw [ha]
    exact (canonical35920 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2589 + difference 0 4) (sourceB2589 + difference 4 0) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5345) := by
    have ha : (tripleCharges (sourceA2589 + difference 0 4) (sourceB2589 + difference 4 0) sourceC2589) = raw35824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35824; decide +kernel
    rw [ha]
    exact (canonical35824 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2589 + difference 0 5) (sourceB2589 + difference 5 0) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2589 + difference 0 5) (sourceB2589 + difference 5 0) sourceC2589) = raw35921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35921; decide +kernel
    rw [ha]
    exact (canonical35921 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2589 + difference 1 0) (sourceB2589 + difference 0 1) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5143) := by
    have ha : (tripleCharges (sourceA2589 + difference 1 0) (sourceB2589 + difference 0 1) sourceC2589) = raw35922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35922; decide +kernel
    rw [ha]
    exact (canonical35922 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2589 + difference 1 2) (sourceB2589 + difference 2 1) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2589 + difference 1 2) (sourceB2589 + difference 2 1) sourceC2589) = raw35622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35622; decide +kernel
    rw [ha]
    exact (canonical35622 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2589 + difference 1 3) (sourceB2589 + difference 3 1) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5121) := by
    have ha : (tripleCharges (sourceA2589 + difference 1 3) (sourceB2589 + difference 3 1) sourceC2589) = raw35923 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35923; decide +kernel
    rw [ha]
    exact (canonical35923 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2589 + difference 1 4) (sourceB2589 + difference 4 1) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2589 + difference 1 4) (sourceB2589 + difference 4 1) sourceC2589) = raw35828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35828; decide +kernel
    rw [ha]
    exact (canonical35828 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2589 + difference 1 5) (sourceB2589 + difference 5 1) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5051) := by
    have ha : (tripleCharges (sourceA2589 + difference 1 5) (sourceB2589 + difference 5 1) sourceC2589) = raw35924 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35924; decide +kernel
    rw [ha]
    exact (canonical35924 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2589 + difference 2 0) (sourceB2589 + difference 0 2) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5224) := by
    have ha : (tripleCharges (sourceA2589 + difference 2 0) (sourceB2589 + difference 0 2) sourceC2589) = raw35925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35925; decide +kernel
    rw [ha]
    exact (canonical35925 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2589 + difference 2 1) (sourceB2589 + difference 1 2) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA2589 + difference 2 1) (sourceB2589 + difference 1 2) sourceC2589) = raw35926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35926; decide +kernel
    rw [ha]
    exact (canonical35926 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2589 + difference 2 3) (sourceB2589 + difference 3 2) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5342) := by
    have ha : (tripleCharges (sourceA2589 + difference 2 3) (sourceB2589 + difference 3 2) sourceC2589) = raw35927 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35927; decide +kernel
    rw [ha]
    exact (canonical35927 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2589 + difference 2 4) (sourceB2589 + difference 4 2) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA2589 + difference 2 4) (sourceB2589 + difference 4 2) sourceC2589) = raw35833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35833; decide +kernel
    rw [ha]
    exact (canonical35833 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2589 + difference 2 5) (sourceB2589 + difference 5 2) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5053) := by
    have ha : (tripleCharges (sourceA2589 + difference 2 5) (sourceB2589 + difference 5 2) sourceC2589) = raw35928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35928; decide +kernel
    rw [ha]
    exact (canonical35928 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2589 + difference 3 0) (sourceB2589 + difference 0 3) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA2589 + difference 3 0) (sourceB2589 + difference 0 3) sourceC2589) = raw35929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35929; decide +kernel
    rw [ha]
    exact (canonical35929 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2589 + difference 3 1) (sourceB2589 + difference 1 3) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2589 + difference 3 1) (sourceB2589 + difference 1 3) sourceC2589) = raw35930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35930; decide +kernel
    rw [ha]
    exact (canonical35930 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2589 + difference 3 2) (sourceB2589 + difference 2 3) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2589 + difference 3 2) (sourceB2589 + difference 2 3) sourceC2589) = raw35630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35630; decide +kernel
    rw [ha]
    exact (canonical35630 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2589 + difference 3 4) (sourceB2589 + difference 4 3) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2589 + difference 3 4) (sourceB2589 + difference 4 3) sourceC2589) = raw35837 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35837; decide +kernel
    rw [ha]
    exact (canonical35837 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2589 + difference 3 5) (sourceB2589 + difference 5 3) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5243) := by
    have ha : (tripleCharges (sourceA2589 + difference 3 5) (sourceB2589 + difference 5 3) sourceC2589) = raw35931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35931; decide +kernel
    rw [ha]
    exact (canonical35931 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2589 + difference 4 0) (sourceB2589 + difference 0 4) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5223) := by
    have ha : (tripleCharges (sourceA2589 + difference 4 0) (sourceB2589 + difference 0 4) sourceC2589) = raw35739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35739; decide +kernel
    rw [ha]
    exact (canonical35739 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2589 + difference 4 1) (sourceB2589 + difference 1 4) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA2589 + difference 4 1) (sourceB2589 + difference 1 4) sourceC2589) = raw35740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35740; decide +kernel
    rw [ha]
    exact (canonical35740 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2589 + difference 4 2) (sourceB2589 + difference 2 4) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2589 + difference 4 2) (sourceB2589 + difference 2 4) sourceC2589) = raw35635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35635; decide +kernel
    rw [ha]
    exact (canonical35635 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2589 + difference 4 3) (sourceB2589 + difference 3 4) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5357) := by
    have ha : (tripleCharges (sourceA2589 + difference 4 3) (sourceB2589 + difference 3 4) sourceC2589) = raw35741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35741; decide +kernel
    rw [ha]
    exact (canonical35741 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2589 + difference 4 5) (sourceB2589 + difference 5 4) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5082) := by
    have ha : (tripleCharges (sourceA2589 + difference 4 5) (sourceB2589 + difference 5 4) sourceC2589) = raw35742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35742; decide +kernel
    rw [ha]
    exact (canonical35742 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2589 + difference 5 0) (sourceB2589 + difference 0 5) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2589 + difference 5 0) (sourceB2589 + difference 0 5) sourceC2589) = raw35623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35623; decide +kernel
    rw [ha]
    exact (canonical35623 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2589 + difference 5 1) (sourceB2589 + difference 1 5) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2589 + difference 5 1) (sourceB2589 + difference 1 5) sourceC2589) = raw35624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35624; decide +kernel
    rw [ha]
    exact (canonical35624 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2589 + difference 5 2) (sourceB2589 + difference 2 5) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2589 + difference 5 2) (sourceB2589 + difference 2 5) sourceC2589) = raw35596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35596; decide +kernel
    rw [ha]
    exact (canonical35596 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2589 + difference 5 3) (sourceB2589 + difference 3 5) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2589 + difference 5 3) (sourceB2589 + difference 3 5) sourceC2589) = raw35625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35625; decide +kernel
    rw [ha]
    exact (canonical35625 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2589 + difference 5 4) (sourceB2589 + difference 4 5) sourceC2589) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2589 + difference 5 4) (sourceB2589 + difference 4 5) sourceC2589) = raw35586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2589 sourceB2589 sourceC2589 difference raw35586; decide +kernel
    rw [ha]
    exact (canonical35586 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2589 sourceB2589 sourceC2589
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2589, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2590 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2590 : Charge := ![0, 3, 0, -1, -1, -1]
def sourceC2590 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceForm2590 : Integer.Sparse Master := [(Sum.inr 4379, 1), (Sum.inr 4380, 1), (Sum.inr 4381, 2), (Sum.inr 4489, 1), (Sum.inr 4980, 1), (Sum.inr 4982, 1), (Sum.inr 4983, 2), (Sum.inr 5028, 1), (Sum.inr 5046, 2), (Sum.inr 5093, 1), (Sum.inr 5110, 2), (Sum.inr 5203, 1), (Sum.inr 5227, 1), (Sum.inr 5228, 2), (Sum.inr 5237, 2), (Sum.inr 5238, 2), (Sum.inr 5290, 1), (Sum.inr 5304, 2), (Sum.inr 5422, 1), (Sum.inr 5450, 1), (Sum.inr 5451, 2)]

theorem sourceEq2590 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2590 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2590 + difference 0 1) (sourceB2590 + difference 1 0) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA2590 + difference 0 1) (sourceB2590 + difference 1 0) sourceC2590) = raw35932 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35932; decide +kernel
    rw [ha]
    exact (canonical35932 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2590 + difference 0 2) (sourceB2590 + difference 2 0) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5093) := by
    have ha : (tripleCharges (sourceA2590 + difference 0 2) (sourceB2590 + difference 2 0) sourceC2590) = raw35933 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35933; decide +kernel
    rw [ha]
    exact (canonical35933 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2590 + difference 0 3) (sourceB2590 + difference 3 0) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA2590 + difference 0 3) (sourceB2590 + difference 3 0) sourceC2590) = raw16219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw16219; decide +kernel
    rw [ha]
    exact (canonical16219 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2590 + difference 0 4) (sourceB2590 + difference 4 0) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA2590 + difference 0 4) (sourceB2590 + difference 4 0) sourceC2590) = raw35934 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35934; decide +kernel
    rw [ha]
    exact (canonical35934 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2590 + difference 0 5) (sourceB2590 + difference 5 0) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA2590 + difference 0 5) (sourceB2590 + difference 5 0) sourceC2590) = raw35935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35935; decide +kernel
    rw [ha]
    exact (canonical35935 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2590 + difference 1 0) (sourceB2590 + difference 0 1) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2590 + difference 1 0) (sourceB2590 + difference 0 1) sourceC2590) = raw16234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw16234; decide +kernel
    rw [ha]
    exact (canonical16234 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2590 + difference 1 2) (sourceB2590 + difference 2 1) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA2590 + difference 1 2) (sourceB2590 + difference 2 1) sourceC2590) = raw16236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw16236; decide +kernel
    rw [ha]
    exact (canonical16236 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2590 + difference 1 3) (sourceB2590 + difference 3 1) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2590 + difference 1 3) (sourceB2590 + difference 3 1) sourceC2590) = raw28233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw28233; decide +kernel
    rw [ha]
    exact (canonical28233 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2590 + difference 1 4) (sourceB2590 + difference 4 1) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2590 + difference 1 4) (sourceB2590 + difference 4 1) sourceC2590) = raw16237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw16237; decide +kernel
    rw [ha]
    exact (canonical16237 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2590 + difference 1 5) (sourceB2590 + difference 5 1) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2590 + difference 1 5) (sourceB2590 + difference 5 1) sourceC2590) = raw16238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw16238; decide +kernel
    rw [ha]
    exact (canonical16238 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2590 + difference 2 0) (sourceB2590 + difference 0 2) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4980) := by
    have ha : (tripleCharges (sourceA2590 + difference 2 0) (sourceB2590 + difference 0 2) sourceC2590) = raw32551 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw32551; decide +kernel
    rw [ha]
    exact (canonical32551 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2590 + difference 2 1) (sourceB2590 + difference 1 2) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4379) := by
    have ha : (tripleCharges (sourceA2590 + difference 2 1) (sourceB2590 + difference 1 2) sourceC2590) = raw35936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35936; decide +kernel
    rw [ha]
    exact (canonical35936 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2590 + difference 2 3) (sourceB2590 + difference 3 2) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2590 + difference 2 3) (sourceB2590 + difference 3 2) sourceC2590) = raw16230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw16230; decide +kernel
    rw [ha]
    exact (canonical16230 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2590 + difference 2 4) (sourceB2590 + difference 4 2) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2590 + difference 2 4) (sourceB2590 + difference 4 2) sourceC2590) = raw35937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35937; decide +kernel
    rw [ha]
    exact (canonical35937 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2590 + difference 2 5) (sourceB2590 + difference 5 2) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5227) := by
    have ha : (tripleCharges (sourceA2590 + difference 2 5) (sourceB2590 + difference 5 2) sourceC2590) = raw34465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw34465; decide +kernel
    rw [ha]
    exact (canonical34465 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2590 + difference 3 0) (sourceB2590 + difference 0 3) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4983) := by
    have ha : (tripleCharges (sourceA2590 + difference 3 0) (sourceB2590 + difference 0 3) sourceC2590) = raw32554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw32554; decide +kernel
    rw [ha]
    exact (canonical32554 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2590 + difference 3 1) (sourceB2590 + difference 1 3) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4381) := by
    have ha : (tripleCharges (sourceA2590 + difference 3 1) (sourceB2590 + difference 1 3) sourceC2590) = raw35938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35938; decide +kernel
    rw [ha]
    exact (canonical35938 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2590 + difference 3 2) (sourceB2590 + difference 2 3) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5046) := by
    have ha : (tripleCharges (sourceA2590 + difference 3 2) (sourceB2590 + difference 2 3) sourceC2590) = raw35939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35939; decide +kernel
    rw [ha]
    exact (canonical35939 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2590 + difference 3 4) (sourceB2590 + difference 4 3) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2590 + difference 3 4) (sourceB2590 + difference 4 3) sourceC2590) = raw35940 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35940; decide +kernel
    rw [ha]
    exact (canonical35940 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2590 + difference 3 5) (sourceB2590 + difference 5 3) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2590 + difference 3 5) (sourceB2590 + difference 5 3) sourceC2590) = raw35941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35941; decide +kernel
    rw [ha]
    exact (canonical35941 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2590 + difference 4 0) (sourceB2590 + difference 0 4) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4983) := by
    have ha : (tripleCharges (sourceA2590 + difference 4 0) (sourceB2590 + difference 0 4) sourceC2590) = raw29954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw29954; decide +kernel
    rw [ha]
    exact (canonical29954 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2590 + difference 4 1) (sourceB2590 + difference 1 4) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4381) := by
    have ha : (tripleCharges (sourceA2590 + difference 4 1) (sourceB2590 + difference 1 4) sourceC2590) = raw35088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35088; decide +kernel
    rw [ha]
    exact (canonical35088 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2590 + difference 4 2) (sourceB2590 + difference 2 4) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5046) := by
    have ha : (tripleCharges (sourceA2590 + difference 4 2) (sourceB2590 + difference 2 4) sourceC2590) = raw35089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35089; decide +kernel
    rw [ha]
    exact (canonical35089 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2590 + difference 4 3) (sourceB2590 + difference 3 4) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2590 + difference 4 3) (sourceB2590 + difference 3 4) sourceC2590) = raw16240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw16240; decide +kernel
    rw [ha]
    exact (canonical16240 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2590 + difference 4 5) (sourceB2590 + difference 5 4) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2590 + difference 4 5) (sourceB2590 + difference 5 4) sourceC2590) = raw35090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35090; decide +kernel
    rw [ha]
    exact (canonical35090 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2590 + difference 5 0) (sourceB2590 + difference 0 5) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4982) := by
    have ha : (tripleCharges (sourceA2590 + difference 5 0) (sourceB2590 + difference 0 5) sourceC2590) = raw28243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw28243; decide +kernel
    rw [ha]
    exact (canonical28243 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2590 + difference 5 1) (sourceB2590 + difference 1 5) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4380) := by
    have ha : (tripleCharges (sourceA2590 + difference 5 1) (sourceB2590 + difference 1 5) sourceC2590) = raw35942 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35942; decide +kernel
    rw [ha]
    exact (canonical35942 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2590 + difference 5 2) (sourceB2590 + difference 2 5) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5028) := by
    have ha : (tripleCharges (sourceA2590 + difference 5 2) (sourceB2590 + difference 2 5) sourceC2590) = raw35943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35943; decide +kernel
    rw [ha]
    exact (canonical35943 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2590 + difference 5 3) (sourceB2590 + difference 3 5) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2590 + difference 5 3) (sourceB2590 + difference 3 5) sourceC2590) = raw16245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw16245; decide +kernel
    rw [ha]
    exact (canonical16245 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2590 + difference 5 4) (sourceB2590 + difference 4 5) sourceC2590) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2590 + difference 5 4) (sourceB2590 + difference 4 5) sourceC2590) = raw35944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2590 sourceB2590 sourceC2590 difference raw35944; decide +kernel
    rw [ha]
    exact (canonical35944 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2590 sourceB2590 sourceC2590
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2590, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2591 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2591 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2591 : Charge := ![0, 3, 0, -1, -1, -1]
def sourceForm2591 : Integer.Sparse Master := [(Sum.inr 4679, 1), (Sum.inr 4686, 1), (Sum.inr 4689, 2), (Sum.inr 4696, 1), (Sum.inr 4697, 1), (Sum.inr 4701, 2), (Sum.inr 4838, 1), (Sum.inr 4879, 1), (Sum.inr 5116, 1), (Sum.inr 5151, 2), (Sum.inr 5217, 2), (Sum.inr 5226, 2), (Sum.inr 5227, 1), (Sum.inr 5236, 2), (Sum.inr 5237, 2), (Sum.inr 5247, 1), (Sum.inr 5271, 2), (Sum.inr 5273, 1), (Sum.inr 5286, 1), (Sum.inr 5299, 2), (Sum.inr 5301, 1)]

theorem sourceEq2591 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2591 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2591 + difference 0 1) (sourceB2591 + difference 1 0) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2591 + difference 0 1) (sourceB2591 + difference 1 0) sourceC2591) = raw35945 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35945; decide +kernel
    rw [ha]
    exact (canonical35945 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2591 + difference 0 2) (sourceB2591 + difference 2 0) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA2591 + difference 0 2) (sourceB2591 + difference 2 0) sourceC2591) = raw35946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35946; decide +kernel
    rw [ha]
    exact (canonical35946 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2591 + difference 0 3) (sourceB2591 + difference 3 0) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA2591 + difference 0 3) (sourceB2591 + difference 3 0) sourceC2591) = raw35947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35947; decide +kernel
    rw [ha]
    exact (canonical35947 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2591 + difference 0 4) (sourceB2591 + difference 4 0) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA2591 + difference 0 4) (sourceB2591 + difference 4 0) sourceC2591) = raw35948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35948; decide +kernel
    rw [ha]
    exact (canonical35948 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2591 + difference 0 5) (sourceB2591 + difference 5 0) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA2591 + difference 0 5) (sourceB2591 + difference 5 0) sourceC2591) = raw35949 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35949; decide +kernel
    rw [ha]
    exact (canonical35949 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2591 + difference 1 0) (sourceB2591 + difference 0 1) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA2591 + difference 1 0) (sourceB2591 + difference 0 1) sourceC2591) = raw35950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35950; decide +kernel
    rw [ha]
    exact (canonical35950 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2591 + difference 1 2) (sourceB2591 + difference 2 1) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA2591 + difference 1 2) (sourceB2591 + difference 2 1) sourceC2591) = raw35951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35951; decide +kernel
    rw [ha]
    exact (canonical35951 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2591 + difference 1 3) (sourceB2591 + difference 3 1) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA2591 + difference 1 3) (sourceB2591 + difference 3 1) sourceC2591) = raw35952 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35952; decide +kernel
    rw [ha]
    exact (canonical35952 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2591 + difference 1 4) (sourceB2591 + difference 4 1) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA2591 + difference 1 4) (sourceB2591 + difference 4 1) sourceC2591) = raw35953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35953; decide +kernel
    rw [ha]
    exact (canonical35953 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2591 + difference 1 5) (sourceB2591 + difference 5 1) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA2591 + difference 1 5) (sourceB2591 + difference 5 1) sourceC2591) = raw35954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35954; decide +kernel
    rw [ha]
    exact (canonical35954 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2591 + difference 2 0) (sourceB2591 + difference 0 2) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4696) := by
    have ha : (tripleCharges (sourceA2591 + difference 2 0) (sourceB2591 + difference 0 2) sourceC2591) = raw35955 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35955; decide +kernel
    rw [ha]
    exact (canonical35955 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2591 + difference 2 1) (sourceB2591 + difference 1 2) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2591 + difference 2 1) (sourceB2591 + difference 1 2) sourceC2591) = raw35956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35956; decide +kernel
    rw [ha]
    exact (canonical35956 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2591 + difference 2 3) (sourceB2591 + difference 3 2) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2591 + difference 2 3) (sourceB2591 + difference 3 2) sourceC2591) = raw35957 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35957; decide +kernel
    rw [ha]
    exact (canonical35957 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2591 + difference 2 4) (sourceB2591 + difference 4 2) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2591 + difference 2 4) (sourceB2591 + difference 4 2) sourceC2591) = raw35958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35958; decide +kernel
    rw [ha]
    exact (canonical35958 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2591 + difference 2 5) (sourceB2591 + difference 5 2) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5227) := by
    have ha : (tripleCharges (sourceA2591 + difference 2 5) (sourceB2591 + difference 5 2) sourceC2591) = raw35959 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35959; decide +kernel
    rw [ha]
    exact (canonical35959 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2591 + difference 3 0) (sourceB2591 + difference 0 3) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4701) := by
    have ha : (tripleCharges (sourceA2591 + difference 3 0) (sourceB2591 + difference 0 3) sourceC2591) = raw35960 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35960; decide +kernel
    rw [ha]
    exact (canonical35960 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2591 + difference 3 1) (sourceB2591 + difference 1 3) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4689) := by
    have ha : (tripleCharges (sourceA2591 + difference 3 1) (sourceB2591 + difference 1 3) sourceC2591) = raw35961 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35961; decide +kernel
    rw [ha]
    exact (canonical35961 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2591 + difference 3 2) (sourceB2591 + difference 2 3) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5217) := by
    have ha : (tripleCharges (sourceA2591 + difference 3 2) (sourceB2591 + difference 2 3) sourceC2591) = raw35962 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35962; decide +kernel
    rw [ha]
    exact (canonical35962 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2591 + difference 3 4) (sourceB2591 + difference 4 3) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA2591 + difference 3 4) (sourceB2591 + difference 4 3) sourceC2591) = raw35963 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35963; decide +kernel
    rw [ha]
    exact (canonical35963 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2591 + difference 3 5) (sourceB2591 + difference 5 3) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2591 + difference 3 5) (sourceB2591 + difference 5 3) sourceC2591) = raw35964 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35964; decide +kernel
    rw [ha]
    exact (canonical35964 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2591 + difference 4 0) (sourceB2591 + difference 0 4) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4701) := by
    have ha : (tripleCharges (sourceA2591 + difference 4 0) (sourceB2591 + difference 0 4) sourceC2591) = raw35965 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35965; decide +kernel
    rw [ha]
    exact (canonical35965 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2591 + difference 4 1) (sourceB2591 + difference 1 4) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4689) := by
    have ha : (tripleCharges (sourceA2591 + difference 4 1) (sourceB2591 + difference 1 4) sourceC2591) = raw35966 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35966; decide +kernel
    rw [ha]
    exact (canonical35966 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2591 + difference 4 2) (sourceB2591 + difference 2 4) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5217) := by
    have ha : (tripleCharges (sourceA2591 + difference 4 2) (sourceB2591 + difference 2 4) sourceC2591) = raw35967 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35967; decide +kernel
    rw [ha]
    exact (canonical35967 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2591 + difference 4 3) (sourceB2591 + difference 3 4) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA2591 + difference 4 3) (sourceB2591 + difference 3 4) sourceC2591) = raw35968 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35968; decide +kernel
    rw [ha]
    exact (canonical35968 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2591 + difference 4 5) (sourceB2591 + difference 5 4) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2591 + difference 4 5) (sourceB2591 + difference 5 4) sourceC2591) = raw35969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35969; decide +kernel
    rw [ha]
    exact (canonical35969 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2591 + difference 5 0) (sourceB2591 + difference 0 5) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4697) := by
    have ha : (tripleCharges (sourceA2591 + difference 5 0) (sourceB2591 + difference 0 5) sourceC2591) = raw35970 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35970; decide +kernel
    rw [ha]
    exact (canonical35970 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2591 + difference 5 1) (sourceB2591 + difference 1 5) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4686) := by
    have ha : (tripleCharges (sourceA2591 + difference 5 1) (sourceB2591 + difference 1 5) sourceC2591) = raw35971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35971; decide +kernel
    rw [ha]
    exact (canonical35971 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2591 + difference 5 2) (sourceB2591 + difference 2 5) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5116) := by
    have ha : (tripleCharges (sourceA2591 + difference 5 2) (sourceB2591 + difference 2 5) sourceC2591) = raw35972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35972; decide +kernel
    rw [ha]
    exact (canonical35972 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2591 + difference 5 3) (sourceB2591 + difference 3 5) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA2591 + difference 5 3) (sourceB2591 + difference 3 5) sourceC2591) = raw35973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35973; decide +kernel
    rw [ha]
    exact (canonical35973 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2591 + difference 5 4) (sourceB2591 + difference 4 5) sourceC2591) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA2591 + difference 5 4) (sourceB2591 + difference 4 5) sourceC2591) = raw35974 := by
      apply Matrix.ext; unfold tripleCharges sourceA2591 sourceB2591 sourceC2591 difference raw35974; decide +kernel
    rw [ha]
    exact (canonical35974 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2591 sourceB2591 sourceC2591
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2591, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
