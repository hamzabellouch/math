import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical111
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical127
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical131
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical151
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical186
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical187
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical188
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical191
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical206
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical209
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical217
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical220
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical221
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical222
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical223
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical232
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical250
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical251
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical252
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical253
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical254
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical255
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical256

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2368 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2368 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2368 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceForm2368 : Integer.Sparse Master := [(Sum.inr 2422, 1), (Sum.inr 2822, 1), (Sum.inr 2824, 1), (Sum.inr 2826, 1), (Sum.inr 2924, 1), (Sum.inr 3779, 1), (Sum.inr 4091, -1)]

theorem sourceEq2368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2368 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2368 + difference 0 1) (sourceB2368 + difference 1 0) sourceC2368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3779) := by
    have ha : (tripleCharges (sourceA2368 + difference 0 1) (sourceB2368 + difference 1 0) sourceC2368) = raw32472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2368 sourceB2368 sourceC2368 difference raw32472; decide +kernel
    rw [ha]
    exact (canonical32472 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2368 + difference 1 1) (sourceB2368 + difference 1 1) sourceC2368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2368 + difference 1 1) (sourceB2368 + difference 1 1) sourceC2368) = raw23905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2368 sourceB2368 sourceC2368 difference raw23905; decide +kernel
    rw [ha]
    exact (canonical23905 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2368 + difference 2 1) (sourceB2368 + difference 1 2) sourceC2368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2826) := by
    have ha : (tripleCharges (sourceA2368 + difference 2 1) (sourceB2368 + difference 1 2) sourceC2368) = raw32473 := by
      apply Matrix.ext; unfold tripleCharges sourceA2368 sourceB2368 sourceC2368 difference raw32473; decide +kernel
    rw [ha]
    exact (canonical32473 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2368 + difference 3 1) (sourceB2368 + difference 1 3) sourceC2368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2822) := by
    have ha : (tripleCharges (sourceA2368 + difference 3 1) (sourceB2368 + difference 1 3) sourceC2368) = raw32474 := by
      apply Matrix.ext; unfold tripleCharges sourceA2368 sourceB2368 sourceC2368 difference raw32474; decide +kernel
    rw [ha]
    exact (canonical32474 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2368 + difference 4 1) (sourceB2368 + difference 1 4) sourceC2368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2824) := by
    have ha : (tripleCharges (sourceA2368 + difference 4 1) (sourceB2368 + difference 1 4) sourceC2368) = raw32475 := by
      apply Matrix.ext; unfold tripleCharges sourceA2368 sourceB2368 sourceC2368 difference raw32475; decide +kernel
    rw [ha]
    exact (canonical32475 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2368 + difference 5 1) (sourceB2368 + difference 1 5) sourceC2368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2422) := by
    have ha : (tripleCharges (sourceA2368 + difference 5 1) (sourceB2368 + difference 1 5) sourceC2368) = raw32476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2368 sourceB2368 sourceC2368 difference raw32476; decide +kernel
    rw [ha]
    exact (canonical32476 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2368 + sourceB2368) sourceC2368) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2368 + sourceB2368) sourceC2368) = raw23911 := by
      apply Matrix.ext; unfold doubleCharges sourceA2368 sourceB2368 sourceC2368 raw23911; decide +kernel
    rw [ha]
    exact (canonical23911 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2368 sourceB2368 sourceC2368
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2368, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2369 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceB2369 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2369 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2369 : Integer.Sparse Master := [(Sum.inr 4802, 1), (Sum.inr 4803, 1), (Sum.inr 4805, 1), (Sum.inr 4816, 1), (Sum.inr 4852, 1), (Sum.inr 5055, 1), (Sum.inr 5056, 1), (Sum.inr 5057, 1), (Sum.inr 5058, 1), (Sum.inr 5060, 1), (Sum.inr 5073, 1), (Sum.inr 5074, 1), (Sum.inr 5076, 1), (Sum.inr 5086, 1), (Sum.inr 5091, 1), (Sum.inr 5101, 1), (Sum.inr 5134, 1), (Sum.inr 5145, 1), (Sum.inr 5146, 1), (Sum.inr 5148, 1), (Sum.inr 5149, 1), (Sum.inr 5150, 1), (Sum.inr 5154, 1), (Sum.inr 5155, 1), (Sum.inr 5169, 1), (Sum.inr 5170, 1), (Sum.inr 5172, 1), (Sum.inr 5191, 1), (Sum.inr 5192, 1), (Sum.inr 5204, 1)]

theorem sourceEq2369 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2369 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2369 + difference 0 1) (sourceB2369 + difference 1 0) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2369 + difference 0 1) (sourceB2369 + difference 1 0) sourceC2369) = raw32477 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32477; decide +kernel
    rw [ha]
    exact (canonical32477 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2369 + difference 0 2) (sourceB2369 + difference 2 0) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2369 + difference 0 2) (sourceB2369 + difference 2 0) sourceC2369) = raw32227 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32227; decide +kernel
    rw [ha]
    exact (canonical32227 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2369 + difference 0 3) (sourceB2369 + difference 3 0) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2369 + difference 0 3) (sourceB2369 + difference 3 0) sourceC2369) = raw32478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32478; decide +kernel
    rw [ha]
    exact (canonical32478 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2369 + difference 0 4) (sourceB2369 + difference 4 0) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5058) := by
    have ha : (tripleCharges (sourceA2369 + difference 0 4) (sourceB2369 + difference 4 0) sourceC2369) = raw32316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32316; decide +kernel
    rw [ha]
    exact (canonical32316 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2369 + difference 0 5) (sourceB2369 + difference 5 0) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5055) := by
    have ha : (tripleCharges (sourceA2369 + difference 0 5) (sourceB2369 + difference 5 0) sourceC2369) = raw32479 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32479; decide +kernel
    rw [ha]
    exact (canonical32479 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2369 + difference 1 0) (sourceB2369 + difference 0 1) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA2369 + difference 1 0) (sourceB2369 + difference 0 1) sourceC2369) = raw32480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32480; decide +kernel
    rw [ha]
    exact (canonical32480 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2369 + difference 1 2) (sourceB2369 + difference 2 1) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2369 + difference 1 2) (sourceB2369 + difference 2 1) sourceC2369) = raw32232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32232; decide +kernel
    rw [ha]
    exact (canonical32232 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2369 + difference 1 3) (sourceB2369 + difference 3 1) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5191) := by
    have ha : (tripleCharges (sourceA2369 + difference 1 3) (sourceB2369 + difference 3 1) sourceC2369) = raw32481 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32481; decide +kernel
    rw [ha]
    exact (canonical32481 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2369 + difference 1 4) (sourceB2369 + difference 4 1) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA2369 + difference 1 4) (sourceB2369 + difference 4 1) sourceC2369) = raw32321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32321; decide +kernel
    rw [ha]
    exact (canonical32321 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2369 + difference 1 5) (sourceB2369 + difference 5 1) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5057) := by
    have ha : (tripleCharges (sourceA2369 + difference 1 5) (sourceB2369 + difference 5 1) sourceC2369) = raw32482 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32482; decide +kernel
    rw [ha]
    exact (canonical32482 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2369 + difference 2 0) (sourceB2369 + difference 0 2) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA2369 + difference 2 0) (sourceB2369 + difference 0 2) sourceC2369) = raw32483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32483; decide +kernel
    rw [ha]
    exact (canonical32483 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2369 + difference 2 1) (sourceB2369 + difference 1 2) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA2369 + difference 2 1) (sourceB2369 + difference 1 2) sourceC2369) = raw32484 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32484; decide +kernel
    rw [ha]
    exact (canonical32484 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2369 + difference 2 3) (sourceB2369 + difference 3 2) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5154) := by
    have ha : (tripleCharges (sourceA2369 + difference 2 3) (sourceB2369 + difference 3 2) sourceC2369) = raw32485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32485; decide +kernel
    rw [ha]
    exact (canonical32485 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2369 + difference 2 4) (sourceB2369 + difference 4 2) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA2369 + difference 2 4) (sourceB2369 + difference 4 2) sourceC2369) = raw32326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32326; decide +kernel
    rw [ha]
    exact (canonical32326 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2369 + difference 2 5) (sourceB2369 + difference 5 2) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5060) := by
    have ha : (tripleCharges (sourceA2369 + difference 2 5) (sourceB2369 + difference 5 2) sourceC2369) = raw32486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32486; decide +kernel
    rw [ha]
    exact (canonical32486 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2369 + difference 3 0) (sourceB2369 + difference 0 3) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2369 + difference 3 0) (sourceB2369 + difference 0 3) sourceC2369) = raw32235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32235; decide +kernel
    rw [ha]
    exact (canonical32235 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2369 + difference 3 1) (sourceB2369 + difference 1 3) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2369 + difference 3 1) (sourceB2369 + difference 1 3) sourceC2369) = raw32236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32236; decide +kernel
    rw [ha]
    exact (canonical32236 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2369 + difference 3 2) (sourceB2369 + difference 2 3) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2369 + difference 3 2) (sourceB2369 + difference 2 3) sourceC2369) = raw32487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32487; decide +kernel
    rw [ha]
    exact (canonical32487 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2369 + difference 3 4) (sourceB2369 + difference 4 3) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2369 + difference 3 4) (sourceB2369 + difference 4 3) sourceC2369) = raw32238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32238; decide +kernel
    rw [ha]
    exact (canonical32238 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2369 + difference 3 5) (sourceB2369 + difference 5 3) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA2369 + difference 3 5) (sourceB2369 + difference 5 3) sourceC2369) = raw32239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32239; decide +kernel
    rw [ha]
    exact (canonical32239 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2369 + difference 4 0) (sourceB2369 + difference 0 4) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA2369 + difference 4 0) (sourceB2369 + difference 0 4) sourceC2369) = raw32488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32488; decide +kernel
    rw [ha]
    exact (canonical32488 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2369 + difference 4 1) (sourceB2369 + difference 1 4) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA2369 + difference 4 1) (sourceB2369 + difference 1 4) sourceC2369) = raw32489 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32489; decide +kernel
    rw [ha]
    exact (canonical32489 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2369 + difference 4 2) (sourceB2369 + difference 2 4) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2369 + difference 4 2) (sourceB2369 + difference 2 4) sourceC2369) = raw32248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32248; decide +kernel
    rw [ha]
    exact (canonical32248 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2369 + difference 4 3) (sourceB2369 + difference 3 4) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5146) := by
    have ha : (tripleCharges (sourceA2369 + difference 4 3) (sourceB2369 + difference 3 4) sourceC2369) = raw32490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32490; decide +kernel
    rw [ha]
    exact (canonical32490 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2369 + difference 4 5) (sourceB2369 + difference 5 4) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5091) := by
    have ha : (tripleCharges (sourceA2369 + difference 4 5) (sourceB2369 + difference 5 4) sourceC2369) = raw32491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32491; decide +kernel
    rw [ha]
    exact (canonical32491 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2369 + difference 5 0) (sourceB2369 + difference 0 5) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2369 + difference 5 0) (sourceB2369 + difference 0 5) sourceC2369) = raw32330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32330; decide +kernel
    rw [ha]
    exact (canonical32330 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2369 + difference 5 1) (sourceB2369 + difference 1 5) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2369 + difference 5 1) (sourceB2369 + difference 1 5) sourceC2369) = raw32331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32331; decide +kernel
    rw [ha]
    exact (canonical32331 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2369 + difference 5 2) (sourceB2369 + difference 2 5) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2369 + difference 5 2) (sourceB2369 + difference 2 5) sourceC2369) = raw32253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32253; decide +kernel
    rw [ha]
    exact (canonical32253 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2369 + difference 5 3) (sourceB2369 + difference 3 5) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA2369 + difference 5 3) (sourceB2369 + difference 3 5) sourceC2369) = raw32332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32332; decide +kernel
    rw [ha]
    exact (canonical32332 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2369 + difference 5 4) (sourceB2369 + difference 4 5) sourceC2369) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA2369 + difference 5 4) (sourceB2369 + difference 4 5) sourceC2369) = raw32492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2369 sourceB2369 sourceC2369 difference raw32492; decide +kernel
    rw [ha]
    exact (canonical32492 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2369 sourceB2369 sourceC2369
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2369, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2370 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2370 : Charge := ![1, 1, 1, 0, 0, -3]
def sourceC2370 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceForm2370 : Integer.Sparse Master := [(Sum.inr 1169, 1), (Sum.inr 2361, 1), (Sum.inr 2573, 3), (Sum.inr 2589, 1), (Sum.inr 4091, -1)]

theorem sourceEq2370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2370 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2370 + difference 2 0) (sourceB2370 + difference 0 2) sourceC2370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1169) := by
    have ha : (tripleCharges (sourceA2370 + difference 2 0) (sourceB2370 + difference 0 2) sourceC2370) = raw32493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2370 sourceB2370 sourceC2370 difference raw32493; decide +kernel
    rw [ha]
    exact (canonical32493 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2370 + difference 2 1) (sourceB2370 + difference 1 2) sourceC2370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2361) := by
    have ha : (tripleCharges (sourceA2370 + difference 2 1) (sourceB2370 + difference 1 2) sourceC2370) = raw32494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2370 sourceB2370 sourceC2370 difference raw32494; decide +kernel
    rw [ha]
    exact (canonical32494 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2370 + difference 2 2) (sourceB2370 + difference 2 2) sourceC2370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA2370 + difference 2 2) (sourceB2370 + difference 2 2) sourceC2370) = raw9355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2370 sourceB2370 sourceC2370 difference raw9355; decide +kernel
    rw [ha]
    exact (canonical9355 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2370 + difference 2 3) (sourceB2370 + difference 3 2) sourceC2370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA2370 + difference 2 3) (sourceB2370 + difference 3 2) sourceC2370) = raw9354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2370 sourceB2370 sourceC2370 difference raw9354; decide +kernel
    rw [ha]
    exact (canonical9354 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2370 + difference 2 4) (sourceB2370 + difference 4 2) sourceC2370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA2370 + difference 2 4) (sourceB2370 + difference 4 2) sourceC2370) = raw32495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2370 sourceB2370 sourceC2370 difference raw32495; decide +kernel
    rw [ha]
    exact (canonical32495 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2370 + difference 2 5) (sourceB2370 + difference 5 2) sourceC2370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2589) := by
    have ha : (tripleCharges (sourceA2370 + difference 2 5) (sourceB2370 + difference 5 2) sourceC2370) = raw32496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2370 sourceB2370 sourceC2370 difference raw32496; decide +kernel
    rw [ha]
    exact (canonical32496 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2370 + sourceB2370) sourceC2370) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2370 + sourceB2370) sourceC2370) = raw9348 := by
      apply Matrix.ext; unfold doubleCharges sourceA2370 sourceB2370 sourceC2370 raw9348; decide +kernel
    rw [ha]
    exact (canonical9348 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2370 sourceB2370 sourceC2370
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2370, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2371 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2371 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC2371 : Charge := ![1, 1, 1, 0, 0, -3]
def sourceForm2371 : Integer.Sparse Master := [(Sum.inr 1964, 1), (Sum.inr 2892, 2), (Sum.inr 2923, 2), (Sum.inr 3496, 1), (Sum.inr 4083, -1)]

theorem sourceEq2371 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2371 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2371 + difference 0 2) (sourceB2371 + difference 2 0) sourceC2371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3496) := by
    have ha : (tripleCharges (sourceA2371 + difference 0 2) (sourceB2371 + difference 2 0) sourceC2371) = raw32497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2371 sourceB2371 sourceC2371 difference raw32497; decide +kernel
    rw [ha]
    exact (canonical32497 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2371 + difference 1 2) (sourceB2371 + difference 2 1) sourceC2371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA2371 + difference 1 2) (sourceB2371 + difference 2 1) sourceC2371) = raw32498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2371 sourceB2371 sourceC2371 difference raw32498; decide +kernel
    rw [ha]
    exact (canonical32498 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2371 + difference 2 2) (sourceB2371 + difference 2 2) sourceC2371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA2371 + difference 2 2) (sourceB2371 + difference 2 2) sourceC2371) = raw32499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2371 sourceB2371 sourceC2371 difference raw32499; decide +kernel
    rw [ha]
    exact (canonical32499 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2371 + difference 3 2) (sourceB2371 + difference 2 3) sourceC2371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2892) := by
    have ha : (tripleCharges (sourceA2371 + difference 3 2) (sourceB2371 + difference 2 3) sourceC2371) = raw32500 := by
      apply Matrix.ext; unfold tripleCharges sourceA2371 sourceB2371 sourceC2371 difference raw32500; decide +kernel
    rw [ha]
    exact (canonical32500 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2371 + difference 4 2) (sourceB2371 + difference 2 4) sourceC2371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2892) := by
    have ha : (tripleCharges (sourceA2371 + difference 4 2) (sourceB2371 + difference 2 4) sourceC2371) = raw32501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2371 sourceB2371 sourceC2371 difference raw32501; decide +kernel
    rw [ha]
    exact (canonical32501 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2371 + difference 5 2) (sourceB2371 + difference 2 5) sourceC2371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1964) := by
    have ha : (tripleCharges (sourceA2371 + difference 5 2) (sourceB2371 + difference 2 5) sourceC2371) = raw32502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2371 sourceB2371 sourceC2371 difference raw32502; decide +kernel
    rw [ha]
    exact (canonical32502 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2371 + sourceB2371) sourceC2371) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2371 + sourceB2371) sourceC2371) = raw32503 := by
      apply Matrix.ext; unfold doubleCharges sourceA2371 sourceB2371 sourceC2371 raw32503; decide +kernel
    rw [ha]
    exact (canonical32503 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2371 sourceB2371 sourceC2371
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2371, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2372 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2372 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC2372 : Charge := ![1, 1, 2, -1, -1, -2]
def sourceForm2372 : Integer.Sparse Master := [(Sum.inr 2416, 1), (Sum.inr 2845, 2), (Sum.inr 2853, 1), (Sum.inr 2908, 1), (Sum.inr 3777, 1), (Sum.inr 4090, -1)]

theorem sourceEq2372 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2372 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2372 + difference 0 2) (sourceB2372 + difference 2 0) sourceC2372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3777) := by
    have ha : (tripleCharges (sourceA2372 + difference 0 2) (sourceB2372 + difference 2 0) sourceC2372) = raw32504 := by
      apply Matrix.ext; unfold tripleCharges sourceA2372 sourceB2372 sourceC2372 difference raw32504; decide +kernel
    rw [ha]
    exact (canonical32504 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2372 + difference 1 2) (sourceB2372 + difference 2 1) sourceC2372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2853) := by
    have ha : (tripleCharges (sourceA2372 + difference 1 2) (sourceB2372 + difference 2 1) sourceC2372) = raw23923 := by
      apply Matrix.ext; unfold tripleCharges sourceA2372 sourceB2372 sourceC2372 difference raw23923; decide +kernel
    rw [ha]
    exact (canonical23923 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2372 + difference 2 2) (sourceB2372 + difference 2 2) sourceC2372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2908) := by
    have ha : (tripleCharges (sourceA2372 + difference 2 2) (sourceB2372 + difference 2 2) sourceC2372) = raw23922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2372 sourceB2372 sourceC2372 difference raw23922; decide +kernel
    rw [ha]
    exact (canonical23922 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2372 + difference 3 2) (sourceB2372 + difference 2 3) sourceC2372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2845) := by
    have ha : (tripleCharges (sourceA2372 + difference 3 2) (sourceB2372 + difference 2 3) sourceC2372) = raw32505 := by
      apply Matrix.ext; unfold tripleCharges sourceA2372 sourceB2372 sourceC2372 difference raw32505; decide +kernel
    rw [ha]
    exact (canonical32505 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2372 + difference 4 2) (sourceB2372 + difference 2 4) sourceC2372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2845) := by
    have ha : (tripleCharges (sourceA2372 + difference 4 2) (sourceB2372 + difference 2 4) sourceC2372) = raw32506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2372 sourceB2372 sourceC2372 difference raw32506; decide +kernel
    rw [ha]
    exact (canonical32506 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2372 + difference 5 2) (sourceB2372 + difference 2 5) sourceC2372) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2416) := by
    have ha : (tripleCharges (sourceA2372 + difference 5 2) (sourceB2372 + difference 2 5) sourceC2372) = raw32507 := by
      apply Matrix.ext; unfold tripleCharges sourceA2372 sourceB2372 sourceC2372 difference raw32507; decide +kernel
    rw [ha]
    exact (canonical32507 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2372 + sourceB2372) sourceC2372) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2372 + sourceB2372) sourceC2372) = raw23927 := by
      apply Matrix.ext; unfold doubleCharges sourceA2372 sourceB2372 sourceC2372 raw23927; decide +kernel
    rw [ha]
    exact (canonical23927 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2372 sourceB2372 sourceC2372
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2372, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2373 : Charge := ![1, 1, 2, -1, -1, -2]
def sourceB2373 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC2373 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2373 : Integer.Sparse Master := [(Sum.inr 2417, 1), (Sum.inr 3363, 2), (Sum.inr 3370, 1), (Sum.inr 3435, 1), (Sum.inr 3600, 1), (Sum.inr 4080, -1)]

theorem sourceEq2373 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2373 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2373 + difference 0 0) (sourceB2373 + difference 0 0) sourceC2373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3600) := by
    have ha : (tripleCharges (sourceA2373 + difference 0 0) (sourceB2373 + difference 0 0) sourceC2373) = raw31920 := by
      apply Matrix.ext; unfold tripleCharges sourceA2373 sourceB2373 sourceC2373 difference raw31920; decide +kernel
    rw [ha]
    exact (canonical31920 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2373 + difference 0 1) (sourceB2373 + difference 1 0) sourceC2373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3370) := by
    have ha : (tripleCharges (sourceA2373 + difference 0 1) (sourceB2373 + difference 1 0) sourceC2373) = raw32006 := by
      apply Matrix.ext; unfold tripleCharges sourceA2373 sourceB2373 sourceC2373 difference raw32006; decide +kernel
    rw [ha]
    exact (canonical32006 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2373 + difference 0 2) (sourceB2373 + difference 2 0) sourceC2373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3435) := by
    have ha : (tripleCharges (sourceA2373 + difference 0 2) (sourceB2373 + difference 2 0) sourceC2373) = raw32508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2373 sourceB2373 sourceC2373 difference raw32508; decide +kernel
    rw [ha]
    exact (canonical32508 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2373 + difference 0 3) (sourceB2373 + difference 3 0) sourceC2373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3363) := by
    have ha : (tripleCharges (sourceA2373 + difference 0 3) (sourceB2373 + difference 3 0) sourceC2373) = raw32509 := by
      apply Matrix.ext; unfold tripleCharges sourceA2373 sourceB2373 sourceC2373 difference raw32509; decide +kernel
    rw [ha]
    exact (canonical32509 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2373 + difference 0 4) (sourceB2373 + difference 4 0) sourceC2373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3363) := by
    have ha : (tripleCharges (sourceA2373 + difference 0 4) (sourceB2373 + difference 4 0) sourceC2373) = raw32510 := by
      apply Matrix.ext; unfold tripleCharges sourceA2373 sourceB2373 sourceC2373 difference raw32510; decide +kernel
    rw [ha]
    exact (canonical32510 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2373 + difference 0 5) (sourceB2373 + difference 5 0) sourceC2373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2417) := by
    have ha : (tripleCharges (sourceA2373 + difference 0 5) (sourceB2373 + difference 5 0) sourceC2373) = raw32511 := by
      apply Matrix.ext; unfold tripleCharges sourceA2373 sourceB2373 sourceC2373 difference raw32511; decide +kernel
    rw [ha]
    exact (canonical32511 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2373 + sourceB2373) sourceC2373) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2373 + sourceB2373) sourceC2373) = raw31902 := by
      apply Matrix.ext; unfold doubleCharges sourceA2373 sourceB2373 sourceC2373 raw31902; decide +kernel
    rw [ha]
    exact (canonical31902 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2373 sourceB2373 sourceC2373
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2373, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2374 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2374 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2374 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceForm2374 : Integer.Sparse Master := [(Sum.inr 2800, 1), (Sum.inr 2801, 2), (Sum.inr 2814, 1), (Sum.inr 2864, 1), (Sum.inr 3692, 1), (Sum.inr 4091, -1)]

theorem sourceEq2374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2374 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2374 + difference 0 1) (sourceB2374 + difference 1 0) sourceC2374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA2374 + difference 0 1) (sourceB2374 + difference 1 0) sourceC2374) = raw32512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2374 sourceB2374 sourceC2374 difference raw32512; decide +kernel
    rw [ha]
    exact (canonical32512 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2374 + difference 1 1) (sourceB2374 + difference 1 1) sourceC2374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2864) := by
    have ha : (tripleCharges (sourceA2374 + difference 1 1) (sourceB2374 + difference 1 1) sourceC2374) = raw32513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2374 sourceB2374 sourceC2374 difference raw32513; decide +kernel
    rw [ha]
    exact (canonical32513 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2374 + difference 2 1) (sourceB2374 + difference 1 2) sourceC2374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2814) := by
    have ha : (tripleCharges (sourceA2374 + difference 2 1) (sourceB2374 + difference 1 2) sourceC2374) = raw32514 := by
      apply Matrix.ext; unfold tripleCharges sourceA2374 sourceB2374 sourceC2374 difference raw32514; decide +kernel
    rw [ha]
    exact (canonical32514 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2374 + difference 3 1) (sourceB2374 + difference 1 3) sourceC2374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2801) := by
    have ha : (tripleCharges (sourceA2374 + difference 3 1) (sourceB2374 + difference 1 3) sourceC2374) = raw32515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2374 sourceB2374 sourceC2374 difference raw32515; decide +kernel
    rw [ha]
    exact (canonical32515 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2374 + difference 4 1) (sourceB2374 + difference 1 4) sourceC2374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2801) := by
    have ha : (tripleCharges (sourceA2374 + difference 4 1) (sourceB2374 + difference 1 4) sourceC2374) = raw32516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2374 sourceB2374 sourceC2374 difference raw32516; decide +kernel
    rw [ha]
    exact (canonical32516 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2374 + difference 5 1) (sourceB2374 + difference 1 5) sourceC2374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2800) := by
    have ha : (tripleCharges (sourceA2374 + difference 5 1) (sourceB2374 + difference 1 5) sourceC2374) = raw32517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2374 sourceB2374 sourceC2374 difference raw32517; decide +kernel
    rw [ha]
    exact (canonical32517 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2374 + sourceB2374) sourceC2374) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2374 + sourceB2374) sourceC2374) = raw26393 := by
      apply Matrix.ext; unfold doubleCharges sourceA2374 sourceB2374 sourceC2374 raw26393; decide +kernel
    rw [ha]
    exact (canonical26393 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2374 sourceB2374 sourceC2374
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2374, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2375 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2375 : Charge := ![2, -1, 1, 0, -1, -1]
def sourceC2375 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceForm2375 : Integer.Sparse Master := [(Sum.inr 2797, 1), (Sum.inr 2799, 1), (Sum.inr 2801, 1), (Sum.inr 2809, 1), (Sum.inr 2862, 1), (Sum.inr 3690, 1), (Sum.inr 4091, -1)]

theorem sourceEq2375 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2375 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2375 + difference 0 1) (sourceB2375 + difference 1 0) sourceC2375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA2375 + difference 0 1) (sourceB2375 + difference 1 0) sourceC2375) = raw16835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2375 sourceB2375 sourceC2375 difference raw16835; decide +kernel
    rw [ha]
    exact (canonical16835 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2375 + difference 1 1) (sourceB2375 + difference 1 1) sourceC2375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA2375 + difference 1 1) (sourceB2375 + difference 1 1) sourceC2375) = raw16829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2375 sourceB2375 sourceC2375 difference raw16829; decide +kernel
    rw [ha]
    exact (canonical16829 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2375 + difference 2 1) (sourceB2375 + difference 1 2) sourceC2375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2809) := by
    have ha : (tripleCharges (sourceA2375 + difference 2 1) (sourceB2375 + difference 1 2) sourceC2375) = raw32518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2375 sourceB2375 sourceC2375 difference raw32518; decide +kernel
    rw [ha]
    exact (canonical32518 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2375 + difference 3 1) (sourceB2375 + difference 1 3) sourceC2375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2799) := by
    have ha : (tripleCharges (sourceA2375 + difference 3 1) (sourceB2375 + difference 1 3) sourceC2375) = raw32519 := by
      apply Matrix.ext; unfold tripleCharges sourceA2375 sourceB2375 sourceC2375 difference raw32519; decide +kernel
    rw [ha]
    exact (canonical32519 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2375 + difference 4 1) (sourceB2375 + difference 1 4) sourceC2375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2801) := by
    have ha : (tripleCharges (sourceA2375 + difference 4 1) (sourceB2375 + difference 1 4) sourceC2375) = raw32520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2375 sourceB2375 sourceC2375 difference raw32520; decide +kernel
    rw [ha]
    exact (canonical32520 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2375 + difference 5 1) (sourceB2375 + difference 1 5) sourceC2375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2797) := by
    have ha : (tripleCharges (sourceA2375 + difference 5 1) (sourceB2375 + difference 1 5) sourceC2375) = raw32521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2375 sourceB2375 sourceC2375 difference raw32521; decide +kernel
    rw [ha]
    exact (canonical32521 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2375 + sourceB2375) sourceC2375) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2375 + sourceB2375) sourceC2375) = raw16832 := by
      apply Matrix.ext; unfold doubleCharges sourceA2375 sourceB2375 sourceC2375 raw16832; decide +kernel
    rw [ha]
    exact (canonical16832 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2375 sourceB2375 sourceC2375
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2375, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2376 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2376 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC2376 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceForm2376 : Integer.Sparse Master := [(Sum.inr 2524, 1), (Sum.inr 2798, 2), (Sum.inr 2807, 1), (Sum.inr 2861, 1), (Sum.inr 3689, 1), (Sum.inr 4092, -1)]

theorem sourceEq2376 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2376 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2376 + difference 0 1) (sourceB2376 + difference 1 0) sourceC2376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3689) := by
    have ha : (tripleCharges (sourceA2376 + difference 0 1) (sourceB2376 + difference 1 0) sourceC2376) = raw32522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2376 sourceB2376 sourceC2376 difference raw32522; decide +kernel
    rw [ha]
    exact (canonical32522 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2376 + difference 1 1) (sourceB2376 + difference 1 1) sourceC2376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2861) := by
    have ha : (tripleCharges (sourceA2376 + difference 1 1) (sourceB2376 + difference 1 1) sourceC2376) = raw32523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2376 sourceB2376 sourceC2376 difference raw32523; decide +kernel
    rw [ha]
    exact (canonical32523 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2376 + difference 2 1) (sourceB2376 + difference 1 2) sourceC2376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2807) := by
    have ha : (tripleCharges (sourceA2376 + difference 2 1) (sourceB2376 + difference 1 2) sourceC2376) = raw32524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2376 sourceB2376 sourceC2376 difference raw32524; decide +kernel
    rw [ha]
    exact (canonical32524 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2376 + difference 3 1) (sourceB2376 + difference 1 3) sourceC2376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2798) := by
    have ha : (tripleCharges (sourceA2376 + difference 3 1) (sourceB2376 + difference 1 3) sourceC2376) = raw32525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2376 sourceB2376 sourceC2376 difference raw32525; decide +kernel
    rw [ha]
    exact (canonical32525 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2376 + difference 4 1) (sourceB2376 + difference 1 4) sourceC2376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2798) := by
    have ha : (tripleCharges (sourceA2376 + difference 4 1) (sourceB2376 + difference 1 4) sourceC2376) = raw32526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2376 sourceB2376 sourceC2376 difference raw32526; decide +kernel
    rw [ha]
    exact (canonical32526 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2376 + difference 5 1) (sourceB2376 + difference 1 5) sourceC2376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2524) := by
    have ha : (tripleCharges (sourceA2376 + difference 5 1) (sourceB2376 + difference 1 5) sourceC2376) = raw32527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2376 sourceB2376 sourceC2376 difference raw32527; decide +kernel
    rw [ha]
    exact (canonical32527 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2376 + sourceB2376) sourceC2376) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2376 + sourceB2376) sourceC2376) = raw32528 := by
      apply Matrix.ext; unfold doubleCharges sourceA2376 sourceB2376 sourceC2376 raw32528; decide +kernel
    rw [ha]
    exact (canonical32528 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2376 sourceB2376 sourceC2376
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2376, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2377 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceB2377 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC2377 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2377 : Integer.Sparse Master := [(Sum.inr 2031, 2), (Sum.inr 2036, 1), (Sum.inr 2046, 1), (Sum.inr 2275, 1), (Sum.inr 3537, 1), (Sum.inr 4080, -1)]

theorem sourceEq2377 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2377 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2377 + difference 0 0) (sourceB2377 + difference 0 0) sourceC2377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA2377 + difference 0 0) (sourceB2377 + difference 0 0) sourceC2377) = raw32529 := by
      apply Matrix.ext; unfold tripleCharges sourceA2377 sourceB2377 sourceC2377 difference raw32529; decide +kernel
    rw [ha]
    exact (canonical32529 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2377 + difference 1 0) (sourceB2377 + difference 0 1) sourceC2377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2036) := by
    have ha : (tripleCharges (sourceA2377 + difference 1 0) (sourceB2377 + difference 0 1) sourceC2377) = raw32530 := by
      apply Matrix.ext; unfold tripleCharges sourceA2377 sourceB2377 sourceC2377 difference raw32530; decide +kernel
    rw [ha]
    exact (canonical32530 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2377 + difference 2 0) (sourceB2377 + difference 0 2) sourceC2377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA2377 + difference 2 0) (sourceB2377 + difference 0 2) sourceC2377) = raw32531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2377 sourceB2377 sourceC2377 difference raw32531; decide +kernel
    rw [ha]
    exact (canonical32531 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2377 + difference 3 0) (sourceB2377 + difference 0 3) sourceC2377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2031) := by
    have ha : (tripleCharges (sourceA2377 + difference 3 0) (sourceB2377 + difference 0 3) sourceC2377) = raw32532 := by
      apply Matrix.ext; unfold tripleCharges sourceA2377 sourceB2377 sourceC2377 difference raw32532; decide +kernel
    rw [ha]
    exact (canonical32532 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2377 + difference 4 0) (sourceB2377 + difference 0 4) sourceC2377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2031) := by
    have ha : (tripleCharges (sourceA2377 + difference 4 0) (sourceB2377 + difference 0 4) sourceC2377) = raw32533 := by
      apply Matrix.ext; unfold tripleCharges sourceA2377 sourceB2377 sourceC2377 difference raw32533; decide +kernel
    rw [ha]
    exact (canonical32533 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2377 + difference 5 0) (sourceB2377 + difference 0 5) sourceC2377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2046) := by
    have ha : (tripleCharges (sourceA2377 + difference 5 0) (sourceB2377 + difference 0 5) sourceC2377) = raw32534 := by
      apply Matrix.ext; unfold tripleCharges sourceA2377 sourceB2377 sourceC2377 difference raw32534; decide +kernel
    rw [ha]
    exact (canonical32534 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2377 + sourceB2377) sourceC2377) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2377 + sourceB2377) sourceC2377) = raw31902 := by
      apply Matrix.ext; unfold doubleCharges sourceA2377 sourceB2377 sourceC2377 raw31902; decide +kernel
    rw [ha]
    exact (canonical31902 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2377 sourceB2377 sourceC2377
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2377, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2378 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2378 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC2378 : Charge := ![1, 2, 0, -2, -1, 0]
def sourceForm2378 : Integer.Sparse Master := [(Sum.inr 2810, 1), (Sum.inr 2816, 1), (Sum.inr 2817, 1), (Sum.inr 2819, 1), (Sum.inr 2885, 1), (Sum.inr 3706, 1), (Sum.inr 4092, -1)]

theorem sourceEq2378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2378 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2378 + difference 0 1) (sourceB2378 + difference 1 0) sourceC2378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA2378 + difference 0 1) (sourceB2378 + difference 1 0) sourceC2378) = raw32535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2378 sourceB2378 sourceC2378 difference raw32535; decide +kernel
    rw [ha]
    exact (canonical32535 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2378 + difference 1 1) (sourceB2378 + difference 1 1) sourceC2378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2885) := by
    have ha : (tripleCharges (sourceA2378 + difference 1 1) (sourceB2378 + difference 1 1) sourceC2378) = raw32536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2378 sourceB2378 sourceC2378 difference raw32536; decide +kernel
    rw [ha]
    exact (canonical32536 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2378 + difference 2 1) (sourceB2378 + difference 1 2) sourceC2378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2810) := by
    have ha : (tripleCharges (sourceA2378 + difference 2 1) (sourceB2378 + difference 1 2) sourceC2378) = raw32537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2378 sourceB2378 sourceC2378 difference raw32537; decide +kernel
    rw [ha]
    exact (canonical32537 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2378 + difference 3 1) (sourceB2378 + difference 1 3) sourceC2378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2817) := by
    have ha : (tripleCharges (sourceA2378 + difference 3 1) (sourceB2378 + difference 1 3) sourceC2378) = raw32538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2378 sourceB2378 sourceC2378 difference raw32538; decide +kernel
    rw [ha]
    exact (canonical32538 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2378 + difference 4 1) (sourceB2378 + difference 1 4) sourceC2378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2819) := by
    have ha : (tripleCharges (sourceA2378 + difference 4 1) (sourceB2378 + difference 1 4) sourceC2378) = raw32539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2378 sourceB2378 sourceC2378 difference raw32539; decide +kernel
    rw [ha]
    exact (canonical32539 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2378 + difference 5 1) (sourceB2378 + difference 1 5) sourceC2378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2816) := by
    have ha : (tripleCharges (sourceA2378 + difference 5 1) (sourceB2378 + difference 1 5) sourceC2378) = raw32540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2378 sourceB2378 sourceC2378 difference raw32540; decide +kernel
    rw [ha]
    exact (canonical32540 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2378 + sourceB2378) sourceC2378) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2378 + sourceB2378) sourceC2378) = raw32541 := by
      apply Matrix.ext; unfold doubleCharges sourceA2378 sourceB2378 sourceC2378 raw32541; decide +kernel
    rw [ha]
    exact (canonical32541 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2378 sourceB2378 sourceC2378
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2378, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2379 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2379 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC2379 : Charge := ![1, 2, 0, -2, 0, -1]
def sourceForm2379 : Integer.Sparse Master := [(Sum.inr 2808, 1), (Sum.inr 2811, 1), (Sum.inr 2813, 1), (Sum.inr 2819, 1), (Sum.inr 2882, 1), (Sum.inr 3705, 1), (Sum.inr 4092, -1)]

theorem sourceEq2379 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2379 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2379 + difference 0 1) (sourceB2379 + difference 1 0) sourceC2379) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3705) := by
    have ha : (tripleCharges (sourceA2379 + difference 0 1) (sourceB2379 + difference 1 0) sourceC2379) = raw32542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2379 sourceB2379 sourceC2379 difference raw32542; decide +kernel
    rw [ha]
    exact (canonical32542 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2379 + difference 1 1) (sourceB2379 + difference 1 1) sourceC2379) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA2379 + difference 1 1) (sourceB2379 + difference 1 1) sourceC2379) = raw32543 := by
      apply Matrix.ext; unfold tripleCharges sourceA2379 sourceB2379 sourceC2379 difference raw32543; decide +kernel
    rw [ha]
    exact (canonical32543 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2379 + difference 2 1) (sourceB2379 + difference 1 2) sourceC2379) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2808) := by
    have ha : (tripleCharges (sourceA2379 + difference 2 1) (sourceB2379 + difference 1 2) sourceC2379) = raw32544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2379 sourceB2379 sourceC2379 difference raw32544; decide +kernel
    rw [ha]
    exact (canonical32544 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2379 + difference 3 1) (sourceB2379 + difference 1 3) sourceC2379) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2813) := by
    have ha : (tripleCharges (sourceA2379 + difference 3 1) (sourceB2379 + difference 1 3) sourceC2379) = raw32545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2379 sourceB2379 sourceC2379 difference raw32545; decide +kernel
    rw [ha]
    exact (canonical32545 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2379 + difference 4 1) (sourceB2379 + difference 1 4) sourceC2379) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2819) := by
    have ha : (tripleCharges (sourceA2379 + difference 4 1) (sourceB2379 + difference 1 4) sourceC2379) = raw32546 := by
      apply Matrix.ext; unfold tripleCharges sourceA2379 sourceB2379 sourceC2379 difference raw32546; decide +kernel
    rw [ha]
    exact (canonical32546 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2379 + difference 5 1) (sourceB2379 + difference 1 5) sourceC2379) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2811) := by
    have ha : (tripleCharges (sourceA2379 + difference 5 1) (sourceB2379 + difference 1 5) sourceC2379) = raw32547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2379 sourceB2379 sourceC2379 difference raw32547; decide +kernel
    rw [ha]
    exact (canonical32547 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2379 + sourceB2379) sourceC2379) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2379 + sourceB2379) sourceC2379) = raw32548 := by
      apply Matrix.ext; unfold doubleCharges sourceA2379 sourceB2379 sourceC2379 raw32548; decide +kernel
    rw [ha]
    exact (canonical32548 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2379 sourceB2379 sourceC2379
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2379, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2380 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2380 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceC2380 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceForm2380 : Integer.Sparse Master := [(Sum.inr 4516, 1), (Sum.inr 4517, 1), (Sum.inr 4518, 2), (Sum.inr 4606, 1), (Sum.inr 4980, 1), (Sum.inr 4982, 1), (Sum.inr 4983, 2), (Sum.inr 5027, 1), (Sum.inr 5109, 2), (Sum.inr 5119, 2), (Sum.inr 5148, 1), (Sum.inr 5202, 1), (Sum.inr 5203, 2), (Sum.inr 5204, 2), (Sum.inr 5207, 2), (Sum.inr 5237, 1), (Sum.inr 5292, 1), (Sum.inr 5293, 2), (Sum.inr 5422, 1), (Sum.inr 5450, 1), (Sum.inr 5451, 2)]

theorem sourceEq2380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2380 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2380 + difference 0 1) (sourceB2380 + difference 1 0) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2380 + difference 0 1) (sourceB2380 + difference 1 0) sourceC2380) = raw16235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw16235; decide +kernel
    rw [ha]
    exact (canonical16235 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2380 + difference 0 2) (sourceB2380 + difference 2 0) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA2380 + difference 0 2) (sourceB2380 + difference 2 0) sourceC2380) = raw16236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw16236; decide +kernel
    rw [ha]
    exact (canonical16236 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2380 + difference 0 3) (sourceB2380 + difference 3 0) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2380 + difference 0 3) (sourceB2380 + difference 3 0) sourceC2380) = raw28233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw28233; decide +kernel
    rw [ha]
    exact (canonical28233 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2380 + difference 0 4) (sourceB2380 + difference 4 0) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2380 + difference 0 4) (sourceB2380 + difference 4 0) sourceC2380) = raw16237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw16237; decide +kernel
    rw [ha]
    exact (canonical16237 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2380 + difference 0 5) (sourceB2380 + difference 5 0) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2380 + difference 0 5) (sourceB2380 + difference 5 0) sourceC2380) = raw16238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw16238; decide +kernel
    rw [ha]
    exact (canonical16238 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2380 + difference 1 0) (sourceB2380 + difference 0 1) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA2380 + difference 1 0) (sourceB2380 + difference 0 1) sourceC2380) = raw26819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw26819; decide +kernel
    rw [ha]
    exact (canonical26819 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2380 + difference 1 2) (sourceB2380 + difference 2 1) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA2380 + difference 1 2) (sourceB2380 + difference 2 1) sourceC2380) = raw32549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw32549; decide +kernel
    rw [ha]
    exact (canonical32549 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2380 + difference 1 3) (sourceB2380 + difference 3 1) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2380 + difference 1 3) (sourceB2380 + difference 3 1) sourceC2380) = raw16224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw16224; decide +kernel
    rw [ha]
    exact (canonical16224 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2380 + difference 1 4) (sourceB2380 + difference 4 1) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2380 + difference 1 4) (sourceB2380 + difference 4 1) sourceC2380) = raw32550 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw32550; decide +kernel
    rw [ha]
    exact (canonical32550 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2380 + difference 1 5) (sourceB2380 + difference 5 1) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA2380 + difference 1 5) (sourceB2380 + difference 5 1) sourceC2380) = raw26793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw26793; decide +kernel
    rw [ha]
    exact (canonical26793 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2380 + difference 2 0) (sourceB2380 + difference 0 2) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4516) := by
    have ha : (tripleCharges (sourceA2380 + difference 2 0) (sourceB2380 + difference 0 2) sourceC2380) = raw26818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw26818; decide +kernel
    rw [ha]
    exact (canonical26818 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2380 + difference 2 1) (sourceB2380 + difference 1 2) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4980) := by
    have ha : (tripleCharges (sourceA2380 + difference 2 1) (sourceB2380 + difference 1 2) sourceC2380) = raw32551 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw32551; decide +kernel
    rw [ha]
    exact (canonical32551 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2380 + difference 2 3) (sourceB2380 + difference 3 2) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2380 + difference 2 3) (sourceB2380 + difference 3 2) sourceC2380) = raw16229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw16229; decide +kernel
    rw [ha]
    exact (canonical16229 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2380 + difference 2 4) (sourceB2380 + difference 4 2) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2380 + difference 2 4) (sourceB2380 + difference 4 2) sourceC2380) = raw32552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw32552; decide +kernel
    rw [ha]
    exact (canonical32552 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2380 + difference 2 5) (sourceB2380 + difference 5 2) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA2380 + difference 2 5) (sourceB2380 + difference 5 2) sourceC2380) = raw26792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw26792; decide +kernel
    rw [ha]
    exact (canonical26792 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2380 + difference 3 0) (sourceB2380 + difference 0 3) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4518) := by
    have ha : (tripleCharges (sourceA2380 + difference 3 0) (sourceB2380 + difference 0 3) sourceC2380) = raw32553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw32553; decide +kernel
    rw [ha]
    exact (canonical32553 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2380 + difference 3 1) (sourceB2380 + difference 1 3) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4983) := by
    have ha : (tripleCharges (sourceA2380 + difference 3 1) (sourceB2380 + difference 1 3) sourceC2380) = raw32554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw32554; decide +kernel
    rw [ha]
    exact (canonical32554 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2380 + difference 3 2) (sourceB2380 + difference 2 3) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5119) := by
    have ha : (tripleCharges (sourceA2380 + difference 3 2) (sourceB2380 + difference 2 3) sourceC2380) = raw32555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw32555; decide +kernel
    rw [ha]
    exact (canonical32555 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2380 + difference 3 4) (sourceB2380 + difference 4 3) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2380 + difference 3 4) (sourceB2380 + difference 4 3) sourceC2380) = raw32556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw32556; decide +kernel
    rw [ha]
    exact (canonical32556 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2380 + difference 3 5) (sourceB2380 + difference 5 3) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2380 + difference 3 5) (sourceB2380 + difference 5 3) sourceC2380) = raw32557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw32557; decide +kernel
    rw [ha]
    exact (canonical32557 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2380 + difference 4 0) (sourceB2380 + difference 0 4) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4518) := by
    have ha : (tripleCharges (sourceA2380 + difference 4 0) (sourceB2380 + difference 0 4) sourceC2380) = raw29953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw29953; decide +kernel
    rw [ha]
    exact (canonical29953 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2380 + difference 4 1) (sourceB2380 + difference 1 4) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4983) := by
    have ha : (tripleCharges (sourceA2380 + difference 4 1) (sourceB2380 + difference 1 4) sourceC2380) = raw29954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw29954; decide +kernel
    rw [ha]
    exact (canonical29954 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2380 + difference 4 2) (sourceB2380 + difference 2 4) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5119) := by
    have ha : (tripleCharges (sourceA2380 + difference 4 2) (sourceB2380 + difference 2 4) sourceC2380) = raw29955 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw29955; decide +kernel
    rw [ha]
    exact (canonical29955 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2380 + difference 4 3) (sourceB2380 + difference 3 4) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2380 + difference 4 3) (sourceB2380 + difference 3 4) sourceC2380) = raw16239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw16239; decide +kernel
    rw [ha]
    exact (canonical16239 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2380 + difference 4 5) (sourceB2380 + difference 5 4) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2380 + difference 4 5) (sourceB2380 + difference 5 4) sourceC2380) = raw29956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw29956; decide +kernel
    rw [ha]
    exact (canonical29956 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2380 + difference 5 0) (sourceB2380 + difference 0 5) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4517) := by
    have ha : (tripleCharges (sourceA2380 + difference 5 0) (sourceB2380 + difference 0 5) sourceC2380) = raw28242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw28242; decide +kernel
    rw [ha]
    exact (canonical28242 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2380 + difference 5 1) (sourceB2380 + difference 1 5) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4982) := by
    have ha : (tripleCharges (sourceA2380 + difference 5 1) (sourceB2380 + difference 1 5) sourceC2380) = raw28243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw28243; decide +kernel
    rw [ha]
    exact (canonical28243 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2380 + difference 5 2) (sourceB2380 + difference 2 5) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5027) := by
    have ha : (tripleCharges (sourceA2380 + difference 5 2) (sourceB2380 + difference 2 5) sourceC2380) = raw28244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw28244; decide +kernel
    rw [ha]
    exact (canonical28244 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2380 + difference 5 3) (sourceB2380 + difference 3 5) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA2380 + difference 5 3) (sourceB2380 + difference 3 5) sourceC2380) = raw16244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw16244; decide +kernel
    rw [ha]
    exact (canonical16244 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2380 + difference 5 4) (sourceB2380 + difference 4 5) sourceC2380) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA2380 + difference 5 4) (sourceB2380 + difference 4 5) sourceC2380) = raw28245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2380 sourceB2380 sourceC2380 difference raw28245; decide +kernel
    rw [ha]
    exact (canonical28245 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2380 sourceB2380 sourceC2380
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2380, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2381 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2381 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceC2381 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceForm2381 : Integer.Sparse Master := [(Sum.inr 1100, 1), (Sum.inr 1101, 1), (Sum.inr 1102, 2), (Sum.inr 1240, 1), (Sum.inr 2416, 1), (Sum.inr 2421, 1), (Sum.inr 2519, 2), (Sum.inr 2793, 1), (Sum.inr 2794, 2), (Sum.inr 2845, 2), (Sum.inr 2880, 1), (Sum.inr 2881, 2), (Sum.inr 2884, 2), (Sum.inr 2889, 2), (Sum.inr 2927, 1), (Sum.inr 3100, 1), (Sum.inr 3102, 2), (Sum.inr 3394, 1), (Sum.inr 3964, 1), (Sum.inr 3987, 2), (Sum.inr 4029, 1)]

theorem sourceEq2381 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2381 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2381 + difference 0 1) (sourceB2381 + difference 1 0) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3394) := by
    have ha : (tripleCharges (sourceA2381 + difference 0 1) (sourceB2381 + difference 1 0) sourceC2381) = raw16265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw16265; decide +kernel
    rw [ha]
    exact (canonical16265 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2381 + difference 0 2) (sourceB2381 + difference 2 0) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3964) := by
    have ha : (tripleCharges (sourceA2381 + difference 0 2) (sourceB2381 + difference 2 0) sourceC2381) = raw16266 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw16266; decide +kernel
    rw [ha]
    exact (canonical16266 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2381 + difference 0 3) (sourceB2381 + difference 3 0) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA2381 + difference 0 3) (sourceB2381 + difference 3 0) sourceC2381) = raw28255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw28255; decide +kernel
    rw [ha]
    exact (canonical28255 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2381 + difference 0 4) (sourceB2381 + difference 4 0) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA2381 + difference 0 4) (sourceB2381 + difference 4 0) sourceC2381) = raw16267 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw16267; decide +kernel
    rw [ha]
    exact (canonical16267 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2381 + difference 0 5) (sourceB2381 + difference 5 0) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA2381 + difference 0 5) (sourceB2381 + difference 5 0) sourceC2381) = raw16268 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw16268; decide +kernel
    rw [ha]
    exact (canonical16268 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2381 + difference 1 0) (sourceB2381 + difference 0 1) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA2381 + difference 1 0) (sourceB2381 + difference 0 1) sourceC2381) = raw26849 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw26849; decide +kernel
    rw [ha]
    exact (canonical26849 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2381 + difference 1 2) (sourceB2381 + difference 2 1) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2927) := by
    have ha : (tripleCharges (sourceA2381 + difference 1 2) (sourceB2381 + difference 2 1) sourceC2381) = raw32558 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw32558; decide +kernel
    rw [ha]
    exact (canonical32558 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2381 + difference 1 3) (sourceB2381 + difference 3 1) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA2381 + difference 1 3) (sourceB2381 + difference 3 1) sourceC2381) = raw16254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw16254; decide +kernel
    rw [ha]
    exact (canonical16254 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2381 + difference 1 4) (sourceB2381 + difference 4 1) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA2381 + difference 1 4) (sourceB2381 + difference 4 1) sourceC2381) = raw32559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw32559; decide +kernel
    rw [ha]
    exact (canonical32559 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2381 + difference 1 5) (sourceB2381 + difference 5 1) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA2381 + difference 1 5) (sourceB2381 + difference 5 1) sourceC2381) = raw26823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw26823; decide +kernel
    rw [ha]
    exact (canonical26823 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2381 + difference 2 0) (sourceB2381 + difference 0 2) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1100) := by
    have ha : (tripleCharges (sourceA2381 + difference 2 0) (sourceB2381 + difference 0 2) sourceC2381) = raw26848 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw26848; decide +kernel
    rw [ha]
    exact (canonical26848 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2381 + difference 2 1) (sourceB2381 + difference 1 2) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2793) := by
    have ha : (tripleCharges (sourceA2381 + difference 2 1) (sourceB2381 + difference 1 2) sourceC2381) = raw32560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw32560; decide +kernel
    rw [ha]
    exact (canonical32560 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2381 + difference 2 3) (sourceB2381 + difference 3 2) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA2381 + difference 2 3) (sourceB2381 + difference 3 2) sourceC2381) = raw16259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw16259; decide +kernel
    rw [ha]
    exact (canonical16259 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2381 + difference 2 4) (sourceB2381 + difference 4 2) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA2381 + difference 2 4) (sourceB2381 + difference 4 2) sourceC2381) = raw32561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw32561; decide +kernel
    rw [ha]
    exact (canonical32561 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2381 + difference 2 5) (sourceB2381 + difference 5 2) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2880) := by
    have ha : (tripleCharges (sourceA2381 + difference 2 5) (sourceB2381 + difference 5 2) sourceC2381) = raw26822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw26822; decide +kernel
    rw [ha]
    exact (canonical26822 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2381 + difference 3 0) (sourceB2381 + difference 0 3) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1102) := by
    have ha : (tripleCharges (sourceA2381 + difference 3 0) (sourceB2381 + difference 0 3) sourceC2381) = raw32562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw32562; decide +kernel
    rw [ha]
    exact (canonical32562 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2381 + difference 3 1) (sourceB2381 + difference 1 3) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2794) := by
    have ha : (tripleCharges (sourceA2381 + difference 3 1) (sourceB2381 + difference 1 3) sourceC2381) = raw32563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw32563; decide +kernel
    rw [ha]
    exact (canonical32563 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2381 + difference 3 2) (sourceB2381 + difference 2 3) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2845) := by
    have ha : (tripleCharges (sourceA2381 + difference 3 2) (sourceB2381 + difference 2 3) sourceC2381) = raw32564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw32564; decide +kernel
    rw [ha]
    exact (canonical32564 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2381 + difference 3 4) (sourceB2381 + difference 4 3) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA2381 + difference 3 4) (sourceB2381 + difference 4 3) sourceC2381) = raw32565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw32565; decide +kernel
    rw [ha]
    exact (canonical32565 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2381 + difference 3 5) (sourceB2381 + difference 5 3) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA2381 + difference 3 5) (sourceB2381 + difference 5 3) sourceC2381) = raw32566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw32566; decide +kernel
    rw [ha]
    exact (canonical32566 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2381 + difference 4 0) (sourceB2381 + difference 0 4) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1102) := by
    have ha : (tripleCharges (sourceA2381 + difference 4 0) (sourceB2381 + difference 0 4) sourceC2381) = raw29970 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw29970; decide +kernel
    rw [ha]
    exact (canonical29970 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2381 + difference 4 1) (sourceB2381 + difference 1 4) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2794) := by
    have ha : (tripleCharges (sourceA2381 + difference 4 1) (sourceB2381 + difference 1 4) sourceC2381) = raw29971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw29971; decide +kernel
    rw [ha]
    exact (canonical29971 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2381 + difference 4 2) (sourceB2381 + difference 2 4) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2845) := by
    have ha : (tripleCharges (sourceA2381 + difference 4 2) (sourceB2381 + difference 2 4) sourceC2381) = raw29972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw29972; decide +kernel
    rw [ha]
    exact (canonical29972 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2381 + difference 4 3) (sourceB2381 + difference 3 4) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA2381 + difference 4 3) (sourceB2381 + difference 3 4) sourceC2381) = raw16269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw16269; decide +kernel
    rw [ha]
    exact (canonical16269 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2381 + difference 4 5) (sourceB2381 + difference 5 4) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA2381 + difference 4 5) (sourceB2381 + difference 5 4) sourceC2381) = raw29973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw29973; decide +kernel
    rw [ha]
    exact (canonical29973 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2381 + difference 5 0) (sourceB2381 + difference 0 5) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1101) := by
    have ha : (tripleCharges (sourceA2381 + difference 5 0) (sourceB2381 + difference 0 5) sourceC2381) = raw28264 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw28264; decide +kernel
    rw [ha]
    exact (canonical28264 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2381 + difference 5 1) (sourceB2381 + difference 1 5) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2421) := by
    have ha : (tripleCharges (sourceA2381 + difference 5 1) (sourceB2381 + difference 1 5) sourceC2381) = raw28265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw28265; decide +kernel
    rw [ha]
    exact (canonical28265 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2381 + difference 5 2) (sourceB2381 + difference 2 5) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2416) := by
    have ha : (tripleCharges (sourceA2381 + difference 5 2) (sourceB2381 + difference 2 5) sourceC2381) = raw28266 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw28266; decide +kernel
    rw [ha]
    exact (canonical28266 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2381 + difference 5 3) (sourceB2381 + difference 3 5) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA2381 + difference 5 3) (sourceB2381 + difference 3 5) sourceC2381) = raw16274 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw16274; decide +kernel
    rw [ha]
    exact (canonical16274 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2381 + difference 5 4) (sourceB2381 + difference 4 5) sourceC2381) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA2381 + difference 5 4) (sourceB2381 + difference 4 5) sourceC2381) = raw28267 := by
      apply Matrix.ext; unfold tripleCharges sourceA2381 sourceB2381 sourceC2381 difference raw28267; decide +kernel
    rw [ha]
    exact (canonical28267 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2381 sourceB2381 sourceC2381
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2381, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2382 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2382 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2382 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceForm2382 : Integer.Sparse Master := [(Sum.inr 4364, 1), (Sum.inr 4365, 1), (Sum.inr 4369, 2), (Sum.inr 4474, 1), (Sum.inr 4968, 1), (Sum.inr 4970, 1), (Sum.inr 4974, 2), (Sum.inr 5041, 1), (Sum.inr 5043, 2), (Sum.inr 5085, 1), (Sum.inr 5147, 2), (Sum.inr 5185, 2), (Sum.inr 5189, 2), (Sum.inr 5202, 1), (Sum.inr 5203, 2), (Sum.inr 5266, 2), (Sum.inr 5301, 1), (Sum.inr 5369, 1), (Sum.inr 5469, 1), (Sum.inr 5473, 2), (Sum.inr 5474, 1)]

theorem sourceEq2382 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2382 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2382 + difference 0 1) (sourceB2382 + difference 1 0) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2382 + difference 0 1) (sourceB2382 + difference 1 0) sourceC2382) = raw32567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32567; decide +kernel
    rw [ha]
    exact (canonical32567 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2382 + difference 0 2) (sourceB2382 + difference 2 0) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA2382 + difference 0 2) (sourceB2382 + difference 2 0) sourceC2382) = raw32568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32568; decide +kernel
    rw [ha]
    exact (canonical32568 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2382 + difference 0 3) (sourceB2382 + difference 3 0) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2382 + difference 0 3) (sourceB2382 + difference 3 0) sourceC2382) = raw32569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32569; decide +kernel
    rw [ha]
    exact (canonical32569 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2382 + difference 0 4) (sourceB2382 + difference 4 0) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2382 + difference 0 4) (sourceB2382 + difference 4 0) sourceC2382) = raw32570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32570; decide +kernel
    rw [ha]
    exact (canonical32570 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2382 + difference 0 5) (sourceB2382 + difference 5 0) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5474) := by
    have ha : (tripleCharges (sourceA2382 + difference 0 5) (sourceB2382 + difference 5 0) sourceC2382) = raw32571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32571; decide +kernel
    rw [ha]
    exact (canonical32571 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2382 + difference 1 0) (sourceB2382 + difference 0 1) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA2382 + difference 1 0) (sourceB2382 + difference 0 1) sourceC2382) = raw32572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32572; decide +kernel
    rw [ha]
    exact (canonical32572 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2382 + difference 1 2) (sourceB2382 + difference 2 1) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA2382 + difference 1 2) (sourceB2382 + difference 2 1) sourceC2382) = raw32573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32573; decide +kernel
    rw [ha]
    exact (canonical32573 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2382 + difference 1 3) (sourceB2382 + difference 3 1) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA2382 + difference 1 3) (sourceB2382 + difference 3 1) sourceC2382) = raw32574 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32574; decide +kernel
    rw [ha]
    exact (canonical32574 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2382 + difference 1 4) (sourceB2382 + difference 4 1) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA2382 + difference 1 4) (sourceB2382 + difference 4 1) sourceC2382) = raw32575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32575; decide +kernel
    rw [ha]
    exact (canonical32575 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2382 + difference 1 5) (sourceB2382 + difference 5 1) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA2382 + difference 1 5) (sourceB2382 + difference 5 1) sourceC2382) = raw32576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32576; decide +kernel
    rw [ha]
    exact (canonical32576 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2382 + difference 2 0) (sourceB2382 + difference 0 2) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4364) := by
    have ha : (tripleCharges (sourceA2382 + difference 2 0) (sourceB2382 + difference 0 2) sourceC2382) = raw32577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32577; decide +kernel
    rw [ha]
    exact (canonical32577 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2382 + difference 2 1) (sourceB2382 + difference 1 2) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4968) := by
    have ha : (tripleCharges (sourceA2382 + difference 2 1) (sourceB2382 + difference 1 2) sourceC2382) = raw32578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32578; decide +kernel
    rw [ha]
    exact (canonical32578 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2382 + difference 2 3) (sourceB2382 + difference 3 2) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA2382 + difference 2 3) (sourceB2382 + difference 3 2) sourceC2382) = raw32579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32579; decide +kernel
    rw [ha]
    exact (canonical32579 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2382 + difference 2 4) (sourceB2382 + difference 4 2) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA2382 + difference 2 4) (sourceB2382 + difference 4 2) sourceC2382) = raw32580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32580; decide +kernel
    rw [ha]
    exact (canonical32580 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2382 + difference 2 5) (sourceB2382 + difference 5 2) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA2382 + difference 2 5) (sourceB2382 + difference 5 2) sourceC2382) = raw32581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32581; decide +kernel
    rw [ha]
    exact (canonical32581 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2382 + difference 3 0) (sourceB2382 + difference 0 3) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4369) := by
    have ha : (tripleCharges (sourceA2382 + difference 3 0) (sourceB2382 + difference 0 3) sourceC2382) = raw32582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32582; decide +kernel
    rw [ha]
    exact (canonical32582 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2382 + difference 3 1) (sourceB2382 + difference 1 3) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4974) := by
    have ha : (tripleCharges (sourceA2382 + difference 3 1) (sourceB2382 + difference 1 3) sourceC2382) = raw32583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32583; decide +kernel
    rw [ha]
    exact (canonical32583 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2382 + difference 3 2) (sourceB2382 + difference 2 3) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5043) := by
    have ha : (tripleCharges (sourceA2382 + difference 3 2) (sourceB2382 + difference 2 3) sourceC2382) = raw32584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32584; decide +kernel
    rw [ha]
    exact (canonical32584 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2382 + difference 3 4) (sourceB2382 + difference 4 3) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2382 + difference 3 4) (sourceB2382 + difference 4 3) sourceC2382) = raw32585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32585; decide +kernel
    rw [ha]
    exact (canonical32585 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2382 + difference 3 5) (sourceB2382 + difference 5 3) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2382 + difference 3 5) (sourceB2382 + difference 5 3) sourceC2382) = raw32586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32586; decide +kernel
    rw [ha]
    exact (canonical32586 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2382 + difference 4 0) (sourceB2382 + difference 0 4) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4369) := by
    have ha : (tripleCharges (sourceA2382 + difference 4 0) (sourceB2382 + difference 0 4) sourceC2382) = raw32587 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32587; decide +kernel
    rw [ha]
    exact (canonical32587 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2382 + difference 4 1) (sourceB2382 + difference 1 4) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4974) := by
    have ha : (tripleCharges (sourceA2382 + difference 4 1) (sourceB2382 + difference 1 4) sourceC2382) = raw32588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32588; decide +kernel
    rw [ha]
    exact (canonical32588 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2382 + difference 4 2) (sourceB2382 + difference 2 4) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5043) := by
    have ha : (tripleCharges (sourceA2382 + difference 4 2) (sourceB2382 + difference 2 4) sourceC2382) = raw32589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32589; decide +kernel
    rw [ha]
    exact (canonical32589 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2382 + difference 4 3) (sourceB2382 + difference 3 4) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2382 + difference 4 3) (sourceB2382 + difference 3 4) sourceC2382) = raw32590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32590; decide +kernel
    rw [ha]
    exact (canonical32590 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2382 + difference 4 5) (sourceB2382 + difference 5 4) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2382 + difference 4 5) (sourceB2382 + difference 5 4) sourceC2382) = raw32591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32591; decide +kernel
    rw [ha]
    exact (canonical32591 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2382 + difference 5 0) (sourceB2382 + difference 0 5) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4365) := by
    have ha : (tripleCharges (sourceA2382 + difference 5 0) (sourceB2382 + difference 0 5) sourceC2382) = raw32592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32592; decide +kernel
    rw [ha]
    exact (canonical32592 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2382 + difference 5 1) (sourceB2382 + difference 1 5) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4970) := by
    have ha : (tripleCharges (sourceA2382 + difference 5 1) (sourceB2382 + difference 1 5) sourceC2382) = raw32593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32593; decide +kernel
    rw [ha]
    exact (canonical32593 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2382 + difference 5 2) (sourceB2382 + difference 2 5) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5041) := by
    have ha : (tripleCharges (sourceA2382 + difference 5 2) (sourceB2382 + difference 2 5) sourceC2382) = raw32594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32594; decide +kernel
    rw [ha]
    exact (canonical32594 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2382 + difference 5 3) (sourceB2382 + difference 3 5) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA2382 + difference 5 3) (sourceB2382 + difference 3 5) sourceC2382) = raw32595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32595; decide +kernel
    rw [ha]
    exact (canonical32595 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2382 + difference 5 4) (sourceB2382 + difference 4 5) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA2382 + difference 5 4) (sourceB2382 + difference 4 5) sourceC2382) = raw32596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32596; decide +kernel
    rw [ha]
    exact (canonical32596 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2382 sourceB2382 sourceC2382
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2382, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2383 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2383 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2383 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceForm2383 : Integer.Sparse Master := [(Sum.inr 1703, 1), (Sum.inr 1704, 1), (Sum.inr 1709, 1), (Sum.inr 1721, 2), (Sum.inr 3458, 1), (Sum.inr 3461, 1), (Sum.inr 3465, 2), (Sum.inr 3529, 2), (Sum.inr 3530, 2), (Sum.inr 3535, 2), (Sum.inr 3542, 2), (Sum.inr 3587, 1), (Sum.inr 3588, 1), (Sum.inr 3592, 2), (Sum.inr 3617, 1), (Sum.inr 3619, 1), (Sum.inr 3621, 2), (Sum.inr 3774, 1), (Sum.inr 3952, 1), (Sum.inr 3961, 2), (Sum.inr 3962, 1)]

theorem sourceEq2383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2383 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2383 + difference 0 1) (sourceB2383 + difference 1 0) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3774) := by
    have ha : (tripleCharges (sourceA2383 + difference 0 1) (sourceB2383 + difference 1 0) sourceC2383) = raw32597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32597; decide +kernel
    rw [ha]
    exact (canonical32597 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2383 + difference 0 2) (sourceB2383 + difference 2 0) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3952) := by
    have ha : (tripleCharges (sourceA2383 + difference 0 2) (sourceB2383 + difference 2 0) sourceC2383) = raw32598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32598; decide +kernel
    rw [ha]
    exact (canonical32598 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2383 + difference 0 3) (sourceB2383 + difference 3 0) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA2383 + difference 0 3) (sourceB2383 + difference 3 0) sourceC2383) = raw32599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32599; decide +kernel
    rw [ha]
    exact (canonical32599 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2383 + difference 0 4) (sourceB2383 + difference 4 0) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA2383 + difference 0 4) (sourceB2383 + difference 4 0) sourceC2383) = raw32600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32600; decide +kernel
    rw [ha]
    exact (canonical32600 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2383 + difference 0 5) (sourceB2383 + difference 5 0) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3962) := by
    have ha : (tripleCharges (sourceA2383 + difference 0 5) (sourceB2383 + difference 5 0) sourceC2383) = raw32601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32601; decide +kernel
    rw [ha]
    exact (canonical32601 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2383 + difference 1 0) (sourceB2383 + difference 0 1) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA2383 + difference 1 0) (sourceB2383 + difference 0 1) sourceC2383) = raw32602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32602; decide +kernel
    rw [ha]
    exact (canonical32602 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2383 + difference 1 2) (sourceB2383 + difference 2 1) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA2383 + difference 1 2) (sourceB2383 + difference 2 1) sourceC2383) = raw32603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32603; decide +kernel
    rw [ha]
    exact (canonical32603 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2383 + difference 1 3) (sourceB2383 + difference 3 1) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA2383 + difference 1 3) (sourceB2383 + difference 3 1) sourceC2383) = raw32604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32604; decide +kernel
    rw [ha]
    exact (canonical32604 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2383 + difference 1 4) (sourceB2383 + difference 4 1) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA2383 + difference 1 4) (sourceB2383 + difference 4 1) sourceC2383) = raw32605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32605; decide +kernel
    rw [ha]
    exact (canonical32605 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2383 + difference 1 5) (sourceB2383 + difference 5 1) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3619) := by
    have ha : (tripleCharges (sourceA2383 + difference 1 5) (sourceB2383 + difference 5 1) sourceC2383) = raw32606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32606; decide +kernel
    rw [ha]
    exact (canonical32606 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2383 + difference 2 0) (sourceB2383 + difference 0 2) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1703) := by
    have ha : (tripleCharges (sourceA2383 + difference 2 0) (sourceB2383 + difference 0 2) sourceC2383) = raw32607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32607; decide +kernel
    rw [ha]
    exact (canonical32607 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2383 + difference 2 1) (sourceB2383 + difference 1 2) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3587) := by
    have ha : (tripleCharges (sourceA2383 + difference 2 1) (sourceB2383 + difference 1 2) sourceC2383) = raw32608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32608; decide +kernel
    rw [ha]
    exact (canonical32608 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2383 + difference 2 3) (sourceB2383 + difference 3 2) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA2383 + difference 2 3) (sourceB2383 + difference 3 2) sourceC2383) = raw32609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32609; decide +kernel
    rw [ha]
    exact (canonical32609 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2383 + difference 2 4) (sourceB2383 + difference 4 2) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA2383 + difference 2 4) (sourceB2383 + difference 4 2) sourceC2383) = raw32610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32610; decide +kernel
    rw [ha]
    exact (canonical32610 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2383 + difference 2 5) (sourceB2383 + difference 5 2) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3617) := by
    have ha : (tripleCharges (sourceA2383 + difference 2 5) (sourceB2383 + difference 5 2) sourceC2383) = raw32611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32611; decide +kernel
    rw [ha]
    exact (canonical32611 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2383 + difference 3 0) (sourceB2383 + difference 0 3) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA2383 + difference 3 0) (sourceB2383 + difference 0 3) sourceC2383) = raw32612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32612; decide +kernel
    rw [ha]
    exact (canonical32612 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2383 + difference 3 1) (sourceB2383 + difference 1 3) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3592) := by
    have ha : (tripleCharges (sourceA2383 + difference 3 1) (sourceB2383 + difference 1 3) sourceC2383) = raw32613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32613; decide +kernel
    rw [ha]
    exact (canonical32613 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2383 + difference 3 2) (sourceB2383 + difference 2 3) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3465) := by
    have ha : (tripleCharges (sourceA2383 + difference 3 2) (sourceB2383 + difference 2 3) sourceC2383) = raw32614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32614; decide +kernel
    rw [ha]
    exact (canonical32614 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2383 + difference 3 4) (sourceB2383 + difference 4 3) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA2383 + difference 3 4) (sourceB2383 + difference 4 3) sourceC2383) = raw32615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32615; decide +kernel
    rw [ha]
    exact (canonical32615 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2383 + difference 3 5) (sourceB2383 + difference 5 3) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3621) := by
    have ha : (tripleCharges (sourceA2383 + difference 3 5) (sourceB2383 + difference 5 3) sourceC2383) = raw32616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32616; decide +kernel
    rw [ha]
    exact (canonical32616 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2383 + difference 4 0) (sourceB2383 + difference 0 4) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA2383 + difference 4 0) (sourceB2383 + difference 0 4) sourceC2383) = raw32617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32617; decide +kernel
    rw [ha]
    exact (canonical32617 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2383 + difference 4 1) (sourceB2383 + difference 1 4) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3592) := by
    have ha : (tripleCharges (sourceA2383 + difference 4 1) (sourceB2383 + difference 1 4) sourceC2383) = raw32618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32618; decide +kernel
    rw [ha]
    exact (canonical32618 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2383 + difference 4 2) (sourceB2383 + difference 2 4) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3465) := by
    have ha : (tripleCharges (sourceA2383 + difference 4 2) (sourceB2383 + difference 2 4) sourceC2383) = raw32619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32619; decide +kernel
    rw [ha]
    exact (canonical32619 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2383 + difference 4 3) (sourceB2383 + difference 3 4) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA2383 + difference 4 3) (sourceB2383 + difference 3 4) sourceC2383) = raw32620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32620; decide +kernel
    rw [ha]
    exact (canonical32620 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2383 + difference 4 5) (sourceB2383 + difference 5 4) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3621) := by
    have ha : (tripleCharges (sourceA2383 + difference 4 5) (sourceB2383 + difference 5 4) sourceC2383) = raw32621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32621; decide +kernel
    rw [ha]
    exact (canonical32621 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2383 + difference 5 0) (sourceB2383 + difference 0 5) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1704) := by
    have ha : (tripleCharges (sourceA2383 + difference 5 0) (sourceB2383 + difference 0 5) sourceC2383) = raw32622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32622; decide +kernel
    rw [ha]
    exact (canonical32622 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2383 + difference 5 1) (sourceB2383 + difference 1 5) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3588) := by
    have ha : (tripleCharges (sourceA2383 + difference 5 1) (sourceB2383 + difference 1 5) sourceC2383) = raw32623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32623; decide +kernel
    rw [ha]
    exact (canonical32623 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2383 + difference 5 2) (sourceB2383 + difference 2 5) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3458) := by
    have ha : (tripleCharges (sourceA2383 + difference 5 2) (sourceB2383 + difference 2 5) sourceC2383) = raw32624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32624; decide +kernel
    rw [ha]
    exact (canonical32624 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2383 + difference 5 3) (sourceB2383 + difference 3 5) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA2383 + difference 5 3) (sourceB2383 + difference 3 5) sourceC2383) = raw32625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32625; decide +kernel
    rw [ha]
    exact (canonical32625 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2383 + difference 5 4) (sourceB2383 + difference 4 5) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA2383 + difference 5 4) (sourceB2383 + difference 4 5) sourceC2383) = raw32626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32626; decide +kernel
    rw [ha]
    exact (canonical32626 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2383 sourceB2383 sourceC2383
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2383, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2384 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2384 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceC2384 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceForm2384 : Integer.Sparse Master := [(Sum.inr 4513, 1), (Sum.inr 4514, 1), (Sum.inr 4515, 1), (Sum.inr 4518, 1), (Sum.inr 4602, 1), (Sum.inr 4713, 1), (Sum.inr 4719, 1), (Sum.inr 4742, 1), (Sum.inr 4843, 1), (Sum.inr 4981, 1), (Sum.inr 4983, 1), (Sum.inr 4984, 1), (Sum.inr 5119, 1), (Sum.inr 5120, 1), (Sum.inr 5149, 1), (Sum.inr 5192, 1), (Sum.inr 5193, 1), (Sum.inr 5202, 1), (Sum.inr 5203, 1), (Sum.inr 5204, 2), (Sum.inr 5207, 1), (Sum.inr 5228, 1), (Sum.inr 5284, 1), (Sum.inr 5292, 1), (Sum.inr 5294, 1), (Sum.inr 5397, 1), (Sum.inr 5411, 1), (Sum.inr 5443, 1), (Sum.inr 5450, 1)]

theorem sourceEq2384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2384 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2384 + difference 0 1) (sourceB2384 + difference 1 0) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2384 + difference 0 1) (sourceB2384 + difference 1 0) sourceC2384) = raw32627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32627; decide +kernel
    rw [ha]
    exact (canonical32627 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2384 + difference 0 2) (sourceB2384 + difference 2 0) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA2384 + difference 0 2) (sourceB2384 + difference 2 0) sourceC2384) = raw32628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32628; decide +kernel
    rw [ha]
    exact (canonical32628 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2384 + difference 0 3) (sourceB2384 + difference 3 0) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2384 + difference 0 3) (sourceB2384 + difference 3 0) sourceC2384) = raw3315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw3315; decide +kernel
    rw [ha]
    exact (canonical3315 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2384 + difference 0 4) (sourceB2384 + difference 4 0) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA2384 + difference 0 4) (sourceB2384 + difference 4 0) sourceC2384) = raw32629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32629; decide +kernel
    rw [ha]
    exact (canonical32629 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2384 + difference 0 5) (sourceB2384 + difference 5 0) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2384 + difference 0 5) (sourceB2384 + difference 5 0) sourceC2384) = raw3305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw3305; decide +kernel
    rw [ha]
    exact (canonical3305 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2384 + difference 1 0) (sourceB2384 + difference 0 1) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA2384 + difference 1 0) (sourceB2384 + difference 0 1) sourceC2384) = raw32630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32630; decide +kernel
    rw [ha]
    exact (canonical32630 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2384 + difference 1 2) (sourceB2384 + difference 2 1) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2384 + difference 1 2) (sourceB2384 + difference 2 1) sourceC2384) = raw32631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32631; decide +kernel
    rw [ha]
    exact (canonical32631 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2384 + difference 1 3) (sourceB2384 + difference 3 1) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA2384 + difference 1 3) (sourceB2384 + difference 3 1) sourceC2384) = raw3314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw3314; decide +kernel
    rw [ha]
    exact (canonical3314 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2384 + difference 1 4) (sourceB2384 + difference 4 1) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA2384 + difference 1 4) (sourceB2384 + difference 4 1) sourceC2384) = raw32632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32632; decide +kernel
    rw [ha]
    exact (canonical32632 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2384 + difference 1 5) (sourceB2384 + difference 5 1) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA2384 + difference 1 5) (sourceB2384 + difference 5 1) sourceC2384) = raw3304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw3304; decide +kernel
    rw [ha]
    exact (canonical3304 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2384 + difference 2 0) (sourceB2384 + difference 0 2) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4513) := by
    have ha : (tripleCharges (sourceA2384 + difference 2 0) (sourceB2384 + difference 0 2) sourceC2384) = raw32633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32633; decide +kernel
    rw [ha]
    exact (canonical32633 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2384 + difference 2 1) (sourceB2384 + difference 1 2) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4981) := by
    have ha : (tripleCharges (sourceA2384 + difference 2 1) (sourceB2384 + difference 1 2) sourceC2384) = raw32634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32634; decide +kernel
    rw [ha]
    exact (canonical32634 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2384 + difference 2 3) (sourceB2384 + difference 3 2) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2384 + difference 2 3) (sourceB2384 + difference 3 2) sourceC2384) = raw28349 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw28349; decide +kernel
    rw [ha]
    exact (canonical28349 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2384 + difference 2 4) (sourceB2384 + difference 4 2) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA2384 + difference 2 4) (sourceB2384 + difference 4 2) sourceC2384) = raw32635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32635; decide +kernel
    rw [ha]
    exact (canonical32635 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2384 + difference 2 5) (sourceB2384 + difference 5 2) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA2384 + difference 2 5) (sourceB2384 + difference 5 2) sourceC2384) = raw32636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32636; decide +kernel
    rw [ha]
    exact (canonical32636 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2384 + difference 3 0) (sourceB2384 + difference 0 3) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4515) := by
    have ha : (tripleCharges (sourceA2384 + difference 3 0) (sourceB2384 + difference 0 3) sourceC2384) = raw32637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32637; decide +kernel
    rw [ha]
    exact (canonical32637 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2384 + difference 3 1) (sourceB2384 + difference 1 3) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4984) := by
    have ha : (tripleCharges (sourceA2384 + difference 3 1) (sourceB2384 + difference 1 3) sourceC2384) = raw32638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32638; decide +kernel
    rw [ha]
    exact (canonical32638 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2384 + difference 3 2) (sourceB2384 + difference 2 3) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5120) := by
    have ha : (tripleCharges (sourceA2384 + difference 3 2) (sourceB2384 + difference 2 3) sourceC2384) = raw32639 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32639; decide +kernel
    rw [ha]
    exact (canonical32639 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2384 + difference 3 4) (sourceB2384 + difference 4 3) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5193) := by
    have ha : (tripleCharges (sourceA2384 + difference 3 4) (sourceB2384 + difference 4 3) sourceC2384) = raw32640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32640; decide +kernel
    rw [ha]
    exact (canonical32640 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2384 + difference 3 5) (sourceB2384 + difference 5 3) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2384 + difference 3 5) (sourceB2384 + difference 5 3) sourceC2384) = raw32641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32641; decide +kernel
    rw [ha]
    exact (canonical32641 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2384 + difference 4 0) (sourceB2384 + difference 0 4) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4518) := by
    have ha : (tripleCharges (sourceA2384 + difference 4 0) (sourceB2384 + difference 0 4) sourceC2384) = raw32642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32642; decide +kernel
    rw [ha]
    exact (canonical32642 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2384 + difference 4 1) (sourceB2384 + difference 1 4) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4983) := by
    have ha : (tripleCharges (sourceA2384 + difference 4 1) (sourceB2384 + difference 1 4) sourceC2384) = raw32643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32643; decide +kernel
    rw [ha]
    exact (canonical32643 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2384 + difference 4 2) (sourceB2384 + difference 2 4) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5119) := by
    have ha : (tripleCharges (sourceA2384 + difference 4 2) (sourceB2384 + difference 2 4) sourceC2384) = raw32644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32644; decide +kernel
    rw [ha]
    exact (canonical32644 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2384 + difference 4 3) (sourceB2384 + difference 3 4) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2384 + difference 4 3) (sourceB2384 + difference 3 4) sourceC2384) = raw28359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw28359; decide +kernel
    rw [ha]
    exact (canonical28359 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2384 + difference 4 5) (sourceB2384 + difference 5 4) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2384 + difference 4 5) (sourceB2384 + difference 5 4) sourceC2384) = raw32645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32645; decide +kernel
    rw [ha]
    exact (canonical32645 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2384 + difference 5 0) (sourceB2384 + difference 0 5) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4514) := by
    have ha : (tripleCharges (sourceA2384 + difference 5 0) (sourceB2384 + difference 0 5) sourceC2384) = raw28350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw28350; decide +kernel
    rw [ha]
    exact (canonical28350 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2384 + difference 5 1) (sourceB2384 + difference 1 5) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4719) := by
    have ha : (tripleCharges (sourceA2384 + difference 5 1) (sourceB2384 + difference 1 5) sourceC2384) = raw28351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw28351; decide +kernel
    rw [ha]
    exact (canonical28351 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2384 + difference 5 2) (sourceB2384 + difference 2 5) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4713) := by
    have ha : (tripleCharges (sourceA2384 + difference 5 2) (sourceB2384 + difference 2 5) sourceC2384) = raw28352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw28352; decide +kernel
    rw [ha]
    exact (canonical28352 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2384 + difference 5 3) (sourceB2384 + difference 3 5) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA2384 + difference 5 3) (sourceB2384 + difference 3 5) sourceC2384) = raw32646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw32646; decide +kernel
    rw [ha]
    exact (canonical32646 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2384 + difference 5 4) (sourceB2384 + difference 4 5) sourceC2384) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA2384 + difference 5 4) (sourceB2384 + difference 4 5) sourceC2384) = raw28353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2384 sourceB2384 sourceC2384 difference raw28353; decide +kernel
    rw [ha]
    exact (canonical28353 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2384 sourceB2384 sourceC2384
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2384, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2385 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2385 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceC2385 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceForm2385 : Integer.Sparse Master := [(Sum.inr 1097, 1), (Sum.inr 1098, 1), (Sum.inr 1099, 1), (Sum.inr 1102, 1), (Sum.inr 1236, 1), (Sum.inr 1867, 1), (Sum.inr 1873, 1), (Sum.inr 1915, 1), (Sum.inr 2062, 1), (Sum.inr 2791, 1), (Sum.inr 2792, 1), (Sum.inr 2794, 1), (Sum.inr 2844, 1), (Sum.inr 2845, 1), (Sum.inr 2853, 1), (Sum.inr 2856, 1), (Sum.inr 2880, 1), (Sum.inr 2881, 2), (Sum.inr 2884, 1), (Sum.inr 2889, 1), (Sum.inr 2924, 1), (Sum.inr 3077, 1), (Sum.inr 3100, 1), (Sum.inr 3101, 1), (Sum.inr 3391, 1), (Sum.inr 3782, 1), (Sum.inr 3809, 1), (Sum.inr 3862, 1), (Sum.inr 4029, 1)]

theorem sourceEq2385 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2385 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2385 + difference 0 1) (sourceB2385 + difference 1 0) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA2385 + difference 0 1) (sourceB2385 + difference 1 0) sourceC2385) = raw32647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32647; decide +kernel
    rw [ha]
    exact (canonical32647 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2385 + difference 0 2) (sourceB2385 + difference 2 0) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA2385 + difference 0 2) (sourceB2385 + difference 2 0) sourceC2385) = raw32648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32648; decide +kernel
    rw [ha]
    exact (canonical32648 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2385 + difference 0 3) (sourceB2385 + difference 3 0) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA2385 + difference 0 3) (sourceB2385 + difference 3 0) sourceC2385) = raw28369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw28369; decide +kernel
    rw [ha]
    exact (canonical28369 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2385 + difference 0 4) (sourceB2385 + difference 4 0) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA2385 + difference 0 4) (sourceB2385 + difference 4 0) sourceC2385) = raw32649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32649; decide +kernel
    rw [ha]
    exact (canonical32649 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2385 + difference 0 5) (sourceB2385 + difference 5 0) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA2385 + difference 0 5) (sourceB2385 + difference 5 0) sourceC2385) = raw32650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32650; decide +kernel
    rw [ha]
    exact (canonical32650 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2385 + difference 1 0) (sourceB2385 + difference 0 1) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA2385 + difference 1 0) (sourceB2385 + difference 0 1) sourceC2385) = raw32651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32651; decide +kernel
    rw [ha]
    exact (canonical32651 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2385 + difference 1 2) (sourceB2385 + difference 2 1) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2385 + difference 1 2) (sourceB2385 + difference 2 1) sourceC2385) = raw32652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32652; decide +kernel
    rw [ha]
    exact (canonical32652 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2385 + difference 1 3) (sourceB2385 + difference 3 1) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA2385 + difference 1 3) (sourceB2385 + difference 3 1) sourceC2385) = raw28374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw28374; decide +kernel
    rw [ha]
    exact (canonical28374 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2385 + difference 1 4) (sourceB2385 + difference 4 1) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA2385 + difference 1 4) (sourceB2385 + difference 4 1) sourceC2385) = raw32653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32653; decide +kernel
    rw [ha]
    exact (canonical32653 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2385 + difference 1 5) (sourceB2385 + difference 5 1) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA2385 + difference 1 5) (sourceB2385 + difference 5 1) sourceC2385) = raw32654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32654; decide +kernel
    rw [ha]
    exact (canonical32654 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2385 + difference 2 0) (sourceB2385 + difference 0 2) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1097) := by
    have ha : (tripleCharges (sourceA2385 + difference 2 0) (sourceB2385 + difference 0 2) sourceC2385) = raw32655 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32655; decide +kernel
    rw [ha]
    exact (canonical32655 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2385 + difference 2 1) (sourceB2385 + difference 1 2) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2791) := by
    have ha : (tripleCharges (sourceA2385 + difference 2 1) (sourceB2385 + difference 1 2) sourceC2385) = raw32656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32656; decide +kernel
    rw [ha]
    exact (canonical32656 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2385 + difference 2 3) (sourceB2385 + difference 3 2) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA2385 + difference 2 3) (sourceB2385 + difference 3 2) sourceC2385) = raw28379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw28379; decide +kernel
    rw [ha]
    exact (canonical28379 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2385 + difference 2 4) (sourceB2385 + difference 4 2) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2853) := by
    have ha : (tripleCharges (sourceA2385 + difference 2 4) (sourceB2385 + difference 4 2) sourceC2385) = raw32657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32657; decide +kernel
    rw [ha]
    exact (canonical32657 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2385 + difference 2 5) (sourceB2385 + difference 5 2) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2880) := by
    have ha : (tripleCharges (sourceA2385 + difference 2 5) (sourceB2385 + difference 5 2) sourceC2385) = raw32658 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32658; decide +kernel
    rw [ha]
    exact (canonical32658 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2385 + difference 3 0) (sourceB2385 + difference 0 3) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1099) := by
    have ha : (tripleCharges (sourceA2385 + difference 3 0) (sourceB2385 + difference 0 3) sourceC2385) = raw32659 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32659; decide +kernel
    rw [ha]
    exact (canonical32659 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2385 + difference 3 1) (sourceB2385 + difference 1 3) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2792) := by
    have ha : (tripleCharges (sourceA2385 + difference 3 1) (sourceB2385 + difference 1 3) sourceC2385) = raw32660 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32660; decide +kernel
    rw [ha]
    exact (canonical32660 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2385 + difference 3 2) (sourceB2385 + difference 2 3) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2844) := by
    have ha : (tripleCharges (sourceA2385 + difference 3 2) (sourceB2385 + difference 2 3) sourceC2385) = raw32661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32661; decide +kernel
    rw [ha]
    exact (canonical32661 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2385 + difference 3 4) (sourceB2385 + difference 4 3) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2856) := by
    have ha : (tripleCharges (sourceA2385 + difference 3 4) (sourceB2385 + difference 4 3) sourceC2385) = raw32662 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32662; decide +kernel
    rw [ha]
    exact (canonical32662 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2385 + difference 3 5) (sourceB2385 + difference 5 3) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA2385 + difference 3 5) (sourceB2385 + difference 5 3) sourceC2385) = raw32663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32663; decide +kernel
    rw [ha]
    exact (canonical32663 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2385 + difference 4 0) (sourceB2385 + difference 0 4) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1102) := by
    have ha : (tripleCharges (sourceA2385 + difference 4 0) (sourceB2385 + difference 0 4) sourceC2385) = raw32664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32664; decide +kernel
    rw [ha]
    exact (canonical32664 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2385 + difference 4 1) (sourceB2385 + difference 1 4) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2794) := by
    have ha : (tripleCharges (sourceA2385 + difference 4 1) (sourceB2385 + difference 1 4) sourceC2385) = raw32665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32665; decide +kernel
    rw [ha]
    exact (canonical32665 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2385 + difference 4 2) (sourceB2385 + difference 2 4) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2845) := by
    have ha : (tripleCharges (sourceA2385 + difference 4 2) (sourceB2385 + difference 2 4) sourceC2385) = raw32666 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32666; decide +kernel
    rw [ha]
    exact (canonical32666 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2385 + difference 4 3) (sourceB2385 + difference 3 4) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA2385 + difference 4 3) (sourceB2385 + difference 3 4) sourceC2385) = raw28389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw28389; decide +kernel
    rw [ha]
    exact (canonical28389 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2385 + difference 4 5) (sourceB2385 + difference 5 4) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA2385 + difference 4 5) (sourceB2385 + difference 5 4) sourceC2385) = raw32667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32667; decide +kernel
    rw [ha]
    exact (canonical32667 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2385 + difference 5 0) (sourceB2385 + difference 0 5) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1098) := by
    have ha : (tripleCharges (sourceA2385 + difference 5 0) (sourceB2385 + difference 0 5) sourceC2385) = raw28380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw28380; decide +kernel
    rw [ha]
    exact (canonical28380 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2385 + difference 5 1) (sourceB2385 + difference 1 5) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1873) := by
    have ha : (tripleCharges (sourceA2385 + difference 5 1) (sourceB2385 + difference 1 5) sourceC2385) = raw28381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw28381; decide +kernel
    rw [ha]
    exact (canonical28381 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2385 + difference 5 2) (sourceB2385 + difference 2 5) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1867) := by
    have ha : (tripleCharges (sourceA2385 + difference 5 2) (sourceB2385 + difference 2 5) sourceC2385) = raw28382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw28382; decide +kernel
    rw [ha]
    exact (canonical28382 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2385 + difference 5 3) (sourceB2385 + difference 3 5) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA2385 + difference 5 3) (sourceB2385 + difference 3 5) sourceC2385) = raw32668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw32668; decide +kernel
    rw [ha]
    exact (canonical32668 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2385 + difference 5 4) (sourceB2385 + difference 4 5) sourceC2385) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1915) := by
    have ha : (tripleCharges (sourceA2385 + difference 5 4) (sourceB2385 + difference 4 5) sourceC2385) = raw28383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2385 sourceB2385 sourceC2385 difference raw28383; decide +kernel
    rw [ha]
    exact (canonical28383 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2385 sourceB2385 sourceC2385
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2385, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2386 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2386 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2386 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceForm2386 : Integer.Sparse Master := [(Sum.inr 4366, 1), (Sum.inr 4367, 1), (Sum.inr 4368, 1), (Sum.inr 4372, 1), (Sum.inr 4475, 1), (Sum.inr 4971, 1), (Sum.inr 4972, 1), (Sum.inr 4973, 1), (Sum.inr 4977, 1), (Sum.inr 5034, 1), (Sum.inr 5042, 1), (Sum.inr 5044, 1), (Sum.inr 5086, 1), (Sum.inr 5109, 1), (Sum.inr 5139, 1), (Sum.inr 5187, 1), (Sum.inr 5188, 1), (Sum.inr 5197, 1), (Sum.inr 5198, 1), (Sum.inr 5199, 1), (Sum.inr 5204, 1), (Sum.inr 5207, 1), (Sum.inr 5267, 1), (Sum.inr 5299, 1), (Sum.inr 5302, 1), (Sum.inr 5367, 1), (Sum.inr 5395, 1), (Sum.inr 5413, 1), (Sum.inr 5428, 1), (Sum.inr 5473, 1)]

theorem sourceEq2386 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2386 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2386 + difference 0 1) (sourceB2386 + difference 1 0) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2386 + difference 0 1) (sourceB2386 + difference 1 0) sourceC2386) = raw32669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32669; decide +kernel
    rw [ha]
    exact (canonical32669 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2386 + difference 0 2) (sourceB2386 + difference 2 0) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA2386 + difference 0 2) (sourceB2386 + difference 2 0) sourceC2386) = raw32670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32670; decide +kernel
    rw [ha]
    exact (canonical32670 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2386 + difference 0 3) (sourceB2386 + difference 3 0) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA2386 + difference 0 3) (sourceB2386 + difference 3 0) sourceC2386) = raw32671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32671; decide +kernel
    rw [ha]
    exact (canonical32671 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2386 + difference 0 4) (sourceB2386 + difference 4 0) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA2386 + difference 0 4) (sourceB2386 + difference 4 0) sourceC2386) = raw32672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32672; decide +kernel
    rw [ha]
    exact (canonical32672 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2386 + difference 0 5) (sourceB2386 + difference 5 0) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2386 + difference 0 5) (sourceB2386 + difference 5 0) sourceC2386) = raw32673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32673; decide +kernel
    rw [ha]
    exact (canonical32673 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2386 + difference 1 0) (sourceB2386 + difference 0 1) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA2386 + difference 1 0) (sourceB2386 + difference 0 1) sourceC2386) = raw32674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32674; decide +kernel
    rw [ha]
    exact (canonical32674 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2386 + difference 1 2) (sourceB2386 + difference 2 1) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA2386 + difference 1 2) (sourceB2386 + difference 2 1) sourceC2386) = raw32675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32675; decide +kernel
    rw [ha]
    exact (canonical32675 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2386 + difference 1 3) (sourceB2386 + difference 3 1) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA2386 + difference 1 3) (sourceB2386 + difference 3 1) sourceC2386) = raw32676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32676; decide +kernel
    rw [ha]
    exact (canonical32676 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2386 + difference 1 4) (sourceB2386 + difference 4 1) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA2386 + difference 1 4) (sourceB2386 + difference 4 1) sourceC2386) = raw32677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32677; decide +kernel
    rw [ha]
    exact (canonical32677 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2386 + difference 1 5) (sourceB2386 + difference 5 1) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA2386 + difference 1 5) (sourceB2386 + difference 5 1) sourceC2386) = raw32678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32678; decide +kernel
    rw [ha]
    exact (canonical32678 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2386 + difference 2 0) (sourceB2386 + difference 0 2) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4366) := by
    have ha : (tripleCharges (sourceA2386 + difference 2 0) (sourceB2386 + difference 0 2) sourceC2386) = raw32679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32679; decide +kernel
    rw [ha]
    exact (canonical32679 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2386 + difference 2 1) (sourceB2386 + difference 1 2) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4971) := by
    have ha : (tripleCharges (sourceA2386 + difference 2 1) (sourceB2386 + difference 1 2) sourceC2386) = raw32680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32680; decide +kernel
    rw [ha]
    exact (canonical32680 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2386 + difference 2 3) (sourceB2386 + difference 3 2) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA2386 + difference 2 3) (sourceB2386 + difference 3 2) sourceC2386) = raw32681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32681; decide +kernel
    rw [ha]
    exact (canonical32681 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2386 + difference 2 4) (sourceB2386 + difference 4 2) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2386 + difference 2 4) (sourceB2386 + difference 4 2) sourceC2386) = raw32682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32682; decide +kernel
    rw [ha]
    exact (canonical32682 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2386 + difference 2 5) (sourceB2386 + difference 5 2) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA2386 + difference 2 5) (sourceB2386 + difference 5 2) sourceC2386) = raw32683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32683; decide +kernel
    rw [ha]
    exact (canonical32683 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2386 + difference 3 0) (sourceB2386 + difference 0 3) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4372) := by
    have ha : (tripleCharges (sourceA2386 + difference 3 0) (sourceB2386 + difference 0 3) sourceC2386) = raw32684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32684; decide +kernel
    rw [ha]
    exact (canonical32684 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2386 + difference 3 1) (sourceB2386 + difference 1 3) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2386 + difference 3 1) (sourceB2386 + difference 1 3) sourceC2386) = raw32685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32685; decide +kernel
    rw [ha]
    exact (canonical32685 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2386 + difference 3 2) (sourceB2386 + difference 2 3) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5044) := by
    have ha : (tripleCharges (sourceA2386 + difference 3 2) (sourceB2386 + difference 2 3) sourceC2386) = raw32686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32686; decide +kernel
    rw [ha]
    exact (canonical32686 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2386 + difference 3 4) (sourceB2386 + difference 4 3) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2386 + difference 3 4) (sourceB2386 + difference 4 3) sourceC2386) = raw32687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32687; decide +kernel
    rw [ha]
    exact (canonical32687 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2386 + difference 3 5) (sourceB2386 + difference 5 3) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA2386 + difference 3 5) (sourceB2386 + difference 5 3) sourceC2386) = raw32688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32688; decide +kernel
    rw [ha]
    exact (canonical32688 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2386 + difference 4 0) (sourceB2386 + difference 0 4) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA2386 + difference 4 0) (sourceB2386 + difference 0 4) sourceC2386) = raw32689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32689; decide +kernel
    rw [ha]
    exact (canonical32689 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2386 + difference 4 1) (sourceB2386 + difference 1 4) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2386 + difference 4 1) (sourceB2386 + difference 1 4) sourceC2386) = raw32690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32690; decide +kernel
    rw [ha]
    exact (canonical32690 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2386 + difference 4 2) (sourceB2386 + difference 2 4) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5042) := by
    have ha : (tripleCharges (sourceA2386 + difference 4 2) (sourceB2386 + difference 2 4) sourceC2386) = raw32691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32691; decide +kernel
    rw [ha]
    exact (canonical32691 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2386 + difference 4 3) (sourceB2386 + difference 3 4) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA2386 + difference 4 3) (sourceB2386 + difference 3 4) sourceC2386) = raw32692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32692; decide +kernel
    rw [ha]
    exact (canonical32692 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2386 + difference 4 5) (sourceB2386 + difference 5 4) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA2386 + difference 4 5) (sourceB2386 + difference 5 4) sourceC2386) = raw32693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32693; decide +kernel
    rw [ha]
    exact (canonical32693 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2386 + difference 5 0) (sourceB2386 + difference 0 5) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA2386 + difference 5 0) (sourceB2386 + difference 0 5) sourceC2386) = raw32694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32694; decide +kernel
    rw [ha]
    exact (canonical32694 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2386 + difference 5 1) (sourceB2386 + difference 1 5) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA2386 + difference 5 1) (sourceB2386 + difference 1 5) sourceC2386) = raw32695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32695; decide +kernel
    rw [ha]
    exact (canonical32695 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2386 + difference 5 2) (sourceB2386 + difference 2 5) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5034) := by
    have ha : (tripleCharges (sourceA2386 + difference 5 2) (sourceB2386 + difference 2 5) sourceC2386) = raw32696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32696; decide +kernel
    rw [ha]
    exact (canonical32696 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2386 + difference 5 3) (sourceB2386 + difference 3 5) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA2386 + difference 5 3) (sourceB2386 + difference 3 5) sourceC2386) = raw32697 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32697; decide +kernel
    rw [ha]
    exact (canonical32697 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2386 + difference 5 4) (sourceB2386 + difference 4 5) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA2386 + difference 5 4) (sourceB2386 + difference 4 5) sourceC2386) = raw32698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32698; decide +kernel
    rw [ha]
    exact (canonical32698 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2386 sourceB2386 sourceC2386
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2386, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2387 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2387 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2387 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceForm2387 : Integer.Sparse Master := [(Sum.inr 1711, 1), (Sum.inr 1712, 1), (Sum.inr 1715, 1), (Sum.inr 1720, 1), (Sum.inr 1734, 1), (Sum.inr 3451, 1), (Sum.inr 3457, 1), (Sum.inr 3462, 1), (Sum.inr 3464, 1), (Sum.inr 3474, 1), (Sum.inr 3486, 1), (Sum.inr 3523, 1), (Sum.inr 3537, 1), (Sum.inr 3538, 1), (Sum.inr 3541, 1), (Sum.inr 3569, 1), (Sum.inr 3570, 1), (Sum.inr 3573, 1), (Sum.inr 3578, 1), (Sum.inr 3590, 1), (Sum.inr 3591, 1), (Sum.inr 3595, 1), (Sum.inr 3624, 1), (Sum.inr 3626, 1), (Sum.inr 3631, 1), (Sum.inr 3766, 1), (Sum.inr 3794, 1), (Sum.inr 3817, 1), (Sum.inr 3845, 1), (Sum.inr 3958, 1)]

theorem sourceEq2387 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2387 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2387 + difference 0 1) (sourceB2387 + difference 1 0) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2387 + difference 0 1) (sourceB2387 + difference 1 0) sourceC2387) = raw32699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32699; decide +kernel
    rw [ha]
    exact (canonical32699 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2387 + difference 0 2) (sourceB2387 + difference 2 0) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA2387 + difference 0 2) (sourceB2387 + difference 2 0) sourceC2387) = raw32700 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32700; decide +kernel
    rw [ha]
    exact (canonical32700 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2387 + difference 0 3) (sourceB2387 + difference 3 0) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA2387 + difference 0 3) (sourceB2387 + difference 3 0) sourceC2387) = raw32701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32701; decide +kernel
    rw [ha]
    exact (canonical32701 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2387 + difference 0 4) (sourceB2387 + difference 4 0) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA2387 + difference 0 4) (sourceB2387 + difference 4 0) sourceC2387) = raw32702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32702; decide +kernel
    rw [ha]
    exact (canonical32702 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2387 + difference 0 5) (sourceB2387 + difference 5 0) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA2387 + difference 0 5) (sourceB2387 + difference 5 0) sourceC2387) = raw32703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32703; decide +kernel
    rw [ha]
    exact (canonical32703 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2387 + difference 1 0) (sourceB2387 + difference 0 1) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA2387 + difference 1 0) (sourceB2387 + difference 0 1) sourceC2387) = raw32704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32704; decide +kernel
    rw [ha]
    exact (canonical32704 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2387 + difference 1 2) (sourceB2387 + difference 2 1) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA2387 + difference 1 2) (sourceB2387 + difference 2 1) sourceC2387) = raw32705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32705; decide +kernel
    rw [ha]
    exact (canonical32705 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2387 + difference 1 3) (sourceB2387 + difference 3 1) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA2387 + difference 1 3) (sourceB2387 + difference 3 1) sourceC2387) = raw32706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32706; decide +kernel
    rw [ha]
    exact (canonical32706 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2387 + difference 1 4) (sourceB2387 + difference 4 1) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA2387 + difference 1 4) (sourceB2387 + difference 4 1) sourceC2387) = raw32707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32707; decide +kernel
    rw [ha]
    exact (canonical32707 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2387 + difference 1 5) (sourceB2387 + difference 5 1) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA2387 + difference 1 5) (sourceB2387 + difference 5 1) sourceC2387) = raw32708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32708; decide +kernel
    rw [ha]
    exact (canonical32708 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2387 + difference 2 0) (sourceB2387 + difference 0 2) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1711) := by
    have ha : (tripleCharges (sourceA2387 + difference 2 0) (sourceB2387 + difference 0 2) sourceC2387) = raw32709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32709; decide +kernel
    rw [ha]
    exact (canonical32709 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2387 + difference 2 1) (sourceB2387 + difference 1 2) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3590) := by
    have ha : (tripleCharges (sourceA2387 + difference 2 1) (sourceB2387 + difference 1 2) sourceC2387) = raw32710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32710; decide +kernel
    rw [ha]
    exact (canonical32710 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2387 + difference 2 3) (sourceB2387 + difference 3 2) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA2387 + difference 2 3) (sourceB2387 + difference 3 2) sourceC2387) = raw32711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32711; decide +kernel
    rw [ha]
    exact (canonical32711 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2387 + difference 2 4) (sourceB2387 + difference 4 2) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA2387 + difference 2 4) (sourceB2387 + difference 4 2) sourceC2387) = raw32712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32712; decide +kernel
    rw [ha]
    exact (canonical32712 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2387 + difference 2 5) (sourceB2387 + difference 5 2) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3569) := by
    have ha : (tripleCharges (sourceA2387 + difference 2 5) (sourceB2387 + difference 5 2) sourceC2387) = raw32713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32713; decide +kernel
    rw [ha]
    exact (canonical32713 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2387 + difference 3 0) (sourceB2387 + difference 0 3) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA2387 + difference 3 0) (sourceB2387 + difference 0 3) sourceC2387) = raw32714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32714; decide +kernel
    rw [ha]
    exact (canonical32714 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2387 + difference 3 1) (sourceB2387 + difference 1 3) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2387 + difference 3 1) (sourceB2387 + difference 1 3) sourceC2387) = raw32715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32715; decide +kernel
    rw [ha]
    exact (canonical32715 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2387 + difference 3 2) (sourceB2387 + difference 2 3) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3474) := by
    have ha : (tripleCharges (sourceA2387 + difference 3 2) (sourceB2387 + difference 2 3) sourceC2387) = raw32716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32716; decide +kernel
    rw [ha]
    exact (canonical32716 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2387 + difference 3 4) (sourceB2387 + difference 4 3) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA2387 + difference 3 4) (sourceB2387 + difference 4 3) sourceC2387) = raw32717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32717; decide +kernel
    rw [ha]
    exact (canonical32717 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2387 + difference 3 5) (sourceB2387 + difference 5 3) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA2387 + difference 3 5) (sourceB2387 + difference 5 3) sourceC2387) = raw32718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32718; decide +kernel
    rw [ha]
    exact (canonical32718 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2387 + difference 4 0) (sourceB2387 + difference 0 4) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA2387 + difference 4 0) (sourceB2387 + difference 0 4) sourceC2387) = raw32719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32719; decide +kernel
    rw [ha]
    exact (canonical32719 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2387 + difference 4 1) (sourceB2387 + difference 1 4) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3591) := by
    have ha : (tripleCharges (sourceA2387 + difference 4 1) (sourceB2387 + difference 1 4) sourceC2387) = raw32720 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32720; decide +kernel
    rw [ha]
    exact (canonical32720 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2387 + difference 4 2) (sourceB2387 + difference 2 4) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3462) := by
    have ha : (tripleCharges (sourceA2387 + difference 4 2) (sourceB2387 + difference 2 4) sourceC2387) = raw32721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32721; decide +kernel
    rw [ha]
    exact (canonical32721 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2387 + difference 4 3) (sourceB2387 + difference 3 4) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2387 + difference 4 3) (sourceB2387 + difference 3 4) sourceC2387) = raw32722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32722; decide +kernel
    rw [ha]
    exact (canonical32722 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2387 + difference 4 5) (sourceB2387 + difference 5 4) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA2387 + difference 4 5) (sourceB2387 + difference 5 4) sourceC2387) = raw32723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32723; decide +kernel
    rw [ha]
    exact (canonical32723 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2387 + difference 5 0) (sourceB2387 + difference 0 5) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA2387 + difference 5 0) (sourceB2387 + difference 0 5) sourceC2387) = raw32724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32724; decide +kernel
    rw [ha]
    exact (canonical32724 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2387 + difference 5 1) (sourceB2387 + difference 1 5) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2387 + difference 5 1) (sourceB2387 + difference 1 5) sourceC2387) = raw32725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32725; decide +kernel
    rw [ha]
    exact (canonical32725 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2387 + difference 5 2) (sourceB2387 + difference 2 5) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3451) := by
    have ha : (tripleCharges (sourceA2387 + difference 5 2) (sourceB2387 + difference 2 5) sourceC2387) = raw32726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32726; decide +kernel
    rw [ha]
    exact (canonical32726 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2387 + difference 5 3) (sourceB2387 + difference 3 5) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA2387 + difference 5 3) (sourceB2387 + difference 3 5) sourceC2387) = raw32727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32727; decide +kernel
    rw [ha]
    exact (canonical32727 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2387 + difference 5 4) (sourceB2387 + difference 4 5) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA2387 + difference 5 4) (sourceB2387 + difference 4 5) sourceC2387) = raw32728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32728; decide +kernel
    rw [ha]
    exact (canonical32728 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2387 sourceB2387 sourceC2387
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2387, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2388 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2388 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC2388 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceForm2388 : Integer.Sparse Master := [(Sum.inr 1970, 1), (Sum.inr 2806, 1), (Sum.inr 2812, 2), (Sum.inr 2879, 1), (Sum.inr 3498, 1), (Sum.inr 4084, -1)]

theorem sourceEq2388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2388 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2388 + difference 0 1) (sourceB2388 + difference 1 0) sourceC2388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3498) := by
    have ha : (tripleCharges (sourceA2388 + difference 0 1) (sourceB2388 + difference 1 0) sourceC2388) = raw32729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2388 sourceB2388 sourceC2388 difference raw32729; decide +kernel
    rw [ha]
    exact (canonical32729 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2388 + difference 1 1) (sourceB2388 + difference 1 1) sourceC2388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA2388 + difference 1 1) (sourceB2388 + difference 1 1) sourceC2388) = raw32730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2388 sourceB2388 sourceC2388 difference raw32730; decide +kernel
    rw [ha]
    exact (canonical32730 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2388 + difference 2 1) (sourceB2388 + difference 1 2) sourceC2388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2806) := by
    have ha : (tripleCharges (sourceA2388 + difference 2 1) (sourceB2388 + difference 1 2) sourceC2388) = raw32731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2388 sourceB2388 sourceC2388 difference raw32731; decide +kernel
    rw [ha]
    exact (canonical32731 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2388 + difference 3 1) (sourceB2388 + difference 1 3) sourceC2388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2812) := by
    have ha : (tripleCharges (sourceA2388 + difference 3 1) (sourceB2388 + difference 1 3) sourceC2388) = raw32732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2388 sourceB2388 sourceC2388 difference raw32732; decide +kernel
    rw [ha]
    exact (canonical32732 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2388 + difference 4 1) (sourceB2388 + difference 1 4) sourceC2388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2812) := by
    have ha : (tripleCharges (sourceA2388 + difference 4 1) (sourceB2388 + difference 1 4) sourceC2388) = raw32733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2388 sourceB2388 sourceC2388 difference raw32733; decide +kernel
    rw [ha]
    exact (canonical32733 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2388 + difference 5 1) (sourceB2388 + difference 1 5) sourceC2388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1970) := by
    have ha : (tripleCharges (sourceA2388 + difference 5 1) (sourceB2388 + difference 1 5) sourceC2388) = raw28458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2388 sourceB2388 sourceC2388 difference raw28458; decide +kernel
    rw [ha]
    exact (canonical28458 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2388 + sourceB2388) sourceC2388) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2388 + sourceB2388) sourceC2388) = raw28461 := by
      apply Matrix.ext; unfold doubleCharges sourceA2388 sourceB2388 sourceC2388 raw28461; decide +kernel
    rw [ha]
    exact (canonical28461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2388 sourceB2388 sourceC2388
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2388, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2389 : Charge := ![1, 2, 1, -1, -1, -2]
def sourceB2389 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC2389 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2389 : Integer.Sparse Master := [(Sum.inr 2413, 1), (Sum.inr 3333, 2), (Sum.inr 3356, 1), (Sum.inr 3435, 1), (Sum.inr 3620, 1), (Sum.inr 4080, -1)]

theorem sourceEq2389 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2389 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2389 + difference 0 0) (sourceB2389 + difference 0 0) sourceC2389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3620) := by
    have ha : (tripleCharges (sourceA2389 + difference 0 0) (sourceB2389 + difference 0 0) sourceC2389) = raw32734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2389 sourceB2389 sourceC2389 difference raw32734; decide +kernel
    rw [ha]
    exact (canonical32734 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2389 + difference 0 1) (sourceB2389 + difference 1 0) sourceC2389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3435) := by
    have ha : (tripleCharges (sourceA2389 + difference 0 1) (sourceB2389 + difference 1 0) sourceC2389) = raw32508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2389 sourceB2389 sourceC2389 difference raw32508; decide +kernel
    rw [ha]
    exact (canonical32508 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2389 + difference 0 2) (sourceB2389 + difference 2 0) sourceC2389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3356) := by
    have ha : (tripleCharges (sourceA2389 + difference 0 2) (sourceB2389 + difference 2 0) sourceC2389) = raw32735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2389 sourceB2389 sourceC2389 difference raw32735; decide +kernel
    rw [ha]
    exact (canonical32735 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2389 + difference 0 3) (sourceB2389 + difference 3 0) sourceC2389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3333) := by
    have ha : (tripleCharges (sourceA2389 + difference 0 3) (sourceB2389 + difference 3 0) sourceC2389) = raw32736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2389 sourceB2389 sourceC2389 difference raw32736; decide +kernel
    rw [ha]
    exact (canonical32736 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2389 + difference 0 4) (sourceB2389 + difference 4 0) sourceC2389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3333) := by
    have ha : (tripleCharges (sourceA2389 + difference 0 4) (sourceB2389 + difference 4 0) sourceC2389) = raw32737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2389 sourceB2389 sourceC2389 difference raw32737; decide +kernel
    rw [ha]
    exact (canonical32737 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2389 + difference 0 5) (sourceB2389 + difference 5 0) sourceC2389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2413) := by
    have ha : (tripleCharges (sourceA2389 + difference 0 5) (sourceB2389 + difference 5 0) sourceC2389) = raw32738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2389 sourceB2389 sourceC2389 difference raw32738; decide +kernel
    rw [ha]
    exact (canonical32738 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2389 + sourceB2389) sourceC2389) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2389 + sourceB2389) sourceC2389) = raw31902 := by
      apply Matrix.ext; unfold doubleCharges sourceA2389 sourceB2389 sourceC2389 raw31902; decide +kernel
    rw [ha]
    exact (canonical31902 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2389 sourceB2389 sourceC2389
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2389, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2390 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2390 : Charge := ![1, 2, -2, 0, 0, -1]
def sourceC2390 : Charge := ![2, -1, 2, -1, -1, -1]
def sourceForm2390 : Integer.Sparse Master := [(Sum.inr 2607, 1), (Sum.inr 3067, 1), (Sum.inr 3751, 1), (Sum.inr 3866, 2), (Sum.inr 3867, 1), (Sum.inr 4087, -1)]

theorem sourceEq2390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2390 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2390 + difference 0 0) (sourceB2390 + difference 0 0) sourceC2390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2607) := by
    have ha : (tripleCharges (sourceA2390 + difference 0 0) (sourceB2390 + difference 0 0) sourceC2390) = raw24061 := by
      apply Matrix.ext; unfold tripleCharges sourceA2390 sourceB2390 sourceC2390 difference raw24061; decide +kernel
    rw [ha]
    exact (canonical24061 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2390 + difference 0 1) (sourceB2390 + difference 1 0) sourceC2390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3067) := by
    have ha : (tripleCharges (sourceA2390 + difference 0 1) (sourceB2390 + difference 1 0) sourceC2390) = raw32739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2390 sourceB2390 sourceC2390 difference raw32739; decide +kernel
    rw [ha]
    exact (canonical32739 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2390 + difference 0 2) (sourceB2390 + difference 2 0) sourceC2390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3751) := by
    have ha : (tripleCharges (sourceA2390 + difference 0 2) (sourceB2390 + difference 2 0) sourceC2390) = raw32740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2390 sourceB2390 sourceC2390 difference raw32740; decide +kernel
    rw [ha]
    exact (canonical32740 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2390 + difference 0 3) (sourceB2390 + difference 3 0) sourceC2390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA2390 + difference 0 3) (sourceB2390 + difference 3 0) sourceC2390) = raw32741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2390 sourceB2390 sourceC2390 difference raw32741; decide +kernel
    rw [ha]
    exact (canonical32741 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2390 + difference 0 4) (sourceB2390 + difference 4 0) sourceC2390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA2390 + difference 0 4) (sourceB2390 + difference 4 0) sourceC2390) = raw32742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2390 sourceB2390 sourceC2390 difference raw32742; decide +kernel
    rw [ha]
    exact (canonical32742 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2390 + difference 0 5) (sourceB2390 + difference 5 0) sourceC2390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3867) := by
    have ha : (tripleCharges (sourceA2390 + difference 0 5) (sourceB2390 + difference 5 0) sourceC2390) = raw32743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2390 sourceB2390 sourceC2390 difference raw32743; decide +kernel
    rw [ha]
    exact (canonical32743 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2390 + sourceB2390) sourceC2390) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA2390 + sourceB2390) sourceC2390) = raw24066 := by
      apply Matrix.ext; unfold doubleCharges sourceA2390 sourceB2390 sourceC2390 raw24066; decide +kernel
    rw [ha]
    exact (canonical24066 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2390 sourceB2390 sourceC2390
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2390, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2391 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2391 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2391 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceForm2391 : Integer.Sparse Master := [(Sum.inr 4545, 1), (Sum.inr 4547, 1), (Sum.inr 4548, 1), (Sum.inr 4556, 1), (Sum.inr 4619, 1), (Sum.inr 4963, 1), (Sum.inr 4965, 1), (Sum.inr 4966, 1), (Sum.inr 4976, 1), (Sum.inr 5041, 1), (Sum.inr 5075, 1), (Sum.inr 5112, 1), (Sum.inr 5116, 1), (Sum.inr 5134, 1), (Sum.inr 5141, 1), (Sum.inr 5144, 1), (Sum.inr 5147, 1), (Sum.inr 5151, 1), (Sum.inr 5160, 1), (Sum.inr 5163, 1), (Sum.inr 5164, 1), (Sum.inr 5173, 1), (Sum.inr 5274, 1), (Sum.inr 5291, 1), (Sum.inr 5304, 1), (Sum.inr 5384, 1), (Sum.inr 5400, 1), (Sum.inr 5409, 1), (Sum.inr 5432, 1), (Sum.inr 5438, 1)]

theorem sourceEq2391 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2391 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2391 + difference 0 1) (sourceB2391 + difference 1 0) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2391 + difference 0 1) (sourceB2391 + difference 1 0) sourceC2391) = raw32744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32744; decide +kernel
    rw [ha]
    exact (canonical32744 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2391 + difference 0 2) (sourceB2391 + difference 2 0) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA2391 + difference 0 2) (sourceB2391 + difference 2 0) sourceC2391) = raw32745 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32745; decide +kernel
    rw [ha]
    exact (canonical32745 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2391 + difference 0 3) (sourceB2391 + difference 3 0) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA2391 + difference 0 3) (sourceB2391 + difference 3 0) sourceC2391) = raw32746 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32746; decide +kernel
    rw [ha]
    exact (canonical32746 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2391 + difference 0 4) (sourceB2391 + difference 4 0) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2391 + difference 0 4) (sourceB2391 + difference 4 0) sourceC2391) = raw32747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32747; decide +kernel
    rw [ha]
    exact (canonical32747 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2391 + difference 0 5) (sourceB2391 + difference 5 0) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2391 + difference 0 5) (sourceB2391 + difference 5 0) sourceC2391) = raw32748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32748; decide +kernel
    rw [ha]
    exact (canonical32748 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2391 + difference 1 0) (sourceB2391 + difference 0 1) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA2391 + difference 1 0) (sourceB2391 + difference 0 1) sourceC2391) = raw32749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32749; decide +kernel
    rw [ha]
    exact (canonical32749 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2391 + difference 1 2) (sourceB2391 + difference 2 1) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2391 + difference 1 2) (sourceB2391 + difference 2 1) sourceC2391) = raw24305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw24305; decide +kernel
    rw [ha]
    exact (canonical24305 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2391 + difference 1 3) (sourceB2391 + difference 3 1) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA2391 + difference 1 3) (sourceB2391 + difference 3 1) sourceC2391) = raw24306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw24306; decide +kernel
    rw [ha]
    exact (canonical24306 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2391 + difference 1 4) (sourceB2391 + difference 4 1) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2391 + difference 1 4) (sourceB2391 + difference 4 1) sourceC2391) = raw24307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw24307; decide +kernel
    rw [ha]
    exact (canonical24307 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2391 + difference 1 5) (sourceB2391 + difference 5 1) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA2391 + difference 1 5) (sourceB2391 + difference 5 1) sourceC2391) = raw24308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw24308; decide +kernel
    rw [ha]
    exact (canonical24308 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2391 + difference 2 0) (sourceB2391 + difference 0 2) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4545) := by
    have ha : (tripleCharges (sourceA2391 + difference 2 0) (sourceB2391 + difference 0 2) sourceC2391) = raw24315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw24315; decide +kernel
    rw [ha]
    exact (canonical24315 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2391 + difference 2 1) (sourceB2391 + difference 1 2) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4963) := by
    have ha : (tripleCharges (sourceA2391 + difference 2 1) (sourceB2391 + difference 1 2) sourceC2391) = raw32750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32750; decide +kernel
    rw [ha]
    exact (canonical32750 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2391 + difference 2 3) (sourceB2391 + difference 3 2) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA2391 + difference 2 3) (sourceB2391 + difference 3 2) sourceC2391) = raw32751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32751; decide +kernel
    rw [ha]
    exact (canonical32751 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2391 + difference 2 4) (sourceB2391 + difference 4 2) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2391 + difference 2 4) (sourceB2391 + difference 4 2) sourceC2391) = raw32752 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32752; decide +kernel
    rw [ha]
    exact (canonical32752 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2391 + difference 2 5) (sourceB2391 + difference 5 2) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA2391 + difference 2 5) (sourceB2391 + difference 5 2) sourceC2391) = raw32753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32753; decide +kernel
    rw [ha]
    exact (canonical32753 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2391 + difference 3 0) (sourceB2391 + difference 0 3) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4556) := by
    have ha : (tripleCharges (sourceA2391 + difference 3 0) (sourceB2391 + difference 0 3) sourceC2391) = raw24320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw24320; decide +kernel
    rw [ha]
    exact (canonical24320 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2391 + difference 3 1) (sourceB2391 + difference 1 3) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4966) := by
    have ha : (tripleCharges (sourceA2391 + difference 3 1) (sourceB2391 + difference 1 3) sourceC2391) = raw32754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32754; decide +kernel
    rw [ha]
    exact (canonical32754 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2391 + difference 3 2) (sourceB2391 + difference 2 3) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5112) := by
    have ha : (tripleCharges (sourceA2391 + difference 3 2) (sourceB2391 + difference 2 3) sourceC2391) = raw32755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32755; decide +kernel
    rw [ha]
    exact (canonical32755 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2391 + difference 3 4) (sourceB2391 + difference 4 3) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2391 + difference 3 4) (sourceB2391 + difference 4 3) sourceC2391) = raw32756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32756; decide +kernel
    rw [ha]
    exact (canonical32756 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2391 + difference 3 5) (sourceB2391 + difference 5 3) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA2391 + difference 3 5) (sourceB2391 + difference 5 3) sourceC2391) = raw32757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32757; decide +kernel
    rw [ha]
    exact (canonical32757 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2391 + difference 4 0) (sourceB2391 + difference 0 4) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4548) := by
    have ha : (tripleCharges (sourceA2391 + difference 4 0) (sourceB2391 + difference 0 4) sourceC2391) = raw24325 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw24325; decide +kernel
    rw [ha]
    exact (canonical24325 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2391 + difference 4 1) (sourceB2391 + difference 1 4) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4976) := by
    have ha : (tripleCharges (sourceA2391 + difference 4 1) (sourceB2391 + difference 1 4) sourceC2391) = raw32758 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32758; decide +kernel
    rw [ha]
    exact (canonical32758 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2391 + difference 4 2) (sourceB2391 + difference 2 4) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5116) := by
    have ha : (tripleCharges (sourceA2391 + difference 4 2) (sourceB2391 + difference 2 4) sourceC2391) = raw32759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32759; decide +kernel
    rw [ha]
    exact (canonical32759 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2391 + difference 4 3) (sourceB2391 + difference 3 4) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA2391 + difference 4 3) (sourceB2391 + difference 3 4) sourceC2391) = raw32760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32760; decide +kernel
    rw [ha]
    exact (canonical32760 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2391 + difference 4 5) (sourceB2391 + difference 5 4) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA2391 + difference 4 5) (sourceB2391 + difference 5 4) sourceC2391) = raw32761 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32761; decide +kernel
    rw [ha]
    exact (canonical32761 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2391 + difference 5 0) (sourceB2391 + difference 0 5) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4547) := by
    have ha : (tripleCharges (sourceA2391 + difference 5 0) (sourceB2391 + difference 0 5) sourceC2391) = raw24330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw24330; decide +kernel
    rw [ha]
    exact (canonical24330 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2391 + difference 5 1) (sourceB2391 + difference 1 5) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4965) := by
    have ha : (tripleCharges (sourceA2391 + difference 5 1) (sourceB2391 + difference 1 5) sourceC2391) = raw32762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32762; decide +kernel
    rw [ha]
    exact (canonical32762 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2391 + difference 5 2) (sourceB2391 + difference 2 5) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5041) := by
    have ha : (tripleCharges (sourceA2391 + difference 5 2) (sourceB2391 + difference 2 5) sourceC2391) = raw32763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32763; decide +kernel
    rw [ha]
    exact (canonical32763 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2391 + difference 5 3) (sourceB2391 + difference 3 5) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA2391 + difference 5 3) (sourceB2391 + difference 3 5) sourceC2391) = raw32764 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32764; decide +kernel
    rw [ha]
    exact (canonical32764 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2391 + difference 5 4) (sourceB2391 + difference 4 5) sourceC2391) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2391 + difference 5 4) (sourceB2391 + difference 4 5) sourceC2391) = raw32765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2391 sourceB2391 sourceC2391 difference raw32765; decide +kernel
    rw [ha]
    exact (canonical32765 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2391 sourceB2391 sourceC2391
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2391, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2392 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2392 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2392 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceForm2392 : Integer.Sparse Master := [(Sum.inr 2655, 1), (Sum.inr 2657, 1), (Sum.inr 2659, 1), (Sum.inr 2681, 1), (Sum.inr 2735, 1), (Sum.inr 3259, 1), (Sum.inr 3266, 1), (Sum.inr 3271, 1), (Sum.inr 3305, 1), (Sum.inr 3458, 1), (Sum.inr 3468, 1), (Sum.inr 3475, 1), (Sum.inr 3514, 1), (Sum.inr 3522, 1), (Sum.inr 3530, 1), (Sum.inr 3547, 1), (Sum.inr 3553, 1), (Sum.inr 3555, 1), (Sum.inr 3556, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3564, 1), (Sum.inr 3565, 1), (Sum.inr 3582, 1), (Sum.inr 3583, 1), (Sum.inr 3799, 1), (Sum.inr 3807, 1), (Sum.inr 3811, 1), (Sum.inr 3850, 1), (Sum.inr 3876, 1)]

theorem sourceEq2392 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2392 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2392 + difference 0 1) (sourceB2392 + difference 1 0) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA2392 + difference 0 1) (sourceB2392 + difference 1 0) sourceC2392) = raw32766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32766; decide +kernel
    rw [ha]
    exact (canonical32766 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2392 + difference 0 2) (sourceB2392 + difference 2 0) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA2392 + difference 0 2) (sourceB2392 + difference 2 0) sourceC2392) = raw32767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32767; decide +kernel
    rw [ha]
    exact (canonical32767 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2392 + difference 0 3) (sourceB2392 + difference 3 0) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA2392 + difference 0 3) (sourceB2392 + difference 3 0) sourceC2392) = raw32768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32768; decide +kernel
    rw [ha]
    exact (canonical32768 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2392 + difference 0 4) (sourceB2392 + difference 4 0) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2392 + difference 0 4) (sourceB2392 + difference 4 0) sourceC2392) = raw32769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32769; decide +kernel
    rw [ha]
    exact (canonical32769 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2392 + difference 0 5) (sourceB2392 + difference 5 0) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA2392 + difference 0 5) (sourceB2392 + difference 5 0) sourceC2392) = raw32770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32770; decide +kernel
    rw [ha]
    exact (canonical32770 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2392 + difference 1 0) (sourceB2392 + difference 0 1) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA2392 + difference 1 0) (sourceB2392 + difference 0 1) sourceC2392) = raw32771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32771; decide +kernel
    rw [ha]
    exact (canonical32771 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2392 + difference 1 2) (sourceB2392 + difference 2 1) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2392 + difference 1 2) (sourceB2392 + difference 2 1) sourceC2392) = raw24365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24365; decide +kernel
    rw [ha]
    exact (canonical24365 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2392 + difference 1 3) (sourceB2392 + difference 3 1) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA2392 + difference 1 3) (sourceB2392 + difference 3 1) sourceC2392) = raw24366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24366; decide +kernel
    rw [ha]
    exact (canonical24366 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2392 + difference 1 4) (sourceB2392 + difference 4 1) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA2392 + difference 1 4) (sourceB2392 + difference 4 1) sourceC2392) = raw24367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24367; decide +kernel
    rw [ha]
    exact (canonical24367 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2392 + difference 1 5) (sourceB2392 + difference 5 1) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA2392 + difference 1 5) (sourceB2392 + difference 5 1) sourceC2392) = raw24368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24368; decide +kernel
    rw [ha]
    exact (canonical24368 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2392 + difference 2 0) (sourceB2392 + difference 0 2) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3259) := by
    have ha : (tripleCharges (sourceA2392 + difference 2 0) (sourceB2392 + difference 0 2) sourceC2392) = raw24375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24375; decide +kernel
    rw [ha]
    exact (canonical24375 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2392 + difference 2 1) (sourceB2392 + difference 1 2) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3553) := by
    have ha : (tripleCharges (sourceA2392 + difference 2 1) (sourceB2392 + difference 1 2) sourceC2392) = raw32772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32772; decide +kernel
    rw [ha]
    exact (canonical32772 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2392 + difference 2 3) (sourceB2392 + difference 3 2) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA2392 + difference 2 3) (sourceB2392 + difference 3 2) sourceC2392) = raw32773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32773; decide +kernel
    rw [ha]
    exact (canonical32773 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2392 + difference 2 4) (sourceB2392 + difference 4 2) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA2392 + difference 2 4) (sourceB2392 + difference 4 2) sourceC2392) = raw32774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32774; decide +kernel
    rw [ha]
    exact (canonical32774 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2392 + difference 2 5) (sourceB2392 + difference 5 2) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA2392 + difference 2 5) (sourceB2392 + difference 5 2) sourceC2392) = raw32775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32775; decide +kernel
    rw [ha]
    exact (canonical32775 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2392 + difference 3 0) (sourceB2392 + difference 0 3) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3271) := by
    have ha : (tripleCharges (sourceA2392 + difference 3 0) (sourceB2392 + difference 0 3) sourceC2392) = raw24380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24380; decide +kernel
    rw [ha]
    exact (canonical24380 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2392 + difference 3 1) (sourceB2392 + difference 1 3) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3555) := by
    have ha : (tripleCharges (sourceA2392 + difference 3 1) (sourceB2392 + difference 1 3) sourceC2392) = raw32776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32776; decide +kernel
    rw [ha]
    exact (canonical32776 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2392 + difference 3 2) (sourceB2392 + difference 2 3) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3556) := by
    have ha : (tripleCharges (sourceA2392 + difference 3 2) (sourceB2392 + difference 2 3) sourceC2392) = raw32777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32777; decide +kernel
    rw [ha]
    exact (canonical32777 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2392 + difference 3 4) (sourceB2392 + difference 4 3) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2392 + difference 3 4) (sourceB2392 + difference 4 3) sourceC2392) = raw32778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32778; decide +kernel
    rw [ha]
    exact (canonical32778 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2392 + difference 3 5) (sourceB2392 + difference 5 3) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA2392 + difference 3 5) (sourceB2392 + difference 5 3) sourceC2392) = raw32779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32779; decide +kernel
    rw [ha]
    exact (canonical32779 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2392 + difference 4 0) (sourceB2392 + difference 0 4) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA2392 + difference 4 0) (sourceB2392 + difference 0 4) sourceC2392) = raw24385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24385; decide +kernel
    rw [ha]
    exact (canonical24385 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2392 + difference 4 1) (sourceB2392 + difference 1 4) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2659) := by
    have ha : (tripleCharges (sourceA2392 + difference 4 1) (sourceB2392 + difference 1 4) sourceC2392) = raw32780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32780; decide +kernel
    rw [ha]
    exact (canonical32780 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2392 + difference 4 2) (sourceB2392 + difference 2 4) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2655) := by
    have ha : (tripleCharges (sourceA2392 + difference 4 2) (sourceB2392 + difference 2 4) sourceC2392) = raw32781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32781; decide +kernel
    rw [ha]
    exact (canonical32781 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2392 + difference 4 3) (sourceB2392 + difference 3 4) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA2392 + difference 4 3) (sourceB2392 + difference 3 4) sourceC2392) = raw32782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32782; decide +kernel
    rw [ha]
    exact (canonical32782 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2392 + difference 4 5) (sourceB2392 + difference 5 4) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA2392 + difference 4 5) (sourceB2392 + difference 5 4) sourceC2392) = raw32783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32783; decide +kernel
    rw [ha]
    exact (canonical32783 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2392 + difference 5 0) (sourceB2392 + difference 0 5) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA2392 + difference 5 0) (sourceB2392 + difference 0 5) sourceC2392) = raw24390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw24390; decide +kernel
    rw [ha]
    exact (canonical24390 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2392 + difference 5 1) (sourceB2392 + difference 1 5) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3475) := by
    have ha : (tripleCharges (sourceA2392 + difference 5 1) (sourceB2392 + difference 1 5) sourceC2392) = raw32784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32784; decide +kernel
    rw [ha]
    exact (canonical32784 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2392 + difference 5 2) (sourceB2392 + difference 2 5) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3458) := by
    have ha : (tripleCharges (sourceA2392 + difference 5 2) (sourceB2392 + difference 2 5) sourceC2392) = raw32785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32785; decide +kernel
    rw [ha]
    exact (canonical32785 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2392 + difference 5 3) (sourceB2392 + difference 3 5) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA2392 + difference 5 3) (sourceB2392 + difference 3 5) sourceC2392) = raw32786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32786; decide +kernel
    rw [ha]
    exact (canonical32786 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2392 + difference 5 4) (sourceB2392 + difference 4 5) sourceC2392) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA2392 + difference 5 4) (sourceB2392 + difference 4 5) sourceC2392) = raw32787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2392 sourceB2392 sourceC2392 difference raw32787; decide +kernel
    rw [ha]
    exact (canonical32787 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2392 sourceB2392 sourceC2392
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2392, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2393 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2393 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2393 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceForm2393 : Integer.Sparse Master := [(Sum.inr 2353, 1), (Sum.inr 2355, 1), (Sum.inr 2356, 1), (Sum.inr 2362, 1), (Sum.inr 2590, 1), (Sum.inr 3732, 1), (Sum.inr 4092, -1)]

theorem sourceEq2393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2393 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2393 + difference 0 1) (sourceB2393 + difference 1 0) sourceC2393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA2393 + difference 0 1) (sourceB2393 + difference 1 0) sourceC2393) = raw32788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2393 sourceB2393 sourceC2393 difference raw32788; decide +kernel
    rw [ha]
    exact (canonical32788 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2393 + difference 1 1) (sourceB2393 + difference 1 1) sourceC2393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2393 + difference 1 1) (sourceB2393 + difference 1 1) sourceC2393) = raw27816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2393 sourceB2393 sourceC2393 difference raw27816; decide +kernel
    rw [ha]
    exact (canonical27816 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2393 + difference 2 1) (sourceB2393 + difference 1 2) sourceC2393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2353) := by
    have ha : (tripleCharges (sourceA2393 + difference 2 1) (sourceB2393 + difference 1 2) sourceC2393) = raw32789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2393 sourceB2393 sourceC2393 difference raw32789; decide +kernel
    rw [ha]
    exact (canonical32789 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2393 + difference 3 1) (sourceB2393 + difference 1 3) sourceC2393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2356) := by
    have ha : (tripleCharges (sourceA2393 + difference 3 1) (sourceB2393 + difference 1 3) sourceC2393) = raw32790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2393 sourceB2393 sourceC2393 difference raw32790; decide +kernel
    rw [ha]
    exact (canonical32790 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2393 + difference 4 1) (sourceB2393 + difference 1 4) sourceC2393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2362) := by
    have ha : (tripleCharges (sourceA2393 + difference 4 1) (sourceB2393 + difference 1 4) sourceC2393) = raw29701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2393 sourceB2393 sourceC2393 difference raw29701; decide +kernel
    rw [ha]
    exact (canonical29701 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2393 + difference 5 1) (sourceB2393 + difference 1 5) sourceC2393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2355) := by
    have ha : (tripleCharges (sourceA2393 + difference 5 1) (sourceB2393 + difference 1 5) sourceC2393) = raw27812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2393 sourceB2393 sourceC2393 difference raw27812; decide +kernel
    rw [ha]
    exact (canonical27812 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2393 + sourceB2393) sourceC2393) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2393 + sourceB2393) sourceC2393) = raw24400 := by
      apply Matrix.ext; unfold doubleCharges sourceA2393 sourceB2393 sourceC2393 raw24400; decide +kernel
    rw [ha]
    exact (canonical24400 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2393 sourceB2393 sourceC2393
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2393, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2394 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2394 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC2394 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceForm2394 : Integer.Sparse Master := [(Sum.inr 4337, 1), (Sum.inr 4338, 1), (Sum.inr 4339, 1), (Sum.inr 4354, 1), (Sum.inr 4452, 1), (Sum.inr 4721, 1), (Sum.inr 4726, 1), (Sum.inr 4744, 1), (Sum.inr 4868, 1), (Sum.inr 4936, 1), (Sum.inr 4937, 1), (Sum.inr 4949, 1), (Sum.inr 5032, 1), (Sum.inr 5038, 1), (Sum.inr 5070, 1), (Sum.inr 5123, 1), (Sum.inr 5125, 1), (Sum.inr 5162, 1), (Sum.inr 5163, 2), (Sum.inr 5172, 1), (Sum.inr 5176, 1), (Sum.inr 5228, 1), (Sum.inr 5290, 1), (Sum.inr 5291, 1), (Sum.inr 5401, 1), (Sum.inr 5404, 1), (Sum.inr 5411, 1), (Sum.inr 5451, 1), (Sum.inr 5485, 1)]

theorem sourceEq2394 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2394 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2394 + difference 0 1) (sourceB2394 + difference 1 0) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2394 + difference 0 1) (sourceB2394 + difference 1 0) sourceC2394) = raw32791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32791; decide +kernel
    rw [ha]
    exact (canonical32791 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2394 + difference 0 2) (sourceB2394 + difference 2 0) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA2394 + difference 0 2) (sourceB2394 + difference 2 0) sourceC2394) = raw32792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32792; decide +kernel
    rw [ha]
    exact (canonical32792 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2394 + difference 0 3) (sourceB2394 + difference 3 0) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2394 + difference 0 3) (sourceB2394 + difference 3 0) sourceC2394) = raw9592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9592; decide +kernel
    rw [ha]
    exact (canonical9592 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2394 + difference 0 4) (sourceB2394 + difference 4 0) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA2394 + difference 0 4) (sourceB2394 + difference 4 0) sourceC2394) = raw32793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32793; decide +kernel
    rw [ha]
    exact (canonical32793 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2394 + difference 0 5) (sourceB2394 + difference 5 0) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2394 + difference 0 5) (sourceB2394 + difference 5 0) sourceC2394) = raw32794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32794; decide +kernel
    rw [ha]
    exact (canonical32794 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2394 + difference 1 0) (sourceB2394 + difference 0 1) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA2394 + difference 1 0) (sourceB2394 + difference 0 1) sourceC2394) = raw9607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9607; decide +kernel
    rw [ha]
    exact (canonical9607 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2394 + difference 1 2) (sourceB2394 + difference 2 1) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA2394 + difference 1 2) (sourceB2394 + difference 2 1) sourceC2394) = raw9609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9609; decide +kernel
    rw [ha]
    exact (canonical9609 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2394 + difference 1 3) (sourceB2394 + difference 3 1) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA2394 + difference 1 3) (sourceB2394 + difference 3 1) sourceC2394) = raw28619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw28619; decide +kernel
    rw [ha]
    exact (canonical28619 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2394 + difference 1 4) (sourceB2394 + difference 4 1) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2394 + difference 1 4) (sourceB2394 + difference 4 1) sourceC2394) = raw9610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9610; decide +kernel
    rw [ha]
    exact (canonical9610 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2394 + difference 1 5) (sourceB2394 + difference 5 1) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA2394 + difference 1 5) (sourceB2394 + difference 5 1) sourceC2394) = raw9611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9611; decide +kernel
    rw [ha]
    exact (canonical9611 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2394 + difference 2 0) (sourceB2394 + difference 0 2) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4337) := by
    have ha : (tripleCharges (sourceA2394 + difference 2 0) (sourceB2394 + difference 0 2) sourceC2394) = raw32795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32795; decide +kernel
    rw [ha]
    exact (canonical32795 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2394 + difference 2 1) (sourceB2394 + difference 1 2) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2394 + difference 2 1) (sourceB2394 + difference 1 2) sourceC2394) = raw32796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32796; decide +kernel
    rw [ha]
    exact (canonical32796 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2394 + difference 2 3) (sourceB2394 + difference 3 2) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2394 + difference 2 3) (sourceB2394 + difference 3 2) sourceC2394) = raw9603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9603; decide +kernel
    rw [ha]
    exact (canonical9603 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2394 + difference 2 4) (sourceB2394 + difference 4 2) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2394 + difference 2 4) (sourceB2394 + difference 4 2) sourceC2394) = raw32797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32797; decide +kernel
    rw [ha]
    exact (canonical32797 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2394 + difference 2 5) (sourceB2394 + difference 5 2) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA2394 + difference 2 5) (sourceB2394 + difference 5 2) sourceC2394) = raw32798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32798; decide +kernel
    rw [ha]
    exact (canonical32798 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2394 + difference 3 0) (sourceB2394 + difference 0 3) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4339) := by
    have ha : (tripleCharges (sourceA2394 + difference 3 0) (sourceB2394 + difference 0 3) sourceC2394) = raw32799 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32799; decide +kernel
    rw [ha]
    exact (canonical32799 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2394 + difference 3 1) (sourceB2394 + difference 1 3) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4937) := by
    have ha : (tripleCharges (sourceA2394 + difference 3 1) (sourceB2394 + difference 1 3) sourceC2394) = raw32800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32800; decide +kernel
    rw [ha]
    exact (canonical32800 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2394 + difference 3 2) (sourceB2394 + difference 2 3) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5032) := by
    have ha : (tripleCharges (sourceA2394 + difference 3 2) (sourceB2394 + difference 2 3) sourceC2394) = raw32801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32801; decide +kernel
    rw [ha]
    exact (canonical32801 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2394 + difference 3 4) (sourceB2394 + difference 4 3) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5125) := by
    have ha : (tripleCharges (sourceA2394 + difference 3 4) (sourceB2394 + difference 4 3) sourceC2394) = raw32802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32802; decide +kernel
    rw [ha]
    exact (canonical32802 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2394 + difference 3 5) (sourceB2394 + difference 5 3) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2394 + difference 3 5) (sourceB2394 + difference 5 3) sourceC2394) = raw32803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw32803; decide +kernel
    rw [ha]
    exact (canonical32803 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2394 + difference 4 0) (sourceB2394 + difference 0 4) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA2394 + difference 4 0) (sourceB2394 + difference 0 4) sourceC2394) = raw29536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw29536; decide +kernel
    rw [ha]
    exact (canonical29536 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2394 + difference 4 1) (sourceB2394 + difference 1 4) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2394 + difference 4 1) (sourceB2394 + difference 1 4) sourceC2394) = raw29537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw29537; decide +kernel
    rw [ha]
    exact (canonical29537 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2394 + difference 4 2) (sourceB2394 + difference 2 4) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5038) := by
    have ha : (tripleCharges (sourceA2394 + difference 4 2) (sourceB2394 + difference 2 4) sourceC2394) = raw29538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw29538; decide +kernel
    rw [ha]
    exact (canonical29538 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2394 + difference 4 3) (sourceB2394 + difference 3 4) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2394 + difference 4 3) (sourceB2394 + difference 3 4) sourceC2394) = raw9613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9613; decide +kernel
    rw [ha]
    exact (canonical9613 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2394 + difference 4 5) (sourceB2394 + difference 5 4) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2394 + difference 4 5) (sourceB2394 + difference 5 4) sourceC2394) = raw29539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw29539; decide +kernel
    rw [ha]
    exact (canonical29539 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2394 + difference 5 0) (sourceB2394 + difference 0 5) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4338) := by
    have ha : (tripleCharges (sourceA2394 + difference 5 0) (sourceB2394 + difference 0 5) sourceC2394) = raw28624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw28624; decide +kernel
    rw [ha]
    exact (canonical28624 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2394 + difference 5 1) (sourceB2394 + difference 1 5) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4726) := by
    have ha : (tripleCharges (sourceA2394 + difference 5 1) (sourceB2394 + difference 1 5) sourceC2394) = raw28625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw28625; decide +kernel
    rw [ha]
    exact (canonical28625 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2394 + difference 5 2) (sourceB2394 + difference 2 5) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4721) := by
    have ha : (tripleCharges (sourceA2394 + difference 5 2) (sourceB2394 + difference 2 5) sourceC2394) = raw28626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw28626; decide +kernel
    rw [ha]
    exact (canonical28626 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2394 + difference 5 3) (sourceB2394 + difference 3 5) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2394 + difference 5 3) (sourceB2394 + difference 3 5) sourceC2394) = raw9618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw9618; decide +kernel
    rw [ha]
    exact (canonical9618 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2394 + difference 5 4) (sourceB2394 + difference 4 5) sourceC2394) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2394 + difference 5 4) (sourceB2394 + difference 4 5) sourceC2394) = raw28627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2394 sourceB2394 sourceC2394 difference raw28627; decide +kernel
    rw [ha]
    exact (canonical28627 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2394 sourceB2394 sourceC2394
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2394, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2395 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2395 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC2395 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceForm2395 : Integer.Sparse Master := [(Sum.inr 915, 1), (Sum.inr 916, 1), (Sum.inr 917, 1), (Sum.inr 932, 1), (Sum.inr 1035, 1), (Sum.inr 1875, 1), (Sum.inr 1880, 1), (Sum.inr 1924, 1), (Sum.inr 2109, 1), (Sum.inr 2328, 1), (Sum.inr 2329, 1), (Sum.inr 2341, 1), (Sum.inr 2424, 1), (Sum.inr 2431, 1), (Sum.inr 2477, 1), (Sum.inr 2536, 1), (Sum.inr 2539, 1), (Sum.inr 2589, 1), (Sum.inr 2590, 2), (Sum.inr 2599, 1), (Sum.inr 2604, 1), (Sum.inr 2672, 1), (Sum.inr 2764, 1), (Sum.inr 2765, 1), (Sum.inr 3787, 1), (Sum.inr 3790, 1), (Sum.inr 3813, 1), (Sum.inr 3888, 1), (Sum.inr 3998, 1)]

theorem sourceEq2395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2395 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2395 + difference 0 1) (sourceB2395 + difference 1 0) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3790) := by
    have ha : (tripleCharges (sourceA2395 + difference 0 1) (sourceB2395 + difference 1 0) sourceC2395) = raw32804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw32804; decide +kernel
    rw [ha]
    exact (canonical32804 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2395 + difference 0 2) (sourceB2395 + difference 2 0) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3787) := by
    have ha : (tripleCharges (sourceA2395 + difference 0 2) (sourceB2395 + difference 2 0) sourceC2395) = raw32805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw32805; decide +kernel
    rw [ha]
    exact (canonical32805 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2395 + difference 0 3) (sourceB2395 + difference 3 0) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA2395 + difference 0 3) (sourceB2395 + difference 3 0) sourceC2395) = raw9622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw9622; decide +kernel
    rw [ha]
    exact (canonical9622 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2395 + difference 0 4) (sourceB2395 + difference 4 0) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA2395 + difference 0 4) (sourceB2395 + difference 4 0) sourceC2395) = raw32806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw32806; decide +kernel
    rw [ha]
    exact (canonical32806 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2395 + difference 0 5) (sourceB2395 + difference 5 0) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA2395 + difference 0 5) (sourceB2395 + difference 5 0) sourceC2395) = raw32807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw32807; decide +kernel
    rw [ha]
    exact (canonical32807 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2395 + difference 1 0) (sourceB2395 + difference 0 1) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA2395 + difference 1 0) (sourceB2395 + difference 0 1) sourceC2395) = raw9637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw9637; decide +kernel
    rw [ha]
    exact (canonical9637 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2395 + difference 1 2) (sourceB2395 + difference 2 1) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA2395 + difference 1 2) (sourceB2395 + difference 2 1) sourceC2395) = raw9639 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw9639; decide +kernel
    rw [ha]
    exact (canonical9639 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2395 + difference 1 3) (sourceB2395 + difference 3 1) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA2395 + difference 1 3) (sourceB2395 + difference 3 1) sourceC2395) = raw28641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw28641; decide +kernel
    rw [ha]
    exact (canonical28641 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2395 + difference 1 4) (sourceB2395 + difference 4 1) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2395 + difference 1 4) (sourceB2395 + difference 4 1) sourceC2395) = raw9640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw9640; decide +kernel
    rw [ha]
    exact (canonical9640 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2395 + difference 1 5) (sourceB2395 + difference 5 1) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA2395 + difference 1 5) (sourceB2395 + difference 5 1) sourceC2395) = raw9641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw9641; decide +kernel
    rw [ha]
    exact (canonical9641 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2395 + difference 2 0) (sourceB2395 + difference 0 2) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 915) := by
    have ha : (tripleCharges (sourceA2395 + difference 2 0) (sourceB2395 + difference 0 2) sourceC2395) = raw32808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw32808; decide +kernel
    rw [ha]
    exact (canonical32808 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2395 + difference 2 1) (sourceB2395 + difference 1 2) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2328) := by
    have ha : (tripleCharges (sourceA2395 + difference 2 1) (sourceB2395 + difference 1 2) sourceC2395) = raw32809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw32809; decide +kernel
    rw [ha]
    exact (canonical32809 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2395 + difference 2 3) (sourceB2395 + difference 3 2) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2395 + difference 2 3) (sourceB2395 + difference 3 2) sourceC2395) = raw9633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw9633; decide +kernel
    rw [ha]
    exact (canonical9633 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2395 + difference 2 4) (sourceB2395 + difference 4 2) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2536) := by
    have ha : (tripleCharges (sourceA2395 + difference 2 4) (sourceB2395 + difference 4 2) sourceC2395) = raw32810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw32810; decide +kernel
    rw [ha]
    exact (canonical32810 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2395 + difference 2 5) (sourceB2395 + difference 5 2) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2589) := by
    have ha : (tripleCharges (sourceA2395 + difference 2 5) (sourceB2395 + difference 5 2) sourceC2395) = raw32811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw32811; decide +kernel
    rw [ha]
    exact (canonical32811 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2395 + difference 3 0) (sourceB2395 + difference 0 3) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 917) := by
    have ha : (tripleCharges (sourceA2395 + difference 3 0) (sourceB2395 + difference 0 3) sourceC2395) = raw32812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw32812; decide +kernel
    rw [ha]
    exact (canonical32812 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2395 + difference 3 1) (sourceB2395 + difference 1 3) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2329) := by
    have ha : (tripleCharges (sourceA2395 + difference 3 1) (sourceB2395 + difference 1 3) sourceC2395) = raw32813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw32813; decide +kernel
    rw [ha]
    exact (canonical32813 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2395 + difference 3 2) (sourceB2395 + difference 2 3) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2424) := by
    have ha : (tripleCharges (sourceA2395 + difference 3 2) (sourceB2395 + difference 2 3) sourceC2395) = raw32814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw32814; decide +kernel
    rw [ha]
    exact (canonical32814 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2395 + difference 3 4) (sourceB2395 + difference 4 3) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2539) := by
    have ha : (tripleCharges (sourceA2395 + difference 3 4) (sourceB2395 + difference 4 3) sourceC2395) = raw32815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw32815; decide +kernel
    rw [ha]
    exact (canonical32815 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2395 + difference 3 5) (sourceB2395 + difference 5 3) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2395 + difference 3 5) (sourceB2395 + difference 5 3) sourceC2395) = raw32816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw32816; decide +kernel
    rw [ha]
    exact (canonical32816 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2395 + difference 4 0) (sourceB2395 + difference 0 4) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 932) := by
    have ha : (tripleCharges (sourceA2395 + difference 4 0) (sourceB2395 + difference 0 4) sourceC2395) = raw29553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw29553; decide +kernel
    rw [ha]
    exact (canonical29553 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2395 + difference 4 1) (sourceB2395 + difference 1 4) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2341) := by
    have ha : (tripleCharges (sourceA2395 + difference 4 1) (sourceB2395 + difference 1 4) sourceC2395) = raw29554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw29554; decide +kernel
    rw [ha]
    exact (canonical29554 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2395 + difference 4 2) (sourceB2395 + difference 2 4) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2431) := by
    have ha : (tripleCharges (sourceA2395 + difference 4 2) (sourceB2395 + difference 2 4) sourceC2395) = raw29555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw29555; decide +kernel
    rw [ha]
    exact (canonical29555 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2395 + difference 4 3) (sourceB2395 + difference 3 4) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2604) := by
    have ha : (tripleCharges (sourceA2395 + difference 4 3) (sourceB2395 + difference 3 4) sourceC2395) = raw9643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw9643; decide +kernel
    rw [ha]
    exact (canonical9643 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2395 + difference 4 5) (sourceB2395 + difference 5 4) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2599) := by
    have ha : (tripleCharges (sourceA2395 + difference 4 5) (sourceB2395 + difference 5 4) sourceC2395) = raw29556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw29556; decide +kernel
    rw [ha]
    exact (canonical29556 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2395 + difference 5 0) (sourceB2395 + difference 0 5) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 916) := by
    have ha : (tripleCharges (sourceA2395 + difference 5 0) (sourceB2395 + difference 0 5) sourceC2395) = raw28646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw28646; decide +kernel
    rw [ha]
    exact (canonical28646 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2395 + difference 5 1) (sourceB2395 + difference 1 5) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1880) := by
    have ha : (tripleCharges (sourceA2395 + difference 5 1) (sourceB2395 + difference 1 5) sourceC2395) = raw28647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw28647; decide +kernel
    rw [ha]
    exact (canonical28647 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2395 + difference 5 2) (sourceB2395 + difference 2 5) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1875) := by
    have ha : (tripleCharges (sourceA2395 + difference 5 2) (sourceB2395 + difference 2 5) sourceC2395) = raw28648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw28648; decide +kernel
    rw [ha]
    exact (canonical28648 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2395 + difference 5 3) (sourceB2395 + difference 3 5) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA2395 + difference 5 3) (sourceB2395 + difference 3 5) sourceC2395) = raw9648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw9648; decide +kernel
    rw [ha]
    exact (canonical9648 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2395 + difference 5 4) (sourceB2395 + difference 4 5) sourceC2395) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA2395 + difference 5 4) (sourceB2395 + difference 4 5) sourceC2395) = raw28649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2395 sourceB2395 sourceC2395 difference raw28649; decide +kernel
    rw [ha]
    exact (canonical28649 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2395 sourceB2395 sourceC2395
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2395, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2396 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB2396 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC2396 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2396 : Integer.Sparse Master := [(Sum.inr 4798, 1), (Sum.inr 4827, 1), (Sum.inr 4828, 1), (Sum.inr 4834, 1), (Sum.inr 4860, 1), (Sum.inr 5069, 1), (Sum.inr 5070, 1), (Sum.inr 5074, 1), (Sum.inr 5079, 1), (Sum.inr 5094, 1), (Sum.inr 5095, 1), (Sum.inr 5101, 1), (Sum.inr 5102, 1), (Sum.inr 5103, 1), (Sum.inr 5105, 1), (Sum.inr 5132, 1), (Sum.inr 5134, 1), (Sum.inr 5143, 1), (Sum.inr 5144, 1), (Sum.inr 5145, 1), (Sum.inr 5158, 1), (Sum.inr 5161, 1), (Sum.inr 5164, 1), (Sum.inr 5168, 1), (Sum.inr 5169, 1), (Sum.inr 5170, 1), (Sum.inr 5183, 1), (Sum.inr 5195, 1), (Sum.inr 5198, 1), (Sum.inr 5199, 1)]

theorem sourceEq2396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2396 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2396 + difference 0 1) (sourceB2396 + difference 1 0) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2396 + difference 0 1) (sourceB2396 + difference 1 0) sourceC2396) = raw32817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32817; decide +kernel
    rw [ha]
    exact (canonical32817 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2396 + difference 0 2) (sourceB2396 + difference 2 0) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA2396 + difference 0 2) (sourceB2396 + difference 2 0) sourceC2396) = raw32818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32818; decide +kernel
    rw [ha]
    exact (canonical32818 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2396 + difference 0 3) (sourceB2396 + difference 3 0) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2396 + difference 0 3) (sourceB2396 + difference 3 0) sourceC2396) = raw32819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32819; decide +kernel
    rw [ha]
    exact (canonical32819 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2396 + difference 0 4) (sourceB2396 + difference 4 0) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA2396 + difference 0 4) (sourceB2396 + difference 4 0) sourceC2396) = raw32820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32820; decide +kernel
    rw [ha]
    exact (canonical32820 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2396 + difference 0 5) (sourceB2396 + difference 5 0) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2396 + difference 0 5) (sourceB2396 + difference 5 0) sourceC2396) = raw32821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32821; decide +kernel
    rw [ha]
    exact (canonical32821 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2396 + difference 1 0) (sourceB2396 + difference 0 1) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2396 + difference 1 0) (sourceB2396 + difference 0 1) sourceC2396) = raw32822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32822; decide +kernel
    rw [ha]
    exact (canonical32822 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2396 + difference 1 2) (sourceB2396 + difference 2 1) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5183) := by
    have ha : (tripleCharges (sourceA2396 + difference 1 2) (sourceB2396 + difference 2 1) sourceC2396) = raw32823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32823; decide +kernel
    rw [ha]
    exact (canonical32823 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2396 + difference 1 3) (sourceB2396 + difference 3 1) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA2396 + difference 1 3) (sourceB2396 + difference 3 1) sourceC2396) = raw32824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32824; decide +kernel
    rw [ha]
    exact (canonical32824 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2396 + difference 1 4) (sourceB2396 + difference 4 1) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5195) := by
    have ha : (tripleCharges (sourceA2396 + difference 1 4) (sourceB2396 + difference 4 1) sourceC2396) = raw32825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32825; decide +kernel
    rw [ha]
    exact (canonical32825 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2396 + difference 1 5) (sourceB2396 + difference 5 1) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA2396 + difference 1 5) (sourceB2396 + difference 5 1) sourceC2396) = raw32826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32826; decide +kernel
    rw [ha]
    exact (canonical32826 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2396 + difference 2 0) (sourceB2396 + difference 0 2) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2396 + difference 2 0) (sourceB2396 + difference 0 2) sourceC2396) = raw32827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32827; decide +kernel
    rw [ha]
    exact (canonical32827 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2396 + difference 2 1) (sourceB2396 + difference 1 2) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA2396 + difference 2 1) (sourceB2396 + difference 1 2) sourceC2396) = raw32828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32828; decide +kernel
    rw [ha]
    exact (canonical32828 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2396 + difference 2 3) (sourceB2396 + difference 3 2) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA2396 + difference 2 3) (sourceB2396 + difference 3 2) sourceC2396) = raw32337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32337; decide +kernel
    rw [ha]
    exact (canonical32337 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2396 + difference 2 4) (sourceB2396 + difference 4 2) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5143) := by
    have ha : (tripleCharges (sourceA2396 + difference 2 4) (sourceB2396 + difference 4 2) sourceC2396) = raw32829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32829; decide +kernel
    rw [ha]
    exact (canonical32829 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2396 + difference 2 5) (sourceB2396 + difference 5 2) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA2396 + difference 2 5) (sourceB2396 + difference 5 2) sourceC2396) = raw32329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32329; decide +kernel
    rw [ha]
    exact (canonical32329 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2396 + difference 3 0) (sourceB2396 + difference 0 3) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2396 + difference 3 0) (sourceB2396 + difference 0 3) sourceC2396) = raw32830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32830; decide +kernel
    rw [ha]
    exact (canonical32830 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2396 + difference 3 1) (sourceB2396 + difference 1 3) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA2396 + difference 3 1) (sourceB2396 + difference 1 3) sourceC2396) = raw32831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32831; decide +kernel
    rw [ha]
    exact (canonical32831 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2396 + difference 3 2) (sourceB2396 + difference 2 3) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5132) := by
    have ha : (tripleCharges (sourceA2396 + difference 3 2) (sourceB2396 + difference 2 3) sourceC2396) = raw32832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32832; decide +kernel
    rw [ha]
    exact (canonical32832 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2396 + difference 3 4) (sourceB2396 + difference 4 3) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5158) := by
    have ha : (tripleCharges (sourceA2396 + difference 3 4) (sourceB2396 + difference 4 3) sourceC2396) = raw32833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32833; decide +kernel
    rw [ha]
    exact (canonical32833 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2396 + difference 3 5) (sourceB2396 + difference 5 3) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA2396 + difference 3 5) (sourceB2396 + difference 5 3) sourceC2396) = raw32834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32834; decide +kernel
    rw [ha]
    exact (canonical32834 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2396 + difference 4 0) (sourceB2396 + difference 0 4) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2396 + difference 4 0) (sourceB2396 + difference 0 4) sourceC2396) = raw32835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32835; decide +kernel
    rw [ha]
    exact (canonical32835 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2396 + difference 4 1) (sourceB2396 + difference 1 4) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2396 + difference 4 1) (sourceB2396 + difference 1 4) sourceC2396) = raw32836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32836; decide +kernel
    rw [ha]
    exact (canonical32836 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2396 + difference 4 2) (sourceB2396 + difference 2 4) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2396 + difference 4 2) (sourceB2396 + difference 2 4) sourceC2396) = raw32837 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32837; decide +kernel
    rw [ha]
    exact (canonical32837 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2396 + difference 4 3) (sourceB2396 + difference 3 4) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2396 + difference 4 3) (sourceB2396 + difference 3 4) sourceC2396) = raw32335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32335; decide +kernel
    rw [ha]
    exact (canonical32335 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2396 + difference 4 5) (sourceB2396 + difference 5 4) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2396 + difference 4 5) (sourceB2396 + difference 5 4) sourceC2396) = raw32254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32254; decide +kernel
    rw [ha]
    exact (canonical32254 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2396 + difference 5 0) (sourceB2396 + difference 0 5) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA2396 + difference 5 0) (sourceB2396 + difference 0 5) sourceC2396) = raw32838 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32838; decide +kernel
    rw [ha]
    exact (canonical32838 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2396 + difference 5 1) (sourceB2396 + difference 1 5) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5094) := by
    have ha : (tripleCharges (sourceA2396 + difference 5 1) (sourceB2396 + difference 1 5) sourceC2396) = raw32839 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32839; decide +kernel
    rw [ha]
    exact (canonical32839 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2396 + difference 5 2) (sourceB2396 + difference 2 5) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5069) := by
    have ha : (tripleCharges (sourceA2396 + difference 5 2) (sourceB2396 + difference 2 5) sourceC2396) = raw32840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32840; decide +kernel
    rw [ha]
    exact (canonical32840 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2396 + difference 5 3) (sourceB2396 + difference 3 5) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA2396 + difference 5 3) (sourceB2396 + difference 3 5) sourceC2396) = raw32841 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32841; decide +kernel
    rw [ha]
    exact (canonical32841 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2396 + difference 5 4) (sourceB2396 + difference 4 5) sourceC2396) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5079) := by
    have ha : (tripleCharges (sourceA2396 + difference 5 4) (sourceB2396 + difference 4 5) sourceC2396) = raw32842 := by
      apply Matrix.ext; unfold tripleCharges sourceA2396 sourceB2396 sourceC2396 difference raw32842; decide +kernel
    rw [ha]
    exact (canonical32842 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2396 sourceB2396 sourceC2396
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2396, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2397 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2397 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC2397 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceForm2397 : Integer.Sparse Master := [(Sum.inr 4527, 1), (Sum.inr 4530, 2), (Sum.inr 4542, 1), (Sum.inr 4606, 1), (Sum.inr 4956, 1), (Sum.inr 4958, 2), (Sum.inr 4964, 1), (Sum.inr 5037, 1), (Sum.inr 5039, 2), (Sum.inr 5104, 1), (Sum.inr 5128, 2), (Sum.inr 5130, 2), (Sum.inr 5137, 2), (Sum.inr 5145, 2), (Sum.inr 5162, 1), (Sum.inr 5259, 2), (Sum.inr 5273, 1), (Sum.inr 5380, 1), (Sum.inr 5396, 1), (Sum.inr 5424, 2), (Sum.inr 5427, 1)]

theorem sourceEq2397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2397 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2397 + difference 0 1) (sourceB2397 + difference 1 0) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2397 + difference 0 1) (sourceB2397 + difference 1 0) sourceC2397) = raw19356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw19356; decide +kernel
    rw [ha]
    exact (canonical19356 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2397 + difference 0 2) (sourceB2397 + difference 2 0) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA2397 + difference 0 2) (sourceB2397 + difference 2 0) sourceC2397) = raw19357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw19357; decide +kernel
    rw [ha]
    exact (canonical19357 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2397 + difference 0 3) (sourceB2397 + difference 3 0) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2397 + difference 0 3) (sourceB2397 + difference 3 0) sourceC2397) = raw19358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw19358; decide +kernel
    rw [ha]
    exact (canonical19358 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2397 + difference 0 4) (sourceB2397 + difference 4 0) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2397 + difference 0 4) (sourceB2397 + difference 4 0) sourceC2397) = raw19359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw19359; decide +kernel
    rw [ha]
    exact (canonical19359 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2397 + difference 0 5) (sourceB2397 + difference 5 0) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5427) := by
    have ha : (tripleCharges (sourceA2397 + difference 0 5) (sourceB2397 + difference 5 0) sourceC2397) = raw14221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw14221; decide +kernel
    rw [ha]
    exact (canonical14221 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2397 + difference 1 0) (sourceB2397 + difference 0 1) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA2397 + difference 1 0) (sourceB2397 + difference 0 1) sourceC2397) = raw14246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw14246; decide +kernel
    rw [ha]
    exact (canonical14246 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2397 + difference 1 2) (sourceB2397 + difference 2 1) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2397 + difference 1 2) (sourceB2397 + difference 2 1) sourceC2397) = raw14248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw14248; decide +kernel
    rw [ha]
    exact (canonical14248 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2397 + difference 1 3) (sourceB2397 + difference 3 1) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2397 + difference 1 3) (sourceB2397 + difference 3 1) sourceC2397) = raw14249 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw14249; decide +kernel
    rw [ha]
    exact (canonical14249 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2397 + difference 1 4) (sourceB2397 + difference 4 1) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2397 + difference 1 4) (sourceB2397 + difference 4 1) sourceC2397) = raw14250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw14250; decide +kernel
    rw [ha]
    exact (canonical14250 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2397 + difference 1 5) (sourceB2397 + difference 5 1) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA2397 + difference 1 5) (sourceB2397 + difference 5 1) sourceC2397) = raw19343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw19343; decide +kernel
    rw [ha]
    exact (canonical19343 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2397 + difference 2 0) (sourceB2397 + difference 0 2) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4542) := by
    have ha : (tripleCharges (sourceA2397 + difference 2 0) (sourceB2397 + difference 0 2) sourceC2397) = raw24470 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw24470; decide +kernel
    rw [ha]
    exact (canonical24470 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2397 + difference 2 1) (sourceB2397 + difference 1 2) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4964) := by
    have ha : (tripleCharges (sourceA2397 + difference 2 1) (sourceB2397 + difference 1 2) sourceC2397) = raw32843 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw32843; decide +kernel
    rw [ha]
    exact (canonical32843 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2397 + difference 2 3) (sourceB2397 + difference 3 2) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA2397 + difference 2 3) (sourceB2397 + difference 3 2) sourceC2397) = raw32844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw32844; decide +kernel
    rw [ha]
    exact (canonical32844 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2397 + difference 2 4) (sourceB2397 + difference 4 2) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA2397 + difference 2 4) (sourceB2397 + difference 4 2) sourceC2397) = raw32845 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw32845; decide +kernel
    rw [ha]
    exact (canonical32845 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2397 + difference 2 5) (sourceB2397 + difference 5 2) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA2397 + difference 2 5) (sourceB2397 + difference 5 2) sourceC2397) = raw14232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw14232; decide +kernel
    rw [ha]
    exact (canonical14232 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2397 + difference 3 0) (sourceB2397 + difference 0 3) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4530) := by
    have ha : (tripleCharges (sourceA2397 + difference 3 0) (sourceB2397 + difference 0 3) sourceC2397) = raw24474 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw24474; decide +kernel
    rw [ha]
    exact (canonical24474 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2397 + difference 3 1) (sourceB2397 + difference 1 3) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4958) := by
    have ha : (tripleCharges (sourceA2397 + difference 3 1) (sourceB2397 + difference 1 3) sourceC2397) = raw32846 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw32846; decide +kernel
    rw [ha]
    exact (canonical32846 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2397 + difference 3 2) (sourceB2397 + difference 2 3) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5039) := by
    have ha : (tripleCharges (sourceA2397 + difference 3 2) (sourceB2397 + difference 2 3) sourceC2397) = raw32847 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw32847; decide +kernel
    rw [ha]
    exact (canonical32847 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2397 + difference 3 4) (sourceB2397 + difference 4 3) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA2397 + difference 3 4) (sourceB2397 + difference 4 3) sourceC2397) = raw32848 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw32848; decide +kernel
    rw [ha]
    exact (canonical32848 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2397 + difference 3 5) (sourceB2397 + difference 5 3) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2397 + difference 3 5) (sourceB2397 + difference 5 3) sourceC2397) = raw14237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw14237; decide +kernel
    rw [ha]
    exact (canonical14237 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2397 + difference 4 0) (sourceB2397 + difference 0 4) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4530) := by
    have ha : (tripleCharges (sourceA2397 + difference 4 0) (sourceB2397 + difference 0 4) sourceC2397) = raw24478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw24478; decide +kernel
    rw [ha]
    exact (canonical24478 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2397 + difference 4 1) (sourceB2397 + difference 1 4) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4958) := by
    have ha : (tripleCharges (sourceA2397 + difference 4 1) (sourceB2397 + difference 1 4) sourceC2397) = raw32849 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw32849; decide +kernel
    rw [ha]
    exact (canonical32849 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2397 + difference 4 2) (sourceB2397 + difference 2 4) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5039) := by
    have ha : (tripleCharges (sourceA2397 + difference 4 2) (sourceB2397 + difference 2 4) sourceC2397) = raw32850 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw32850; decide +kernel
    rw [ha]
    exact (canonical32850 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2397 + difference 4 3) (sourceB2397 + difference 3 4) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA2397 + difference 4 3) (sourceB2397 + difference 3 4) sourceC2397) = raw32851 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw32851; decide +kernel
    rw [ha]
    exact (canonical32851 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2397 + difference 4 5) (sourceB2397 + difference 5 4) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2397 + difference 4 5) (sourceB2397 + difference 5 4) sourceC2397) = raw14242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw14242; decide +kernel
    rw [ha]
    exact (canonical14242 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2397 + difference 5 0) (sourceB2397 + difference 0 5) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4527) := by
    have ha : (tripleCharges (sourceA2397 + difference 5 0) (sourceB2397 + difference 0 5) sourceC2397) = raw24482 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw24482; decide +kernel
    rw [ha]
    exact (canonical24482 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2397 + difference 5 1) (sourceB2397 + difference 1 5) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4956) := by
    have ha : (tripleCharges (sourceA2397 + difference 5 1) (sourceB2397 + difference 1 5) sourceC2397) = raw32852 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw32852; decide +kernel
    rw [ha]
    exact (canonical32852 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2397 + difference 5 2) (sourceB2397 + difference 2 5) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5037) := by
    have ha : (tripleCharges (sourceA2397 + difference 5 2) (sourceB2397 + difference 2 5) sourceC2397) = raw32853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw32853; decide +kernel
    rw [ha]
    exact (canonical32853 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2397 + difference 5 3) (sourceB2397 + difference 3 5) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA2397 + difference 5 3) (sourceB2397 + difference 3 5) sourceC2397) = raw32854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw32854; decide +kernel
    rw [ha]
    exact (canonical32854 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2397 + difference 5 4) (sourceB2397 + difference 4 5) sourceC2397) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA2397 + difference 5 4) (sourceB2397 + difference 4 5) sourceC2397) = raw32855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2397 sourceB2397 sourceC2397 difference raw32855; decide +kernel
    rw [ha]
    exact (canonical32855 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2397 sourceB2397 sourceC2397
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2397, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2398 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2398 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC2398 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceForm2398 : Integer.Sparse Master := [(Sum.inr 3255, 1), (Sum.inr 3257, 1), (Sum.inr 3261, 2), (Sum.inr 3299, 1), (Sum.inr 3455, 1), (Sum.inr 3456, 2), (Sum.inr 3483, 1), (Sum.inr 3510, 1), (Sum.inr 3511, 2), (Sum.inr 3519, 2), (Sum.inr 3520, 2), (Sum.inr 3521, 2), (Sum.inr 3544, 2), (Sum.inr 3546, 1), (Sum.inr 3554, 1), (Sum.inr 3562, 2), (Sum.inr 3563, 1), (Sum.inr 3798, 1), (Sum.inr 3836, 1), (Sum.inr 3843, 2), (Sum.inr 3844, 1)]

theorem sourceEq2398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2398 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2398 + difference 0 1) (sourceB2398 + difference 1 0) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3836) := by
    have ha : (tripleCharges (sourceA2398 + difference 0 1) (sourceB2398 + difference 1 0) sourceC2398) = raw32856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32856; decide +kernel
    rw [ha]
    exact (canonical32856 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2398 + difference 0 2) (sourceB2398 + difference 2 0) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3798) := by
    have ha : (tripleCharges (sourceA2398 + difference 0 2) (sourceB2398 + difference 2 0) sourceC2398) = raw32857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32857; decide +kernel
    rw [ha]
    exact (canonical32857 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2398 + difference 0 3) (sourceB2398 + difference 3 0) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA2398 + difference 0 3) (sourceB2398 + difference 3 0) sourceC2398) = raw32858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32858; decide +kernel
    rw [ha]
    exact (canonical32858 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2398 + difference 0 4) (sourceB2398 + difference 4 0) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA2398 + difference 0 4) (sourceB2398 + difference 4 0) sourceC2398) = raw32859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32859; decide +kernel
    rw [ha]
    exact (canonical32859 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2398 + difference 0 5) (sourceB2398 + difference 5 0) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3844) := by
    have ha : (tripleCharges (sourceA2398 + difference 0 5) (sourceB2398 + difference 5 0) sourceC2398) = raw32860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32860; decide +kernel
    rw [ha]
    exact (canonical32860 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2398 + difference 1 0) (sourceB2398 + difference 0 1) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA2398 + difference 1 0) (sourceB2398 + difference 0 1) sourceC2398) = raw32861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32861; decide +kernel
    rw [ha]
    exact (canonical32861 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2398 + difference 1 2) (sourceB2398 + difference 2 1) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3483) := by
    have ha : (tripleCharges (sourceA2398 + difference 1 2) (sourceB2398 + difference 2 1) sourceC2398) = raw24517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24517; decide +kernel
    rw [ha]
    exact (canonical24517 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2398 + difference 1 3) (sourceB2398 + difference 3 1) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA2398 + difference 1 3) (sourceB2398 + difference 3 1) sourceC2398) = raw24518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24518; decide +kernel
    rw [ha]
    exact (canonical24518 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2398 + difference 1 4) (sourceB2398 + difference 4 1) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA2398 + difference 1 4) (sourceB2398 + difference 4 1) sourceC2398) = raw24519 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24519; decide +kernel
    rw [ha]
    exact (canonical24519 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2398 + difference 1 5) (sourceB2398 + difference 5 1) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA2398 + difference 1 5) (sourceB2398 + difference 5 1) sourceC2398) = raw24520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24520; decide +kernel
    rw [ha]
    exact (canonical24520 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2398 + difference 2 0) (sourceB2398 + difference 0 2) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3257) := by
    have ha : (tripleCharges (sourceA2398 + difference 2 0) (sourceB2398 + difference 0 2) sourceC2398) = raw24527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24527; decide +kernel
    rw [ha]
    exact (canonical24527 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2398 + difference 2 1) (sourceB2398 + difference 1 2) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3554) := by
    have ha : (tripleCharges (sourceA2398 + difference 2 1) (sourceB2398 + difference 1 2) sourceC2398) = raw32862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32862; decide +kernel
    rw [ha]
    exact (canonical32862 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2398 + difference 2 3) (sourceB2398 + difference 3 2) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA2398 + difference 2 3) (sourceB2398 + difference 3 2) sourceC2398) = raw32863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32863; decide +kernel
    rw [ha]
    exact (canonical32863 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2398 + difference 2 4) (sourceB2398 + difference 4 2) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA2398 + difference 2 4) (sourceB2398 + difference 4 2) sourceC2398) = raw32864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32864; decide +kernel
    rw [ha]
    exact (canonical32864 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2398 + difference 2 5) (sourceB2398 + difference 5 2) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3563) := by
    have ha : (tripleCharges (sourceA2398 + difference 2 5) (sourceB2398 + difference 5 2) sourceC2398) = raw32865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32865; decide +kernel
    rw [ha]
    exact (canonical32865 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2398 + difference 3 0) (sourceB2398 + difference 0 3) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3261) := by
    have ha : (tripleCharges (sourceA2398 + difference 3 0) (sourceB2398 + difference 0 3) sourceC2398) = raw24532 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24532; decide +kernel
    rw [ha]
    exact (canonical24532 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2398 + difference 3 1) (sourceB2398 + difference 1 3) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3511) := by
    have ha : (tripleCharges (sourceA2398 + difference 3 1) (sourceB2398 + difference 1 3) sourceC2398) = raw32866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32866; decide +kernel
    rw [ha]
    exact (canonical32866 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2398 + difference 3 2) (sourceB2398 + difference 2 3) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3456) := by
    have ha : (tripleCharges (sourceA2398 + difference 3 2) (sourceB2398 + difference 2 3) sourceC2398) = raw32867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32867; decide +kernel
    rw [ha]
    exact (canonical32867 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2398 + difference 3 4) (sourceB2398 + difference 4 3) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2398 + difference 3 4) (sourceB2398 + difference 4 3) sourceC2398) = raw32868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32868; decide +kernel
    rw [ha]
    exact (canonical32868 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2398 + difference 3 5) (sourceB2398 + difference 5 3) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3521) := by
    have ha : (tripleCharges (sourceA2398 + difference 3 5) (sourceB2398 + difference 5 3) sourceC2398) = raw32869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32869; decide +kernel
    rw [ha]
    exact (canonical32869 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2398 + difference 4 0) (sourceB2398 + difference 0 4) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3261) := by
    have ha : (tripleCharges (sourceA2398 + difference 4 0) (sourceB2398 + difference 0 4) sourceC2398) = raw24537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24537; decide +kernel
    rw [ha]
    exact (canonical24537 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2398 + difference 4 1) (sourceB2398 + difference 1 4) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3511) := by
    have ha : (tripleCharges (sourceA2398 + difference 4 1) (sourceB2398 + difference 1 4) sourceC2398) = raw32870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32870; decide +kernel
    rw [ha]
    exact (canonical32870 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2398 + difference 4 2) (sourceB2398 + difference 2 4) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3456) := by
    have ha : (tripleCharges (sourceA2398 + difference 4 2) (sourceB2398 + difference 2 4) sourceC2398) = raw32871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32871; decide +kernel
    rw [ha]
    exact (canonical32871 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2398 + difference 4 3) (sourceB2398 + difference 3 4) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2398 + difference 4 3) (sourceB2398 + difference 3 4) sourceC2398) = raw32872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32872; decide +kernel
    rw [ha]
    exact (canonical32872 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2398 + difference 4 5) (sourceB2398 + difference 5 4) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3521) := by
    have ha : (tripleCharges (sourceA2398 + difference 4 5) (sourceB2398 + difference 5 4) sourceC2398) = raw32873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32873; decide +kernel
    rw [ha]
    exact (canonical32873 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2398 + difference 5 0) (sourceB2398 + difference 0 5) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3255) := by
    have ha : (tripleCharges (sourceA2398 + difference 5 0) (sourceB2398 + difference 0 5) sourceC2398) = raw24542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24542; decide +kernel
    rw [ha]
    exact (canonical24542 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2398 + difference 5 1) (sourceB2398 + difference 1 5) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3510) := by
    have ha : (tripleCharges (sourceA2398 + difference 5 1) (sourceB2398 + difference 1 5) sourceC2398) = raw32874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32874; decide +kernel
    rw [ha]
    exact (canonical32874 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2398 + difference 5 2) (sourceB2398 + difference 2 5) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3455) := by
    have ha : (tripleCharges (sourceA2398 + difference 5 2) (sourceB2398 + difference 2 5) sourceC2398) = raw32875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32875; decide +kernel
    rw [ha]
    exact (canonical32875 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2398 + difference 5 3) (sourceB2398 + difference 3 5) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA2398 + difference 5 3) (sourceB2398 + difference 3 5) sourceC2398) = raw32876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32876; decide +kernel
    rw [ha]
    exact (canonical32876 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2398 + difference 5 4) (sourceB2398 + difference 4 5) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA2398 + difference 5 4) (sourceB2398 + difference 4 5) sourceC2398) = raw32877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32877; decide +kernel
    rw [ha]
    exact (canonical32877 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2398 sourceB2398 sourceC2398
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2398, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2399 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2399 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC2399 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceForm2399 : Integer.Sparse Master := [(Sum.inr 2349, 1), (Sum.inr 2351, 2), (Sum.inr 2354, 1), (Sum.inr 2556, 1), (Sum.inr 3721, 1), (Sum.inr 4091, -1)]

theorem sourceEq2399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2399 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2399 + difference 0 1) (sourceB2399 + difference 1 0) sourceC2399) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA2399 + difference 0 1) (sourceB2399 + difference 1 0) sourceC2399) = raw32878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2399 sourceB2399 sourceC2399 difference raw32878; decide +kernel
    rw [ha]
    exact (canonical32878 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2399 + difference 1 1) (sourceB2399 + difference 1 1) sourceC2399) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA2399 + difference 1 1) (sourceB2399 + difference 1 1) sourceC2399) = raw24553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2399 sourceB2399 sourceC2399 difference raw24553; decide +kernel
    rw [ha]
    exact (canonical24553 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2399 + difference 2 1) (sourceB2399 + difference 1 2) sourceC2399) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2354) := by
    have ha : (tripleCharges (sourceA2399 + difference 2 1) (sourceB2399 + difference 1 2) sourceC2399) = raw32879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2399 sourceB2399 sourceC2399 difference raw32879; decide +kernel
    rw [ha]
    exact (canonical32879 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2399 + difference 3 1) (sourceB2399 + difference 1 3) sourceC2399) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2351) := by
    have ha : (tripleCharges (sourceA2399 + difference 3 1) (sourceB2399 + difference 1 3) sourceC2399) = raw32880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2399 sourceB2399 sourceC2399 difference raw32880; decide +kernel
    rw [ha]
    exact (canonical32880 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2399 + difference 4 1) (sourceB2399 + difference 1 4) sourceC2399) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2351) := by
    have ha : (tripleCharges (sourceA2399 + difference 4 1) (sourceB2399 + difference 1 4) sourceC2399) = raw29487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2399 sourceB2399 sourceC2399 difference raw29487; decide +kernel
    rw [ha]
    exact (canonical29487 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2399 + difference 5 1) (sourceB2399 + difference 1 5) sourceC2399) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2349) := by
    have ha : (tripleCharges (sourceA2399 + difference 5 1) (sourceB2399 + difference 1 5) sourceC2399) = raw27531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2399 sourceB2399 sourceC2399 difference raw27531; decide +kernel
    rw [ha]
    exact (canonical27531 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2399 + sourceB2399) sourceC2399) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2399 + sourceB2399) sourceC2399) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA2399 sourceB2399 sourceC2399 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2399 sourceB2399 sourceC2399
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2399, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
