import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical111
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical112
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical127
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical142
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical144
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical149
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical166
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical167
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical195
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical198
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical199
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical212
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical214
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical242
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical243
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical251
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical252
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical253
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical256
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical257
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical258
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical259
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical260
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical261
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical262
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical263
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical264

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2432 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2432 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceC2432 : Charge := ![2, 1, 1, -1, -1, -2]
def sourceForm2432 : Integer.Sparse Master := [(Sum.inr 4090, 1), (Sum.inr 4523, 1), (Sum.inr 4524, 2), (Sum.inr 4537, 1), (Sum.inr 4581, 1), (Sum.inr 4927, 1), (Sum.inr 4928, 2), (Sum.inr 4936, 1), (Sum.inr 5026, 1), (Sum.inr 5029, 2), (Sum.inr 5047, 2), (Sum.inr 5050, 2), (Sum.inr 5058, 1), (Sum.inr 5059, 2), (Sum.inr 5070, 2), (Sum.inr 5093, 1), (Sum.inr 5241, 2), (Sum.inr 5247, 1), (Sum.inr 5345, 1), (Sum.inr 5394, 2), (Sum.inr 5396, 1)]

theorem sourceEq2432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2432 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2432 + difference 0 1) (sourceB2432 + difference 1 0) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5345) := by
    have ha : (tripleCharges (sourceA2432 + difference 0 1) (sourceB2432 + difference 1 0) sourceC2432) = raw33387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33387; decide +kernel
    rw [ha]
    exact (canonical33387 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2432 + difference 0 2) (sourceB2432 + difference 2 0) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA2432 + difference 0 2) (sourceB2432 + difference 2 0) sourceC2432) = raw33388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33388; decide +kernel
    rw [ha]
    exact (canonical33388 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2432 + difference 0 3) (sourceB2432 + difference 3 0) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA2432 + difference 0 3) (sourceB2432 + difference 3 0) sourceC2432) = raw33389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33389; decide +kernel
    rw [ha]
    exact (canonical33389 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2432 + difference 0 4) (sourceB2432 + difference 4 0) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA2432 + difference 0 4) (sourceB2432 + difference 4 0) sourceC2432) = raw33390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33390; decide +kernel
    rw [ha]
    exact (canonical33390 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2432 + difference 0 5) (sourceB2432 + difference 5 0) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA2432 + difference 0 5) (sourceB2432 + difference 5 0) sourceC2432) = raw33391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33391; decide +kernel
    rw [ha]
    exact (canonical33391 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2432 + difference 1 0) (sourceB2432 + difference 0 1) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA2432 + difference 1 0) (sourceB2432 + difference 0 1) sourceC2432) = raw33392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33392; decide +kernel
    rw [ha]
    exact (canonical33392 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2432 + difference 1 2) (sourceB2432 + difference 2 1) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5058) := by
    have ha : (tripleCharges (sourceA2432 + difference 1 2) (sourceB2432 + difference 2 1) sourceC2432) = raw33393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33393; decide +kernel
    rw [ha]
    exact (canonical33393 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2432 + difference 1 3) (sourceB2432 + difference 3 1) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA2432 + difference 1 3) (sourceB2432 + difference 3 1) sourceC2432) = raw33394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33394; decide +kernel
    rw [ha]
    exact (canonical33394 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2432 + difference 1 4) (sourceB2432 + difference 4 1) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA2432 + difference 1 4) (sourceB2432 + difference 4 1) sourceC2432) = raw33395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33395; decide +kernel
    rw [ha]
    exact (canonical33395 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2432 + difference 1 5) (sourceB2432 + difference 5 1) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA2432 + difference 1 5) (sourceB2432 + difference 5 1) sourceC2432) = raw33396 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33396; decide +kernel
    rw [ha]
    exact (canonical33396 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2432 + difference 2 0) (sourceB2432 + difference 0 2) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4537) := by
    have ha : (tripleCharges (sourceA2432 + difference 2 0) (sourceB2432 + difference 0 2) sourceC2432) = raw33397 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33397; decide +kernel
    rw [ha]
    exact (canonical33397 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2432 + difference 2 1) (sourceB2432 + difference 1 2) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2432 + difference 2 1) (sourceB2432 + difference 1 2) sourceC2432) = raw33398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33398; decide +kernel
    rw [ha]
    exact (canonical33398 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2432 + difference 2 3) (sourceB2432 + difference 3 2) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA2432 + difference 2 3) (sourceB2432 + difference 3 2) sourceC2432) = raw33399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33399; decide +kernel
    rw [ha]
    exact (canonical33399 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2432 + difference 2 4) (sourceB2432 + difference 4 2) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA2432 + difference 2 4) (sourceB2432 + difference 4 2) sourceC2432) = raw33400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33400; decide +kernel
    rw [ha]
    exact (canonical33400 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2432 + difference 2 5) (sourceB2432 + difference 5 2) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5093) := by
    have ha : (tripleCharges (sourceA2432 + difference 2 5) (sourceB2432 + difference 5 2) sourceC2432) = raw33401 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33401; decide +kernel
    rw [ha]
    exact (canonical33401 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2432 + difference 3 0) (sourceB2432 + difference 0 3) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4524) := by
    have ha : (tripleCharges (sourceA2432 + difference 3 0) (sourceB2432 + difference 0 3) sourceC2432) = raw33402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33402; decide +kernel
    rw [ha]
    exact (canonical33402 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2432 + difference 3 1) (sourceB2432 + difference 1 3) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2432 + difference 3 1) (sourceB2432 + difference 1 3) sourceC2432) = raw33403 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33403; decide +kernel
    rw [ha]
    exact (canonical33403 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2432 + difference 3 2) (sourceB2432 + difference 2 3) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5029) := by
    have ha : (tripleCharges (sourceA2432 + difference 3 2) (sourceB2432 + difference 2 3) sourceC2432) = raw33404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33404; decide +kernel
    rw [ha]
    exact (canonical33404 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2432 + difference 3 4) (sourceB2432 + difference 4 3) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2432 + difference 3 4) (sourceB2432 + difference 4 3) sourceC2432) = raw33405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33405; decide +kernel
    rw [ha]
    exact (canonical33405 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2432 + difference 3 5) (sourceB2432 + difference 5 3) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA2432 + difference 3 5) (sourceB2432 + difference 5 3) sourceC2432) = raw33406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33406; decide +kernel
    rw [ha]
    exact (canonical33406 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2432 + difference 4 0) (sourceB2432 + difference 0 4) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4524) := by
    have ha : (tripleCharges (sourceA2432 + difference 4 0) (sourceB2432 + difference 0 4) sourceC2432) = raw33407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33407; decide +kernel
    rw [ha]
    exact (canonical33407 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2432 + difference 4 1) (sourceB2432 + difference 1 4) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2432 + difference 4 1) (sourceB2432 + difference 1 4) sourceC2432) = raw33408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33408; decide +kernel
    rw [ha]
    exact (canonical33408 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2432 + difference 4 2) (sourceB2432 + difference 2 4) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5029) := by
    have ha : (tripleCharges (sourceA2432 + difference 4 2) (sourceB2432 + difference 2 4) sourceC2432) = raw33409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33409; decide +kernel
    rw [ha]
    exact (canonical33409 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2432 + difference 4 3) (sourceB2432 + difference 3 4) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2432 + difference 4 3) (sourceB2432 + difference 3 4) sourceC2432) = raw33410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33410; decide +kernel
    rw [ha]
    exact (canonical33410 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2432 + difference 4 5) (sourceB2432 + difference 5 4) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA2432 + difference 4 5) (sourceB2432 + difference 5 4) sourceC2432) = raw33411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33411; decide +kernel
    rw [ha]
    exact (canonical33411 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2432 + difference 5 0) (sourceB2432 + difference 0 5) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4523) := by
    have ha : (tripleCharges (sourceA2432 + difference 5 0) (sourceB2432 + difference 0 5) sourceC2432) = raw33412 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33412; decide +kernel
    rw [ha]
    exact (canonical33412 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2432 + difference 5 1) (sourceB2432 + difference 1 5) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4927) := by
    have ha : (tripleCharges (sourceA2432 + difference 5 1) (sourceB2432 + difference 1 5) sourceC2432) = raw33413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33413; decide +kernel
    rw [ha]
    exact (canonical33413 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2432 + difference 5 2) (sourceB2432 + difference 2 5) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5026) := by
    have ha : (tripleCharges (sourceA2432 + difference 5 2) (sourceB2432 + difference 2 5) sourceC2432) = raw33414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33414; decide +kernel
    rw [ha]
    exact (canonical33414 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2432 + difference 5 3) (sourceB2432 + difference 3 5) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5047) := by
    have ha : (tripleCharges (sourceA2432 + difference 5 3) (sourceB2432 + difference 3 5) sourceC2432) = raw33415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33415; decide +kernel
    rw [ha]
    exact (canonical33415 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2432 + difference 5 4) (sourceB2432 + difference 4 5) sourceC2432) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5047) := by
    have ha : (tripleCharges (sourceA2432 + difference 5 4) (sourceB2432 + difference 4 5) sourceC2432) = raw33416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2432 sourceB2432 sourceC2432 difference raw33416; decide +kernel
    rw [ha]
    exact (canonical33416 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2432 sourceB2432 sourceC2432
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2432, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2433 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceB2433 : Charge := ![2, 1, 1, -1, -1, -2]
def sourceC2433 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2433 : Integer.Sparse Master := [(Sum.inr 4080, 1), (Sum.inr 4712, 1), (Sum.inr 4715, 2), (Sum.inr 4786, 1), (Sum.inr 4989, 1), (Sum.inr 4990, 2), (Sum.inr 5017, 1), (Sum.inr 5028, 1), (Sum.inr 5046, 2), (Sum.inr 5055, 2), (Sum.inr 5056, 2), (Sum.inr 5059, 2), (Sum.inr 5101, 2), (Sum.inr 5104, 1), (Sum.inr 5123, 1), (Sum.inr 5134, 2), (Sum.inr 5137, 1), (Sum.inr 5148, 1), (Sum.inr 5149, 2), (Sum.inr 5155, 1), (Sum.inr 5192, 1)]

theorem sourceEq2433 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2433 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2433 + difference 0 1) (sourceB2433 + difference 1 0) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA2433 + difference 0 1) (sourceB2433 + difference 1 0) sourceC2433) = raw33417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33417; decide +kernel
    rw [ha]
    exact (canonical33417 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2433 + difference 0 2) (sourceB2433 + difference 2 0) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA2433 + difference 0 2) (sourceB2433 + difference 2 0) sourceC2433) = raw33418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33418; decide +kernel
    rw [ha]
    exact (canonical33418 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2433 + difference 0 3) (sourceB2433 + difference 3 0) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2433 + difference 0 3) (sourceB2433 + difference 3 0) sourceC2433) = raw33419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33419; decide +kernel
    rw [ha]
    exact (canonical33419 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2433 + difference 0 4) (sourceB2433 + difference 4 0) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2433 + difference 0 4) (sourceB2433 + difference 4 0) sourceC2433) = raw32996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw32996; decide +kernel
    rw [ha]
    exact (canonical32996 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2433 + difference 0 5) (sourceB2433 + difference 5 0) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA2433 + difference 0 5) (sourceB2433 + difference 5 0) sourceC2433) = raw32898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw32898; decide +kernel
    rw [ha]
    exact (canonical32898 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2433 + difference 1 0) (sourceB2433 + difference 0 1) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4786) := by
    have ha : (tripleCharges (sourceA2433 + difference 1 0) (sourceB2433 + difference 0 1) sourceC2433) = raw32914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw32914; decide +kernel
    rw [ha]
    exact (canonical32914 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2433 + difference 1 2) (sourceB2433 + difference 2 1) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2433 + difference 1 2) (sourceB2433 + difference 2 1) sourceC2433) = raw32916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw32916; decide +kernel
    rw [ha]
    exact (canonical32916 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2433 + difference 1 3) (sourceB2433 + difference 3 1) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2433 + difference 1 3) (sourceB2433 + difference 3 1) sourceC2433) = raw32917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw32917; decide +kernel
    rw [ha]
    exact (canonical32917 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2433 + difference 1 4) (sourceB2433 + difference 4 1) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2433 + difference 1 4) (sourceB2433 + difference 4 1) sourceC2433) = raw32837 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw32837; decide +kernel
    rw [ha]
    exact (canonical32837 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2433 + difference 1 5) (sourceB2433 + difference 5 1) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2433 + difference 1 5) (sourceB2433 + difference 5 1) sourceC2433) = raw32252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw32252; decide +kernel
    rw [ha]
    exact (canonical32252 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2433 + difference 2 0) (sourceB2433 + difference 0 2) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2433 + difference 2 0) (sourceB2433 + difference 0 2) sourceC2433) = raw33420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33420; decide +kernel
    rw [ha]
    exact (canonical33420 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2433 + difference 2 1) (sourceB2433 + difference 1 2) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5017) := by
    have ha : (tripleCharges (sourceA2433 + difference 2 1) (sourceB2433 + difference 1 2) sourceC2433) = raw33421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33421; decide +kernel
    rw [ha]
    exact (canonical33421 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2433 + difference 2 3) (sourceB2433 + difference 3 2) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2433 + difference 2 3) (sourceB2433 + difference 3 2) sourceC2433) = raw33239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33239; decide +kernel
    rw [ha]
    exact (canonical33239 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2433 + difference 2 4) (sourceB2433 + difference 4 2) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2433 + difference 2 4) (sourceB2433 + difference 4 2) sourceC2433) = raw32836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw32836; decide +kernel
    rw [ha]
    exact (canonical32836 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2433 + difference 2 5) (sourceB2433 + difference 5 2) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2433 + difference 2 5) (sourceB2433 + difference 5 2) sourceC2433) = raw32251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw32251; decide +kernel
    rw [ha]
    exact (canonical32251 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2433 + difference 3 0) (sourceB2433 + difference 0 3) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4715) := by
    have ha : (tripleCharges (sourceA2433 + difference 3 0) (sourceB2433 + difference 0 3) sourceC2433) = raw33422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33422; decide +kernel
    rw [ha]
    exact (canonical33422 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2433 + difference 3 1) (sourceB2433 + difference 1 3) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4990) := by
    have ha : (tripleCharges (sourceA2433 + difference 3 1) (sourceB2433 + difference 1 3) sourceC2433) = raw33423 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33423; decide +kernel
    rw [ha]
    exact (canonical33423 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2433 + difference 3 2) (sourceB2433 + difference 2 3) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5046) := by
    have ha : (tripleCharges (sourceA2433 + difference 3 2) (sourceB2433 + difference 2 3) sourceC2433) = raw33424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33424; decide +kernel
    rw [ha]
    exact (canonical33424 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2433 + difference 3 4) (sourceB2433 + difference 4 3) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2433 + difference 3 4) (sourceB2433 + difference 4 3) sourceC2433) = raw33004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33004; decide +kernel
    rw [ha]
    exact (canonical33004 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2433 + difference 3 5) (sourceB2433 + difference 5 3) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA2433 + difference 3 5) (sourceB2433 + difference 5 3) sourceC2433) = raw32907 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw32907; decide +kernel
    rw [ha]
    exact (canonical32907 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2433 + difference 4 0) (sourceB2433 + difference 0 4) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4715) := by
    have ha : (tripleCharges (sourceA2433 + difference 4 0) (sourceB2433 + difference 0 4) sourceC2433) = raw33425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33425; decide +kernel
    rw [ha]
    exact (canonical33425 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2433 + difference 4 1) (sourceB2433 + difference 1 4) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4990) := by
    have ha : (tripleCharges (sourceA2433 + difference 4 1) (sourceB2433 + difference 1 4) sourceC2433) = raw33426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33426; decide +kernel
    rw [ha]
    exact (canonical33426 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2433 + difference 4 2) (sourceB2433 + difference 2 4) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5046) := by
    have ha : (tripleCharges (sourceA2433 + difference 4 2) (sourceB2433 + difference 2 4) sourceC2433) = raw33427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33427; decide +kernel
    rw [ha]
    exact (canonical33427 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2433 + difference 4 3) (sourceB2433 + difference 3 4) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2433 + difference 4 3) (sourceB2433 + difference 3 4) sourceC2433) = raw33428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33428; decide +kernel
    rw [ha]
    exact (canonical33428 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2433 + difference 4 5) (sourceB2433 + difference 5 4) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA2433 + difference 4 5) (sourceB2433 + difference 5 4) sourceC2433) = raw32911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw32911; decide +kernel
    rw [ha]
    exact (canonical32911 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2433 + difference 5 0) (sourceB2433 + difference 0 5) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4712) := by
    have ha : (tripleCharges (sourceA2433 + difference 5 0) (sourceB2433 + difference 0 5) sourceC2433) = raw33429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33429; decide +kernel
    rw [ha]
    exact (canonical33429 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2433 + difference 5 1) (sourceB2433 + difference 1 5) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4989) := by
    have ha : (tripleCharges (sourceA2433 + difference 5 1) (sourceB2433 + difference 1 5) sourceC2433) = raw33430 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33430; decide +kernel
    rw [ha]
    exact (canonical33430 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2433 + difference 5 2) (sourceB2433 + difference 2 5) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5028) := by
    have ha : (tripleCharges (sourceA2433 + difference 5 2) (sourceB2433 + difference 2 5) sourceC2433) = raw33431 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33431; decide +kernel
    rw [ha]
    exact (canonical33431 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2433 + difference 5 3) (sourceB2433 + difference 3 5) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5055) := by
    have ha : (tripleCharges (sourceA2433 + difference 5 3) (sourceB2433 + difference 3 5) sourceC2433) = raw33432 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33432; decide +kernel
    rw [ha]
    exact (canonical33432 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2433 + difference 5 4) (sourceB2433 + difference 4 5) sourceC2433) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5055) := by
    have ha : (tripleCharges (sourceA2433 + difference 5 4) (sourceB2433 + difference 4 5) sourceC2433) = raw33007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2433 sourceB2433 sourceC2433 difference raw33007; decide +kernel
    rw [ha]
    exact (canonical33007 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2433 sourceB2433 sourceC2433
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2433, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2434 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceB2434 : Charge := ![2, 2, -1, -1, -1, -1]
def sourceC2434 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2434 : Integer.Sparse Master := [(Sum.inr 1770, 1), (Sum.inr 1771, 2), (Sum.inr 1776, 1), (Sum.inr 1943, 1), (Sum.inr 3352, 1), (Sum.inr 4080, -1)]

theorem sourceEq2434 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2434 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2434 + difference 0 0) (sourceB2434 + difference 0 0) sourceC2434) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3352) := by
    have ha : (tripleCharges (sourceA2434 + difference 0 0) (sourceB2434 + difference 0 0) sourceC2434) = raw33433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2434 sourceB2434 sourceC2434 difference raw33433; decide +kernel
    rw [ha]
    exact (canonical33433 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2434 + difference 1 0) (sourceB2434 + difference 0 1) sourceC2434) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1943) := by
    have ha : (tripleCharges (sourceA2434 + difference 1 0) (sourceB2434 + difference 0 1) sourceC2434) = raw33434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2434 sourceB2434 sourceC2434 difference raw33434; decide +kernel
    rw [ha]
    exact (canonical33434 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2434 + difference 2 0) (sourceB2434 + difference 0 2) sourceC2434) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1776) := by
    have ha : (tripleCharges (sourceA2434 + difference 2 0) (sourceB2434 + difference 0 2) sourceC2434) = raw33435 := by
      apply Matrix.ext; unfold tripleCharges sourceA2434 sourceB2434 sourceC2434 difference raw33435; decide +kernel
    rw [ha]
    exact (canonical33435 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2434 + difference 3 0) (sourceB2434 + difference 0 3) sourceC2434) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1771) := by
    have ha : (tripleCharges (sourceA2434 + difference 3 0) (sourceB2434 + difference 0 3) sourceC2434) = raw33436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2434 sourceB2434 sourceC2434 difference raw33436; decide +kernel
    rw [ha]
    exact (canonical33436 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2434 + difference 4 0) (sourceB2434 + difference 0 4) sourceC2434) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1771) := by
    have ha : (tripleCharges (sourceA2434 + difference 4 0) (sourceB2434 + difference 0 4) sourceC2434) = raw33437 := by
      apply Matrix.ext; unfold tripleCharges sourceA2434 sourceB2434 sourceC2434 difference raw33437; decide +kernel
    rw [ha]
    exact (canonical33437 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2434 + difference 5 0) (sourceB2434 + difference 0 5) sourceC2434) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1770) := by
    have ha : (tripleCharges (sourceA2434 + difference 5 0) (sourceB2434 + difference 0 5) sourceC2434) = raw33438 := by
      apply Matrix.ext; unfold tripleCharges sourceA2434 sourceB2434 sourceC2434 difference raw33438; decide +kernel
    rw [ha]
    exact (canonical33438 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2434 + sourceB2434) sourceC2434) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2434 + sourceB2434) sourceC2434) = raw31902 := by
      apply Matrix.ext; unfold doubleCharges sourceA2434 sourceB2434 sourceC2434 raw31902; decide +kernel
    rw [ha]
    exact (canonical31902 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2434 sourceB2434 sourceC2434
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2434, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2435 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceB2435 : Charge := ![2, 2, -1, -1, -1, -1]
def sourceC2435 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2435 : Integer.Sparse Master := [(Sum.inr 1770, 1), (Sum.inr 2791, 1), (Sum.inr 3340, 2), (Sum.inr 3352, 1), (Sum.inr 3356, 1), (Sum.inr 4080, -1)]

theorem sourceEq2435 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2435 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2435 + difference 5 0) (sourceB2435 + difference 0 5) sourceC2435) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1770) := by
    have ha : (tripleCharges (sourceA2435 + difference 5 0) (sourceB2435 + difference 0 5) sourceC2435) = raw33438 := by
      apply Matrix.ext; unfold tripleCharges sourceA2435 sourceB2435 sourceC2435 difference raw33438; decide +kernel
    rw [ha]
    exact (canonical33438 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2435 + difference 5 1) (sourceB2435 + difference 1 5) sourceC2435) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2791) := by
    have ha : (tripleCharges (sourceA2435 + difference 5 1) (sourceB2435 + difference 1 5) sourceC2435) = raw33439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2435 sourceB2435 sourceC2435 difference raw33439; decide +kernel
    rw [ha]
    exact (canonical33439 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2435 + difference 5 2) (sourceB2435 + difference 2 5) sourceC2435) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3356) := by
    have ha : (tripleCharges (sourceA2435 + difference 5 2) (sourceB2435 + difference 2 5) sourceC2435) = raw33440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2435 sourceB2435 sourceC2435 difference raw33440; decide +kernel
    rw [ha]
    exact (canonical33440 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2435 + difference 5 3) (sourceB2435 + difference 3 5) sourceC2435) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3340) := by
    have ha : (tripleCharges (sourceA2435 + difference 5 3) (sourceB2435 + difference 3 5) sourceC2435) = raw33441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2435 sourceB2435 sourceC2435 difference raw33441; decide +kernel
    rw [ha]
    exact (canonical33441 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2435 + difference 5 4) (sourceB2435 + difference 4 5) sourceC2435) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3340) := by
    have ha : (tripleCharges (sourceA2435 + difference 5 4) (sourceB2435 + difference 4 5) sourceC2435) = raw33442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2435 sourceB2435 sourceC2435 difference raw33442; decide +kernel
    rw [ha]
    exact (canonical33442 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2435 + difference 5 5) (sourceB2435 + difference 5 5) sourceC2435) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3352) := by
    have ha : (tripleCharges (sourceA2435 + difference 5 5) (sourceB2435 + difference 5 5) sourceC2435) = raw33433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2435 sourceB2435 sourceC2435 difference raw33433; decide +kernel
    rw [ha]
    exact (canonical33433 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2435 + sourceB2435) sourceC2435) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2435 + sourceB2435) sourceC2435) = raw31902 := by
      apply Matrix.ext; unfold doubleCharges sourceA2435 sourceB2435 sourceC2435 raw31902; decide +kernel
    rw [ha]
    exact (canonical31902 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2435 sourceB2435 sourceC2435
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2435, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2436 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2436 : Charge := ![1, -1, 1, 0, -1, 0]
def sourceC2436 : Charge := ![2, 2, -1, -1, 0, -2]
def sourceForm2436 : Integer.Sparse Master := [(Sum.inr 2295, 1), (Sum.inr 2296, 1), (Sum.inr 2298, 1), (Sum.inr 2304, 1), (Sum.inr 2382, 1), (Sum.inr 3650, 1), (Sum.inr 4088, -1)]

theorem sourceEq2436 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2436 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2436 + difference 0 1) (sourceB2436 + difference 1 0) sourceC2436) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3650) := by
    have ha : (tripleCharges (sourceA2436 + difference 0 1) (sourceB2436 + difference 1 0) sourceC2436) = raw33443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2436 sourceB2436 sourceC2436 difference raw33443; decide +kernel
    rw [ha]
    exact (canonical33443 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2436 + difference 1 1) (sourceB2436 + difference 1 1) sourceC2436) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2382) := by
    have ha : (tripleCharges (sourceA2436 + difference 1 1) (sourceB2436 + difference 1 1) sourceC2436) = raw33444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2436 sourceB2436 sourceC2436 difference raw33444; decide +kernel
    rw [ha]
    exact (canonical33444 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2436 + difference 2 1) (sourceB2436 + difference 1 2) sourceC2436) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2304) := by
    have ha : (tripleCharges (sourceA2436 + difference 2 1) (sourceB2436 + difference 1 2) sourceC2436) = raw33445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2436 sourceB2436 sourceC2436 difference raw33445; decide +kernel
    rw [ha]
    exact (canonical33445 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2436 + difference 3 1) (sourceB2436 + difference 1 3) sourceC2436) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2296) := by
    have ha : (tripleCharges (sourceA2436 + difference 3 1) (sourceB2436 + difference 1 3) sourceC2436) = raw33446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2436 sourceB2436 sourceC2436 difference raw33446; decide +kernel
    rw [ha]
    exact (canonical33446 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2436 + difference 4 1) (sourceB2436 + difference 1 4) sourceC2436) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2298) := by
    have ha : (tripleCharges (sourceA2436 + difference 4 1) (sourceB2436 + difference 1 4) sourceC2436) = raw33447 := by
      apply Matrix.ext; unfold tripleCharges sourceA2436 sourceB2436 sourceC2436 difference raw33447; decide +kernel
    rw [ha]
    exact (canonical33447 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2436 + difference 5 1) (sourceB2436 + difference 1 5) sourceC2436) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2295) := by
    have ha : (tripleCharges (sourceA2436 + difference 5 1) (sourceB2436 + difference 1 5) sourceC2436) = raw33448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2436 sourceB2436 sourceC2436 difference raw33448; decide +kernel
    rw [ha]
    exact (canonical33448 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2436 + sourceB2436) sourceC2436) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2436 + sourceB2436) sourceC2436) = raw33449 := by
      apply Matrix.ext; unfold doubleCharges sourceA2436 sourceB2436 sourceC2436 raw33449; decide +kernel
    rw [ha]
    exact (canonical33449 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2436 sourceB2436 sourceC2436
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2436, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2437 : Charge := ![1, -1, 0, 1, 0, -1]
def sourceB2437 : Charge := ![2, 2, 0, -2, -1, -1]
def sourceC2437 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2437 : Integer.Sparse Master := [(Sum.inr 1771, 1), (Sum.inr 1778, 1), (Sum.inr 1780, 1), (Sum.inr 1782, 1), (Sum.inr 1947, 1), (Sum.inr 3357, 1), (Sum.inr 4080, -1)]

theorem sourceEq2437 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2437 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2437 + difference 0 0) (sourceB2437 + difference 0 0) sourceC2437) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3357) := by
    have ha : (tripleCharges (sourceA2437 + difference 0 0) (sourceB2437 + difference 0 0) sourceC2437) = raw33450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2437 sourceB2437 sourceC2437 difference raw33450; decide +kernel
    rw [ha]
    exact (canonical33450 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2437 + difference 1 0) (sourceB2437 + difference 0 1) sourceC2437) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1947) := by
    have ha : (tripleCharges (sourceA2437 + difference 1 0) (sourceB2437 + difference 0 1) sourceC2437) = raw33379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2437 sourceB2437 sourceC2437 difference raw33379; decide +kernel
    rw [ha]
    exact (canonical33379 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2437 + difference 2 0) (sourceB2437 + difference 0 2) sourceC2437) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1771) := by
    have ha : (tripleCharges (sourceA2437 + difference 2 0) (sourceB2437 + difference 0 2) sourceC2437) = raw33436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2437 sourceB2437 sourceC2437 difference raw33436; decide +kernel
    rw [ha]
    exact (canonical33436 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2437 + difference 3 0) (sourceB2437 + difference 0 3) sourceC2437) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1778) := by
    have ha : (tripleCharges (sourceA2437 + difference 3 0) (sourceB2437 + difference 0 3) sourceC2437) = raw33451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2437 sourceB2437 sourceC2437 difference raw33451; decide +kernel
    rw [ha]
    exact (canonical33451 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2437 + difference 4 0) (sourceB2437 + difference 0 4) sourceC2437) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1782) := by
    have ha : (tripleCharges (sourceA2437 + difference 4 0) (sourceB2437 + difference 0 4) sourceC2437) = raw33452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2437 sourceB2437 sourceC2437 difference raw33452; decide +kernel
    rw [ha]
    exact (canonical33452 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2437 + difference 5 0) (sourceB2437 + difference 0 5) sourceC2437) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1780) := by
    have ha : (tripleCharges (sourceA2437 + difference 5 0) (sourceB2437 + difference 0 5) sourceC2437) = raw33453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2437 sourceB2437 sourceC2437 difference raw33453; decide +kernel
    rw [ha]
    exact (canonical33453 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2437 + sourceB2437) sourceC2437) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2437 + sourceB2437) sourceC2437) = raw31902 := by
      apply Matrix.ext; unfold doubleCharges sourceA2437 sourceB2437 sourceC2437 raw31902; decide +kernel
    rw [ha]
    exact (canonical31902 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2437 sourceB2437 sourceC2437
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2437, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2438 : Charge := ![1, -1, 0, 0, 0, 0]
def sourceB2438 : Charge := ![2, 2, 0, -1, -1, -2]
def sourceC2438 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2438 : Integer.Sparse Master := [(Sum.inr 4080, 1), (Sum.inr 4641, 1), (Sum.inr 4649, 1), (Sum.inr 4652, 2), (Sum.inr 4981, 1), (Sum.inr 4982, 1), (Sum.inr 4983, 2), (Sum.inr 4989, 1), (Sum.inr 4990, 2), (Sum.inr 4996, 2), (Sum.inr 4998, 1), (Sum.inr 5014, 2), (Sum.inr 5015, 2), (Sum.inr 5018, 2), (Sum.inr 5058, 1), (Sum.inr 5101, 2), (Sum.inr 5104, 1), (Sum.inr 5192, 1), (Sum.inr 5203, 1), (Sum.inr 5204, 2), (Sum.inr 5213, 1)]

theorem sourceEq2438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2438 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2438 + difference 0 1) (sourceB2438 + difference 1 0) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5213) := by
    have ha : (tripleCharges (sourceA2438 + difference 0 1) (sourceB2438 + difference 1 0) sourceC2438) = raw33454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33454; decide +kernel
    rw [ha]
    exact (canonical33454 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2438 + difference 0 2) (sourceB2438 + difference 2 0) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA2438 + difference 0 2) (sourceB2438 + difference 2 0) sourceC2438) = raw33417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33417; decide +kernel
    rw [ha]
    exact (canonical33417 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2438 + difference 0 3) (sourceB2438 + difference 3 0) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2438 + difference 0 3) (sourceB2438 + difference 3 0) sourceC2438) = raw33455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33455; decide +kernel
    rw [ha]
    exact (canonical33455 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2438 + difference 0 4) (sourceB2438 + difference 4 0) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2438 + difference 0 4) (sourceB2438 + difference 4 0) sourceC2438) = raw33456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33456; decide +kernel
    rw [ha]
    exact (canonical33456 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2438 + difference 0 5) (sourceB2438 + difference 5 0) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2438 + difference 0 5) (sourceB2438 + difference 5 0) sourceC2438) = raw33457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33457; decide +kernel
    rw [ha]
    exact (canonical33457 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2438 + difference 1 0) (sourceB2438 + difference 0 1) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2438 + difference 1 0) (sourceB2438 + difference 0 1) sourceC2438) = raw33420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33420; decide +kernel
    rw [ha]
    exact (canonical33420 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2438 + difference 1 2) (sourceB2438 + difference 2 1) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5058) := by
    have ha : (tripleCharges (sourceA2438 + difference 1 2) (sourceB2438 + difference 2 1) sourceC2438) = raw32915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw32915; decide +kernel
    rw [ha]
    exact (canonical32915 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2438 + difference 1 3) (sourceB2438 + difference 3 1) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2438 + difference 1 3) (sourceB2438 + difference 3 1) sourceC2438) = raw33239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33239; decide +kernel
    rw [ha]
    exact (canonical33239 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2438 + difference 1 4) (sourceB2438 + difference 4 1) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2438 + difference 1 4) (sourceB2438 + difference 4 1) sourceC2438) = raw32836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw32836; decide +kernel
    rw [ha]
    exact (canonical32836 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2438 + difference 1 5) (sourceB2438 + difference 5 1) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2438 + difference 1 5) (sourceB2438 + difference 5 1) sourceC2438) = raw32251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw32251; decide +kernel
    rw [ha]
    exact (canonical32251 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2438 + difference 2 0) (sourceB2438 + difference 0 2) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4641) := by
    have ha : (tripleCharges (sourceA2438 + difference 2 0) (sourceB2438 + difference 0 2) sourceC2438) = raw33458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33458; decide +kernel
    rw [ha]
    exact (canonical33458 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2438 + difference 2 1) (sourceB2438 + difference 1 2) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4981) := by
    have ha : (tripleCharges (sourceA2438 + difference 2 1) (sourceB2438 + difference 1 2) sourceC2438) = raw33459 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33459; decide +kernel
    rw [ha]
    exact (canonical33459 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2438 + difference 2 3) (sourceB2438 + difference 3 2) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA2438 + difference 2 3) (sourceB2438 + difference 3 2) sourceC2438) = raw33238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33238; decide +kernel
    rw [ha]
    exact (canonical33238 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2438 + difference 2 4) (sourceB2438 + difference 4 2) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA2438 + difference 2 4) (sourceB2438 + difference 4 2) sourceC2438) = raw33148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33148; decide +kernel
    rw [ha]
    exact (canonical33148 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2438 + difference 2 5) (sourceB2438 + difference 5 2) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA2438 + difference 2 5) (sourceB2438 + difference 5 2) sourceC2438) = raw33146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33146; decide +kernel
    rw [ha]
    exact (canonical33146 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2438 + difference 3 0) (sourceB2438 + difference 0 3) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4652) := by
    have ha : (tripleCharges (sourceA2438 + difference 3 0) (sourceB2438 + difference 0 3) sourceC2438) = raw33460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33460; decide +kernel
    rw [ha]
    exact (canonical33460 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2438 + difference 3 1) (sourceB2438 + difference 1 3) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4983) := by
    have ha : (tripleCharges (sourceA2438 + difference 3 1) (sourceB2438 + difference 1 3) sourceC2438) = raw33461 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33461; decide +kernel
    rw [ha]
    exact (canonical33461 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2438 + difference 3 2) (sourceB2438 + difference 2 3) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4990) := by
    have ha : (tripleCharges (sourceA2438 + difference 3 2) (sourceB2438 + difference 2 3) sourceC2438) = raw33423 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33423; decide +kernel
    rw [ha]
    exact (canonical33423 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2438 + difference 3 4) (sourceB2438 + difference 4 3) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2438 + difference 3 4) (sourceB2438 + difference 4 3) sourceC2438) = raw33462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33462; decide +kernel
    rw [ha]
    exact (canonical33462 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2438 + difference 3 5) (sourceB2438 + difference 5 3) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA2438 + difference 3 5) (sourceB2438 + difference 5 3) sourceC2438) = raw33463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33463; decide +kernel
    rw [ha]
    exact (canonical33463 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2438 + difference 4 0) (sourceB2438 + difference 0 4) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4652) := by
    have ha : (tripleCharges (sourceA2438 + difference 4 0) (sourceB2438 + difference 0 4) sourceC2438) = raw33464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33464; decide +kernel
    rw [ha]
    exact (canonical33464 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2438 + difference 4 1) (sourceB2438 + difference 1 4) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4983) := by
    have ha : (tripleCharges (sourceA2438 + difference 4 1) (sourceB2438 + difference 1 4) sourceC2438) = raw33465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33465; decide +kernel
    rw [ha]
    exact (canonical33465 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2438 + difference 4 2) (sourceB2438 + difference 2 4) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4990) := by
    have ha : (tripleCharges (sourceA2438 + difference 4 2) (sourceB2438 + difference 2 4) sourceC2438) = raw33426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33426; decide +kernel
    rw [ha]
    exact (canonical33426 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2438 + difference 4 3) (sourceB2438 + difference 3 4) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2438 + difference 4 3) (sourceB2438 + difference 3 4) sourceC2438) = raw33466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33466; decide +kernel
    rw [ha]
    exact (canonical33466 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2438 + difference 4 5) (sourceB2438 + difference 5 4) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA2438 + difference 4 5) (sourceB2438 + difference 5 4) sourceC2438) = raw33467 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33467; decide +kernel
    rw [ha]
    exact (canonical33467 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2438 + difference 5 0) (sourceB2438 + difference 0 5) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4649) := by
    have ha : (tripleCharges (sourceA2438 + difference 5 0) (sourceB2438 + difference 0 5) sourceC2438) = raw33468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33468; decide +kernel
    rw [ha]
    exact (canonical33468 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2438 + difference 5 1) (sourceB2438 + difference 1 5) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4982) := by
    have ha : (tripleCharges (sourceA2438 + difference 5 1) (sourceB2438 + difference 1 5) sourceC2438) = raw33469 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33469; decide +kernel
    rw [ha]
    exact (canonical33469 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2438 + difference 5 2) (sourceB2438 + difference 2 5) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4989) := by
    have ha : (tripleCharges (sourceA2438 + difference 5 2) (sourceB2438 + difference 2 5) sourceC2438) = raw33430 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33430; decide +kernel
    rw [ha]
    exact (canonical33430 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2438 + difference 5 3) (sourceB2438 + difference 3 5) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA2438 + difference 5 3) (sourceB2438 + difference 3 5) sourceC2438) = raw33470 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33470; decide +kernel
    rw [ha]
    exact (canonical33470 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2438 + difference 5 4) (sourceB2438 + difference 4 5) sourceC2438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA2438 + difference 5 4) (sourceB2438 + difference 4 5) sourceC2438) = raw33471 := by
      apply Matrix.ext; unfold tripleCharges sourceA2438 sourceB2438 sourceC2438 difference raw33471; decide +kernel
    rw [ha]
    exact (canonical33471 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2438 sourceB2438 sourceC2438
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2438, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2439 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2439 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2439 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceForm2439 : Integer.Sparse Master := [(Sum.inr 4366, 1), (Sum.inr 4371, 1), (Sum.inr 4372, 2), (Sum.inr 4461, 1), (Sum.inr 4698, 1), (Sum.inr 4702, 1), (Sum.inr 4703, 2), (Sum.inr 4765, 1), (Sum.inr 4775, 2), (Sum.inr 4805, 1), (Sum.inr 4808, 2), (Sum.inr 4852, 2), (Sum.inr 4856, 2), (Sum.inr 4864, 1), (Sum.inr 4866, 2), (Sum.inr 4889, 2), (Sum.inr 4893, 1), (Sum.inr 5263, 1), (Sum.inr 5279, 1), (Sum.inr 5290, 1), (Sum.inr 5299, 2)]

theorem sourceEq2439 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2439 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2439 + difference 0 1) (sourceB2439 + difference 1 0) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5279) := by
    have ha : (tripleCharges (sourceA2439 + difference 0 1) (sourceB2439 + difference 1 0) sourceC2439) = raw33472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33472; decide +kernel
    rw [ha]
    exact (canonical33472 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2439 + difference 0 2) (sourceB2439 + difference 2 0) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA2439 + difference 0 2) (sourceB2439 + difference 2 0) sourceC2439) = raw33473 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33473; decide +kernel
    rw [ha]
    exact (canonical33473 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2439 + difference 0 3) (sourceB2439 + difference 3 0) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA2439 + difference 0 3) (sourceB2439 + difference 3 0) sourceC2439) = raw33474 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33474; decide +kernel
    rw [ha]
    exact (canonical33474 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2439 + difference 0 4) (sourceB2439 + difference 4 0) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA2439 + difference 0 4) (sourceB2439 + difference 4 0) sourceC2439) = raw33475 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33475; decide +kernel
    rw [ha]
    exact (canonical33475 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2439 + difference 0 5) (sourceB2439 + difference 5 0) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA2439 + difference 0 5) (sourceB2439 + difference 5 0) sourceC2439) = raw14330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw14330; decide +kernel
    rw [ha]
    exact (canonical14330 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2439 + difference 1 0) (sourceB2439 + difference 0 1) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA2439 + difference 1 0) (sourceB2439 + difference 0 1) sourceC2439) = raw14355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw14355; decide +kernel
    rw [ha]
    exact (canonical14355 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2439 + difference 1 2) (sourceB2439 + difference 2 1) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2439 + difference 1 2) (sourceB2439 + difference 2 1) sourceC2439) = raw14357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw14357; decide +kernel
    rw [ha]
    exact (canonical14357 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2439 + difference 1 3) (sourceB2439 + difference 3 1) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2439 + difference 1 3) (sourceB2439 + difference 3 1) sourceC2439) = raw14358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw14358; decide +kernel
    rw [ha]
    exact (canonical14358 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2439 + difference 1 4) (sourceB2439 + difference 4 1) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2439 + difference 1 4) (sourceB2439 + difference 4 1) sourceC2439) = raw14359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw14359; decide +kernel
    rw [ha]
    exact (canonical14359 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2439 + difference 1 5) (sourceB2439 + difference 5 1) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA2439 + difference 1 5) (sourceB2439 + difference 5 1) sourceC2439) = raw25003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw25003; decide +kernel
    rw [ha]
    exact (canonical25003 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2439 + difference 2 0) (sourceB2439 + difference 0 2) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4366) := by
    have ha : (tripleCharges (sourceA2439 + difference 2 0) (sourceB2439 + difference 0 2) sourceC2439) = raw25009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw25009; decide +kernel
    rw [ha]
    exact (canonical25009 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2439 + difference 2 1) (sourceB2439 + difference 1 2) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4698) := by
    have ha : (tripleCharges (sourceA2439 + difference 2 1) (sourceB2439 + difference 1 2) sourceC2439) = raw33476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33476; decide +kernel
    rw [ha]
    exact (canonical33476 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2439 + difference 2 3) (sourceB2439 + difference 3 2) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA2439 + difference 2 3) (sourceB2439 + difference 3 2) sourceC2439) = raw33477 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33477; decide +kernel
    rw [ha]
    exact (canonical33477 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2439 + difference 2 4) (sourceB2439 + difference 4 2) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA2439 + difference 2 4) (sourceB2439 + difference 4 2) sourceC2439) = raw33478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33478; decide +kernel
    rw [ha]
    exact (canonical33478 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2439 + difference 2 5) (sourceB2439 + difference 5 2) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA2439 + difference 2 5) (sourceB2439 + difference 5 2) sourceC2439) = raw14341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw14341; decide +kernel
    rw [ha]
    exact (canonical14341 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2439 + difference 3 0) (sourceB2439 + difference 0 3) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4372) := by
    have ha : (tripleCharges (sourceA2439 + difference 3 0) (sourceB2439 + difference 0 3) sourceC2439) = raw25013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw25013; decide +kernel
    rw [ha]
    exact (canonical25013 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2439 + difference 3 1) (sourceB2439 + difference 1 3) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4703) := by
    have ha : (tripleCharges (sourceA2439 + difference 3 1) (sourceB2439 + difference 1 3) sourceC2439) = raw33479 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33479; decide +kernel
    rw [ha]
    exact (canonical33479 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2439 + difference 3 2) (sourceB2439 + difference 2 3) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4775) := by
    have ha : (tripleCharges (sourceA2439 + difference 3 2) (sourceB2439 + difference 2 3) sourceC2439) = raw33480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33480; decide +kernel
    rw [ha]
    exact (canonical33480 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2439 + difference 3 4) (sourceB2439 + difference 4 3) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2439 + difference 3 4) (sourceB2439 + difference 4 3) sourceC2439) = raw33481 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33481; decide +kernel
    rw [ha]
    exact (canonical33481 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2439 + difference 3 5) (sourceB2439 + difference 5 3) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2439 + difference 3 5) (sourceB2439 + difference 5 3) sourceC2439) = raw14346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw14346; decide +kernel
    rw [ha]
    exact (canonical14346 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2439 + difference 4 0) (sourceB2439 + difference 0 4) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4372) := by
    have ha : (tripleCharges (sourceA2439 + difference 4 0) (sourceB2439 + difference 0 4) sourceC2439) = raw25017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw25017; decide +kernel
    rw [ha]
    exact (canonical25017 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2439 + difference 4 1) (sourceB2439 + difference 1 4) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4703) := by
    have ha : (tripleCharges (sourceA2439 + difference 4 1) (sourceB2439 + difference 1 4) sourceC2439) = raw33482 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33482; decide +kernel
    rw [ha]
    exact (canonical33482 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2439 + difference 4 2) (sourceB2439 + difference 2 4) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4775) := by
    have ha : (tripleCharges (sourceA2439 + difference 4 2) (sourceB2439 + difference 2 4) sourceC2439) = raw33483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33483; decide +kernel
    rw [ha]
    exact (canonical33483 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2439 + difference 4 3) (sourceB2439 + difference 3 4) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2439 + difference 4 3) (sourceB2439 + difference 3 4) sourceC2439) = raw33484 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33484; decide +kernel
    rw [ha]
    exact (canonical33484 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2439 + difference 4 5) (sourceB2439 + difference 5 4) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2439 + difference 4 5) (sourceB2439 + difference 5 4) sourceC2439) = raw14351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw14351; decide +kernel
    rw [ha]
    exact (canonical14351 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2439 + difference 5 0) (sourceB2439 + difference 0 5) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4371) := by
    have ha : (tripleCharges (sourceA2439 + difference 5 0) (sourceB2439 + difference 0 5) sourceC2439) = raw25021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw25021; decide +kernel
    rw [ha]
    exact (canonical25021 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2439 + difference 5 1) (sourceB2439 + difference 1 5) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4702) := by
    have ha : (tripleCharges (sourceA2439 + difference 5 1) (sourceB2439 + difference 1 5) sourceC2439) = raw33485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33485; decide +kernel
    rw [ha]
    exact (canonical33485 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2439 + difference 5 2) (sourceB2439 + difference 2 5) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4765) := by
    have ha : (tripleCharges (sourceA2439 + difference 5 2) (sourceB2439 + difference 2 5) sourceC2439) = raw33486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33486; decide +kernel
    rw [ha]
    exact (canonical33486 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2439 + difference 5 3) (sourceB2439 + difference 3 5) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA2439 + difference 5 3) (sourceB2439 + difference 3 5) sourceC2439) = raw33487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33487; decide +kernel
    rw [ha]
    exact (canonical33487 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2439 + difference 5 4) (sourceB2439 + difference 4 5) sourceC2439) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA2439 + difference 5 4) (sourceB2439 + difference 4 5) sourceC2439) = raw33488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2439 sourceB2439 sourceC2439 difference raw33488; decide +kernel
    rw [ha]
    exact (canonical33488 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2439 sourceB2439 sourceC2439
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2439, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2440 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2440 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2440 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceForm2440 : Integer.Sparse Master := [(Sum.inr 1711, 1), (Sum.inr 1734, 2), (Sum.inr 1737, 1), (Sum.inr 1742, 1), (Sum.inr 2179, 1), (Sum.inr 2180, 1), (Sum.inr 2211, 2), (Sum.inr 2214, 1), (Sum.inr 2220, 2), (Sum.inr 2241, 1), (Sum.inr 2248, 1), (Sum.inr 2250, 2), (Sum.inr 2260, 2), (Sum.inr 2263, 1), (Sum.inr 2272, 2), (Sum.inr 2274, 2), (Sum.inr 2277, 2), (Sum.inr 2728, 1), (Sum.inr 2748, 1), (Sum.inr 2764, 1), (Sum.inr 2773, 2)]

theorem sourceEq2440 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2440 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2440 + difference 0 1) (sourceB2440 + difference 1 0) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2748) := by
    have ha : (tripleCharges (sourceA2440 + difference 0 1) (sourceB2440 + difference 1 0) sourceC2440) = raw33489 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33489; decide +kernel
    rw [ha]
    exact (canonical33489 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2440 + difference 0 2) (sourceB2440 + difference 2 0) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA2440 + difference 0 2) (sourceB2440 + difference 2 0) sourceC2440) = raw33490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33490; decide +kernel
    rw [ha]
    exact (canonical33490 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2440 + difference 0 3) (sourceB2440 + difference 3 0) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA2440 + difference 0 3) (sourceB2440 + difference 3 0) sourceC2440) = raw33491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33491; decide +kernel
    rw [ha]
    exact (canonical33491 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2440 + difference 0 4) (sourceB2440 + difference 4 0) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA2440 + difference 0 4) (sourceB2440 + difference 4 0) sourceC2440) = raw33492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33492; decide +kernel
    rw [ha]
    exact (canonical33492 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2440 + difference 0 5) (sourceB2440 + difference 5 0) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA2440 + difference 0 5) (sourceB2440 + difference 5 0) sourceC2440) = raw33493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33493; decide +kernel
    rw [ha]
    exact (canonical33493 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2440 + difference 1 0) (sourceB2440 + difference 0 1) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA2440 + difference 1 0) (sourceB2440 + difference 0 1) sourceC2440) = raw33494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33494; decide +kernel
    rw [ha]
    exact (canonical33494 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2440 + difference 1 2) (sourceB2440 + difference 2 1) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA2440 + difference 1 2) (sourceB2440 + difference 2 1) sourceC2440) = raw25026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25026; decide +kernel
    rw [ha]
    exact (canonical25026 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2440 + difference 1 3) (sourceB2440 + difference 3 1) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA2440 + difference 1 3) (sourceB2440 + difference 3 1) sourceC2440) = raw25027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25027; decide +kernel
    rw [ha]
    exact (canonical25027 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2440 + difference 1 4) (sourceB2440 + difference 4 1) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA2440 + difference 1 4) (sourceB2440 + difference 4 1) sourceC2440) = raw25028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25028; decide +kernel
    rw [ha]
    exact (canonical25028 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2440 + difference 1 5) (sourceB2440 + difference 5 1) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA2440 + difference 1 5) (sourceB2440 + difference 5 1) sourceC2440) = raw25029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25029; decide +kernel
    rw [ha]
    exact (canonical25029 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2440 + difference 2 0) (sourceB2440 + difference 0 2) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1711) := by
    have ha : (tripleCharges (sourceA2440 + difference 2 0) (sourceB2440 + difference 0 2) sourceC2440) = raw25036 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25036; decide +kernel
    rw [ha]
    exact (canonical25036 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2440 + difference 2 1) (sourceB2440 + difference 1 2) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2248) := by
    have ha : (tripleCharges (sourceA2440 + difference 2 1) (sourceB2440 + difference 1 2) sourceC2440) = raw33495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33495; decide +kernel
    rw [ha]
    exact (canonical33495 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2440 + difference 2 3) (sourceB2440 + difference 3 2) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA2440 + difference 2 3) (sourceB2440 + difference 3 2) sourceC2440) = raw33496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33496; decide +kernel
    rw [ha]
    exact (canonical33496 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2440 + difference 2 4) (sourceB2440 + difference 4 2) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA2440 + difference 2 4) (sourceB2440 + difference 4 2) sourceC2440) = raw33497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33497; decide +kernel
    rw [ha]
    exact (canonical33497 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2440 + difference 2 5) (sourceB2440 + difference 5 2) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA2440 + difference 2 5) (sourceB2440 + difference 5 2) sourceC2440) = raw33498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33498; decide +kernel
    rw [ha]
    exact (canonical33498 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2440 + difference 3 0) (sourceB2440 + difference 0 3) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA2440 + difference 3 0) (sourceB2440 + difference 0 3) sourceC2440) = raw25041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25041; decide +kernel
    rw [ha]
    exact (canonical25041 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2440 + difference 3 1) (sourceB2440 + difference 1 3) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2272) := by
    have ha : (tripleCharges (sourceA2440 + difference 3 1) (sourceB2440 + difference 1 3) sourceC2440) = raw33499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33499; decide +kernel
    rw [ha]
    exact (canonical33499 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2440 + difference 3 2) (sourceB2440 + difference 2 3) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2211) := by
    have ha : (tripleCharges (sourceA2440 + difference 3 2) (sourceB2440 + difference 2 3) sourceC2440) = raw33500 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33500; decide +kernel
    rw [ha]
    exact (canonical33500 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2440 + difference 3 4) (sourceB2440 + difference 4 3) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2440 + difference 3 4) (sourceB2440 + difference 4 3) sourceC2440) = raw33501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33501; decide +kernel
    rw [ha]
    exact (canonical33501 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2440 + difference 3 5) (sourceB2440 + difference 5 3) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2440 + difference 3 5) (sourceB2440 + difference 5 3) sourceC2440) = raw33502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33502; decide +kernel
    rw [ha]
    exact (canonical33502 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2440 + difference 4 0) (sourceB2440 + difference 0 4) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA2440 + difference 4 0) (sourceB2440 + difference 0 4) sourceC2440) = raw25046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25046; decide +kernel
    rw [ha]
    exact (canonical25046 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2440 + difference 4 1) (sourceB2440 + difference 1 4) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2272) := by
    have ha : (tripleCharges (sourceA2440 + difference 4 1) (sourceB2440 + difference 1 4) sourceC2440) = raw33503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33503; decide +kernel
    rw [ha]
    exact (canonical33503 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2440 + difference 4 2) (sourceB2440 + difference 2 4) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2211) := by
    have ha : (tripleCharges (sourceA2440 + difference 4 2) (sourceB2440 + difference 2 4) sourceC2440) = raw33504 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33504; decide +kernel
    rw [ha]
    exact (canonical33504 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2440 + difference 4 3) (sourceB2440 + difference 3 4) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2440 + difference 4 3) (sourceB2440 + difference 3 4) sourceC2440) = raw33505 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33505; decide +kernel
    rw [ha]
    exact (canonical33505 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2440 + difference 4 5) (sourceB2440 + difference 5 4) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2440 + difference 4 5) (sourceB2440 + difference 5 4) sourceC2440) = raw33506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33506; decide +kernel
    rw [ha]
    exact (canonical33506 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2440 + difference 5 0) (sourceB2440 + difference 0 5) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1742) := by
    have ha : (tripleCharges (sourceA2440 + difference 5 0) (sourceB2440 + difference 0 5) sourceC2440) = raw25051 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25051; decide +kernel
    rw [ha]
    exact (canonical25051 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2440 + difference 5 1) (sourceB2440 + difference 1 5) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2180) := by
    have ha : (tripleCharges (sourceA2440 + difference 5 1) (sourceB2440 + difference 1 5) sourceC2440) = raw33507 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33507; decide +kernel
    rw [ha]
    exact (canonical33507 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2440 + difference 5 2) (sourceB2440 + difference 2 5) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2179) := by
    have ha : (tripleCharges (sourceA2440 + difference 5 2) (sourceB2440 + difference 2 5) sourceC2440) = raw33508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33508; decide +kernel
    rw [ha]
    exact (canonical33508 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2440 + difference 5 3) (sourceB2440 + difference 3 5) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA2440 + difference 5 3) (sourceB2440 + difference 3 5) sourceC2440) = raw33509 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33509; decide +kernel
    rw [ha]
    exact (canonical33509 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2440 + difference 5 4) (sourceB2440 + difference 4 5) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA2440 + difference 5 4) (sourceB2440 + difference 4 5) sourceC2440) = raw33510 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33510; decide +kernel
    rw [ha]
    exact (canonical33510 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2440 sourceB2440 sourceC2440
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2440, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2441 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2441 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2441 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceForm2441 : Integer.Sparse Master := [(Sum.inr 1824, 1), (Sum.inr 1828, 1), (Sum.inr 1829, 2), (Sum.inr 2110, 1), (Sum.inr 3079, 1), (Sum.inr 4083, -1)]

theorem sourceEq2441 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2441 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2441 + difference 0 1) (sourceB2441 + difference 1 0) sourceC2441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3079) := by
    have ha : (tripleCharges (sourceA2441 + difference 0 1) (sourceB2441 + difference 1 0) sourceC2441) = raw33511 := by
      apply Matrix.ext; unfold tripleCharges sourceA2441 sourceB2441 sourceC2441 difference raw33511; decide +kernel
    rw [ha]
    exact (canonical33511 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2441 + difference 1 1) (sourceB2441 + difference 1 1) sourceC2441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA2441 + difference 1 1) (sourceB2441 + difference 1 1) sourceC2441) = raw25062 := by
      apply Matrix.ext; unfold tripleCharges sourceA2441 sourceB2441 sourceC2441 difference raw25062; decide +kernel
    rw [ha]
    exact (canonical25062 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2441 + difference 2 1) (sourceB2441 + difference 1 2) sourceC2441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1824) := by
    have ha : (tripleCharges (sourceA2441 + difference 2 1) (sourceB2441 + difference 1 2) sourceC2441) = raw33512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2441 sourceB2441 sourceC2441 difference raw33512; decide +kernel
    rw [ha]
    exact (canonical33512 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2441 + difference 3 1) (sourceB2441 + difference 1 3) sourceC2441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1829) := by
    have ha : (tripleCharges (sourceA2441 + difference 3 1) (sourceB2441 + difference 1 3) sourceC2441) = raw33513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2441 sourceB2441 sourceC2441 difference raw33513; decide +kernel
    rw [ha]
    exact (canonical33513 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2441 + difference 4 1) (sourceB2441 + difference 1 4) sourceC2441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1829) := by
    have ha : (tripleCharges (sourceA2441 + difference 4 1) (sourceB2441 + difference 1 4) sourceC2441) = raw33514 := by
      apply Matrix.ext; unfold tripleCharges sourceA2441 sourceB2441 sourceC2441 difference raw33514; decide +kernel
    rw [ha]
    exact (canonical33514 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2441 + difference 5 1) (sourceB2441 + difference 1 5) sourceC2441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1828) := by
    have ha : (tripleCharges (sourceA2441 + difference 5 1) (sourceB2441 + difference 1 5) sourceC2441) = raw33515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2441 sourceB2441 sourceC2441 difference raw33515; decide +kernel
    rw [ha]
    exact (canonical33515 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2441 + sourceB2441) sourceC2441) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2441 + sourceB2441) sourceC2441) = raw25061 := by
      apply Matrix.ext; unfold doubleCharges sourceA2441 sourceB2441 sourceC2441 raw25061; decide +kernel
    rw [ha]
    exact (canonical25061 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2441 sourceB2441 sourceC2441
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2441, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2442 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2442 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceC2442 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceForm2442 : Integer.Sparse Master := [(Sum.inr 4236, 1), (Sum.inr 4237, 1), (Sum.inr 4238, 2), (Sum.inr 4275, 1), (Sum.inr 4685, 1), (Sum.inr 4686, 1), (Sum.inr 4688, 2), (Sum.inr 4723, 1), (Sum.inr 4724, 2), (Sum.inr 4746, 1), (Sum.inr 4859, 1), (Sum.inr 4860, 2), (Sum.inr 4869, 3), (Sum.inr 4871, 2), (Sum.inr 4874, 2), (Sum.inr 4898, 2), (Sum.inr 5387, 1), (Sum.inr 5403, 1), (Sum.inr 5443, 2), (Sum.inr 5448, 1)]

theorem sourceEq2442 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2442 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2442 + difference 0 1) (sourceB2442 + difference 1 0) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2442 + difference 0 1) (sourceB2442 + difference 1 0) sourceC2442) = raw19193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw19193; decide +kernel
    rw [ha]
    exact (canonical19193 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2442 + difference 0 2) (sourceB2442 + difference 2 0) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA2442 + difference 0 2) (sourceB2442 + difference 2 0) sourceC2442) = raw19194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw19194; decide +kernel
    rw [ha]
    exact (canonical19194 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2442 + difference 0 3) (sourceB2442 + difference 3 0) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2442 + difference 0 3) (sourceB2442 + difference 3 0) sourceC2442) = raw10769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10769; decide +kernel
    rw [ha]
    exact (canonical10769 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2442 + difference 0 4) (sourceB2442 + difference 4 0) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2442 + difference 0 4) (sourceB2442 + difference 4 0) sourceC2442) = raw19195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw19195; decide +kernel
    rw [ha]
    exact (canonical19195 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2442 + difference 0 5) (sourceB2442 + difference 5 0) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA2442 + difference 0 5) (sourceB2442 + difference 5 0) sourceC2442) = raw33516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33516; decide +kernel
    rw [ha]
    exact (canonical33516 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2442 + difference 1 0) (sourceB2442 + difference 0 1) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4275) := by
    have ha : (tripleCharges (sourceA2442 + difference 1 0) (sourceB2442 + difference 0 1) sourceC2442) = raw10784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10784; decide +kernel
    rw [ha]
    exact (canonical10784 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2442 + difference 1 2) (sourceB2442 + difference 2 1) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4746) := by
    have ha : (tripleCharges (sourceA2442 + difference 1 2) (sourceB2442 + difference 2 1) sourceC2442) = raw10786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10786; decide +kernel
    rw [ha]
    exact (canonical10786 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2442 + difference 1 3) (sourceB2442 + difference 3 1) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA2442 + difference 1 3) (sourceB2442 + difference 3 1) sourceC2442) = raw31012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw31012; decide +kernel
    rw [ha]
    exact (canonical31012 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2442 + difference 1 4) (sourceB2442 + difference 4 1) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA2442 + difference 1 4) (sourceB2442 + difference 4 1) sourceC2442) = raw10787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10787; decide +kernel
    rw [ha]
    exact (canonical10787 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2442 + difference 1 5) (sourceB2442 + difference 5 1) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2442 + difference 1 5) (sourceB2442 + difference 5 1) sourceC2442) = raw10788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10788; decide +kernel
    rw [ha]
    exact (canonical10788 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2442 + difference 2 0) (sourceB2442 + difference 0 2) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4236) := by
    have ha : (tripleCharges (sourceA2442 + difference 2 0) (sourceB2442 + difference 0 2) sourceC2442) = raw33517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33517; decide +kernel
    rw [ha]
    exact (canonical33517 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2442 + difference 2 1) (sourceB2442 + difference 1 2) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4685) := by
    have ha : (tripleCharges (sourceA2442 + difference 2 1) (sourceB2442 + difference 1 2) sourceC2442) = raw33518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33518; decide +kernel
    rw [ha]
    exact (canonical33518 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2442 + difference 2 3) (sourceB2442 + difference 3 2) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2442 + difference 2 3) (sourceB2442 + difference 3 2) sourceC2442) = raw10780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10780; decide +kernel
    rw [ha]
    exact (canonical10780 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2442 + difference 2 4) (sourceB2442 + difference 4 2) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2442 + difference 2 4) (sourceB2442 + difference 4 2) sourceC2442) = raw33519 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33519; decide +kernel
    rw [ha]
    exact (canonical33519 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2442 + difference 2 5) (sourceB2442 + difference 5 2) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4859) := by
    have ha : (tripleCharges (sourceA2442 + difference 2 5) (sourceB2442 + difference 5 2) sourceC2442) = raw19178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw19178; decide +kernel
    rw [ha]
    exact (canonical19178 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2442 + difference 3 0) (sourceB2442 + difference 0 3) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4238) := by
    have ha : (tripleCharges (sourceA2442 + difference 3 0) (sourceB2442 + difference 0 3) sourceC2442) = raw33520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33520; decide +kernel
    rw [ha]
    exact (canonical33520 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2442 + difference 3 1) (sourceB2442 + difference 1 3) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2442 + difference 3 1) (sourceB2442 + difference 1 3) sourceC2442) = raw33521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33521; decide +kernel
    rw [ha]
    exact (canonical33521 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2442 + difference 3 2) (sourceB2442 + difference 2 3) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4724) := by
    have ha : (tripleCharges (sourceA2442 + difference 3 2) (sourceB2442 + difference 2 3) sourceC2442) = raw33522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33522; decide +kernel
    rw [ha]
    exact (canonical33522 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2442 + difference 3 4) (sourceB2442 + difference 4 3) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2442 + difference 3 4) (sourceB2442 + difference 4 3) sourceC2442) = raw33523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33523; decide +kernel
    rw [ha]
    exact (canonical33523 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2442 + difference 3 5) (sourceB2442 + difference 5 3) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2442 + difference 3 5) (sourceB2442 + difference 5 3) sourceC2442) = raw19183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw19183; decide +kernel
    rw [ha]
    exact (canonical19183 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2442 + difference 4 0) (sourceB2442 + difference 0 4) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4238) := by
    have ha : (tripleCharges (sourceA2442 + difference 4 0) (sourceB2442 + difference 0 4) sourceC2442) = raw31017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw31017; decide +kernel
    rw [ha]
    exact (canonical31017 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2442 + difference 4 1) (sourceB2442 + difference 1 4) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2442 + difference 4 1) (sourceB2442 + difference 1 4) sourceC2442) = raw31018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw31018; decide +kernel
    rw [ha]
    exact (canonical31018 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2442 + difference 4 2) (sourceB2442 + difference 2 4) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4724) := by
    have ha : (tripleCharges (sourceA2442 + difference 4 2) (sourceB2442 + difference 2 4) sourceC2442) = raw31019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw31019; decide +kernel
    rw [ha]
    exact (canonical31019 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2442 + difference 4 3) (sourceB2442 + difference 3 4) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2442 + difference 4 3) (sourceB2442 + difference 3 4) sourceC2442) = raw10790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10790; decide +kernel
    rw [ha]
    exact (canonical10790 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2442 + difference 4 5) (sourceB2442 + difference 5 4) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2442 + difference 4 5) (sourceB2442 + difference 5 4) sourceC2442) = raw19188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw19188; decide +kernel
    rw [ha]
    exact (canonical19188 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2442 + difference 5 0) (sourceB2442 + difference 0 5) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4237) := by
    have ha : (tripleCharges (sourceA2442 + difference 5 0) (sourceB2442 + difference 0 5) sourceC2442) = raw33524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33524; decide +kernel
    rw [ha]
    exact (canonical33524 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2442 + difference 5 1) (sourceB2442 + difference 1 5) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4686) := by
    have ha : (tripleCharges (sourceA2442 + difference 5 1) (sourceB2442 + difference 1 5) sourceC2442) = raw33525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33525; decide +kernel
    rw [ha]
    exact (canonical33525 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2442 + difference 5 2) (sourceB2442 + difference 2 5) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4723) := by
    have ha : (tripleCharges (sourceA2442 + difference 5 2) (sourceB2442 + difference 2 5) sourceC2442) = raw33526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33526; decide +kernel
    rw [ha]
    exact (canonical33526 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2442 + difference 5 3) (sourceB2442 + difference 3 5) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2442 + difference 5 3) (sourceB2442 + difference 3 5) sourceC2442) = raw10795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10795; decide +kernel
    rw [ha]
    exact (canonical10795 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2442 + difference 5 4) (sourceB2442 + difference 4 5) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2442 + difference 5 4) (sourceB2442 + difference 4 5) sourceC2442) = raw33527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33527; decide +kernel
    rw [ha]
    exact (canonical33527 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2442 sourceB2442 sourceC2442
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2442, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2443 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2443 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceC2443 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceForm2443 : Integer.Sparse Master := [(Sum.inr 736, 1), (Sum.inr 737, 1), (Sum.inr 738, 2), (Sum.inr 827, 1), (Sum.inr 1811, 1), (Sum.inr 1812, 1), (Sum.inr 1814, 2), (Sum.inr 1877, 1), (Sum.inr 1878, 2), (Sum.inr 1925, 1), (Sum.inr 2100, 1), (Sum.inr 2101, 2), (Sum.inr 2110, 2), (Sum.inr 2112, 2), (Sum.inr 2115, 2), (Sum.inr 2275, 1), (Sum.inr 2279, 2), (Sum.inr 3739, 1), (Sum.inr 3789, 1), (Sum.inr 3885, 1), (Sum.inr 3889, 2)]

theorem sourceEq2443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2443 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2443 + difference 0 1) (sourceB2443 + difference 1 0) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3739) := by
    have ha : (tripleCharges (sourceA2443 + difference 0 1) (sourceB2443 + difference 1 0) sourceC2443) = raw33528 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33528; decide +kernel
    rw [ha]
    exact (canonical33528 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2443 + difference 0 2) (sourceB2443 + difference 2 0) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3789) := by
    have ha : (tripleCharges (sourceA2443 + difference 0 2) (sourceB2443 + difference 2 0) sourceC2443) = raw33529 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33529; decide +kernel
    rw [ha]
    exact (canonical33529 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2443 + difference 0 3) (sourceB2443 + difference 3 0) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA2443 + difference 0 3) (sourceB2443 + difference 3 0) sourceC2443) = raw31032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw31032; decide +kernel
    rw [ha]
    exact (canonical31032 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2443 + difference 0 4) (sourceB2443 + difference 4 0) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA2443 + difference 0 4) (sourceB2443 + difference 4 0) sourceC2443) = raw33530 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33530; decide +kernel
    rw [ha]
    exact (canonical33530 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2443 + difference 0 5) (sourceB2443 + difference 5 0) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA2443 + difference 0 5) (sourceB2443 + difference 5 0) sourceC2443) = raw33531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33531; decide +kernel
    rw [ha]
    exact (canonical33531 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2443 + difference 1 0) (sourceB2443 + difference 0 1) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 827) := by
    have ha : (tripleCharges (sourceA2443 + difference 1 0) (sourceB2443 + difference 0 1) sourceC2443) = raw33532 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33532; decide +kernel
    rw [ha]
    exact (canonical33532 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2443 + difference 1 2) (sourceB2443 + difference 2 1) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1925) := by
    have ha : (tripleCharges (sourceA2443 + difference 1 2) (sourceB2443 + difference 2 1) sourceC2443) = raw33533 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33533; decide +kernel
    rw [ha]
    exact (canonical33533 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2443 + difference 1 3) (sourceB2443 + difference 3 1) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA2443 + difference 1 3) (sourceB2443 + difference 3 1) sourceC2443) = raw31037 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw31037; decide +kernel
    rw [ha]
    exact (canonical31037 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2443 + difference 1 4) (sourceB2443 + difference 4 1) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA2443 + difference 1 4) (sourceB2443 + difference 4 1) sourceC2443) = raw33534 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33534; decide +kernel
    rw [ha]
    exact (canonical33534 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2443 + difference 1 5) (sourceB2443 + difference 5 1) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA2443 + difference 1 5) (sourceB2443 + difference 5 1) sourceC2443) = raw33535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33535; decide +kernel
    rw [ha]
    exact (canonical33535 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2443 + difference 2 0) (sourceB2443 + difference 0 2) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 736) := by
    have ha : (tripleCharges (sourceA2443 + difference 2 0) (sourceB2443 + difference 0 2) sourceC2443) = raw33536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33536; decide +kernel
    rw [ha]
    exact (canonical33536 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2443 + difference 2 1) (sourceB2443 + difference 1 2) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1811) := by
    have ha : (tripleCharges (sourceA2443 + difference 2 1) (sourceB2443 + difference 1 2) sourceC2443) = raw33537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33537; decide +kernel
    rw [ha]
    exact (canonical33537 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2443 + difference 2 3) (sourceB2443 + difference 3 2) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA2443 + difference 2 3) (sourceB2443 + difference 3 2) sourceC2443) = raw31042 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw31042; decide +kernel
    rw [ha]
    exact (canonical31042 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2443 + difference 2 4) (sourceB2443 + difference 4 2) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA2443 + difference 2 4) (sourceB2443 + difference 4 2) sourceC2443) = raw33538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33538; decide +kernel
    rw [ha]
    exact (canonical33538 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2443 + difference 2 5) (sourceB2443 + difference 5 2) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2100) := by
    have ha : (tripleCharges (sourceA2443 + difference 2 5) (sourceB2443 + difference 5 2) sourceC2443) = raw33539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33539; decide +kernel
    rw [ha]
    exact (canonical33539 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2443 + difference 3 0) (sourceB2443 + difference 0 3) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 738) := by
    have ha : (tripleCharges (sourceA2443 + difference 3 0) (sourceB2443 + difference 0 3) sourceC2443) = raw33540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33540; decide +kernel
    rw [ha]
    exact (canonical33540 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2443 + difference 3 1) (sourceB2443 + difference 1 3) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1814) := by
    have ha : (tripleCharges (sourceA2443 + difference 3 1) (sourceB2443 + difference 1 3) sourceC2443) = raw33541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33541; decide +kernel
    rw [ha]
    exact (canonical33541 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2443 + difference 3 2) (sourceB2443 + difference 2 3) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1878) := by
    have ha : (tripleCharges (sourceA2443 + difference 3 2) (sourceB2443 + difference 2 3) sourceC2443) = raw33542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33542; decide +kernel
    rw [ha]
    exact (canonical33542 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2443 + difference 3 4) (sourceB2443 + difference 4 3) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA2443 + difference 3 4) (sourceB2443 + difference 4 3) sourceC2443) = raw33543 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33543; decide +kernel
    rw [ha]
    exact (canonical33543 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2443 + difference 3 5) (sourceB2443 + difference 5 3) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2101) := by
    have ha : (tripleCharges (sourceA2443 + difference 3 5) (sourceB2443 + difference 5 3) sourceC2443) = raw33544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33544; decide +kernel
    rw [ha]
    exact (canonical33544 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2443 + difference 4 0) (sourceB2443 + difference 0 4) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 738) := by
    have ha : (tripleCharges (sourceA2443 + difference 4 0) (sourceB2443 + difference 0 4) sourceC2443) = raw31044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw31044; decide +kernel
    rw [ha]
    exact (canonical31044 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2443 + difference 4 1) (sourceB2443 + difference 1 4) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1814) := by
    have ha : (tripleCharges (sourceA2443 + difference 4 1) (sourceB2443 + difference 1 4) sourceC2443) = raw31045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw31045; decide +kernel
    rw [ha]
    exact (canonical31045 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2443 + difference 4 2) (sourceB2443 + difference 2 4) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1878) := by
    have ha : (tripleCharges (sourceA2443 + difference 4 2) (sourceB2443 + difference 2 4) sourceC2443) = raw31046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw31046; decide +kernel
    rw [ha]
    exact (canonical31046 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2443 + difference 4 3) (sourceB2443 + difference 3 4) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA2443 + difference 4 3) (sourceB2443 + difference 3 4) sourceC2443) = raw33545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33545; decide +kernel
    rw [ha]
    exact (canonical33545 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2443 + difference 4 5) (sourceB2443 + difference 5 4) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2101) := by
    have ha : (tripleCharges (sourceA2443 + difference 4 5) (sourceB2443 + difference 5 4) sourceC2443) = raw31048 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw31048; decide +kernel
    rw [ha]
    exact (canonical31048 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2443 + difference 5 0) (sourceB2443 + difference 0 5) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 737) := by
    have ha : (tripleCharges (sourceA2443 + difference 5 0) (sourceB2443 + difference 0 5) sourceC2443) = raw33546 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33546; decide +kernel
    rw [ha]
    exact (canonical33546 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2443 + difference 5 1) (sourceB2443 + difference 1 5) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1812) := by
    have ha : (tripleCharges (sourceA2443 + difference 5 1) (sourceB2443 + difference 1 5) sourceC2443) = raw33547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33547; decide +kernel
    rw [ha]
    exact (canonical33547 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2443 + difference 5 2) (sourceB2443 + difference 2 5) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1877) := by
    have ha : (tripleCharges (sourceA2443 + difference 5 2) (sourceB2443 + difference 2 5) sourceC2443) = raw33548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33548; decide +kernel
    rw [ha]
    exact (canonical33548 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2443 + difference 5 3) (sourceB2443 + difference 3 5) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA2443 + difference 5 3) (sourceB2443 + difference 3 5) sourceC2443) = raw31058 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw31058; decide +kernel
    rw [ha]
    exact (canonical31058 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2443 + difference 5 4) (sourceB2443 + difference 4 5) sourceC2443) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA2443 + difference 5 4) (sourceB2443 + difference 4 5) sourceC2443) = raw33549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2443 sourceB2443 sourceC2443 difference raw33549; decide +kernel
    rw [ha]
    exact (canonical33549 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2443 sourceB2443 sourceC2443
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2443, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2444 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceB2444 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceC2444 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2444 : Integer.Sparse Master := [(Sum.inr 4469, 1), (Sum.inr 4471, 2), (Sum.inr 4477, 1), (Sum.inr 4489, 1), (Sum.inr 4805, 1), (Sum.inr 4813, 2), (Sum.inr 4818, 1), (Sum.inr 4826, 1), (Sum.inr 4838, 1), (Sum.inr 4839, 2), (Sum.inr 4852, 2), (Sum.inr 4854, 1), (Sum.inr 4866, 2), (Sum.inr 4867, 2), (Sum.inr 4870, 2), (Sum.inr 4880, 2), (Sum.inr 4882, 1), (Sum.inr 5172, 1), (Sum.inr 5187, 1), (Sum.inr 5204, 2), (Sum.inr 5205, 1)]

theorem sourceEq2444 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2444 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2444 + difference 0 1) (sourceB2444 + difference 1 0) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2444 + difference 0 1) (sourceB2444 + difference 1 0) sourceC2444) = raw32487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw32487; decide +kernel
    rw [ha]
    exact (canonical32487 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2444 + difference 0 2) (sourceB2444 + difference 2 0) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA2444 + difference 0 2) (sourceB2444 + difference 2 0) sourceC2444) = raw32231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw32231; decide +kernel
    rw [ha]
    exact (canonical32231 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2444 + difference 0 3) (sourceB2444 + difference 3 0) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2444 + difference 0 3) (sourceB2444 + difference 3 0) sourceC2444) = raw32232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw32232; decide +kernel
    rw [ha]
    exact (canonical32232 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2444 + difference 0 4) (sourceB2444 + difference 4 0) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2444 + difference 0 4) (sourceB2444 + difference 4 0) sourceC2444) = raw32233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw32233; decide +kernel
    rw [ha]
    exact (canonical32233 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2444 + difference 0 5) (sourceB2444 + difference 5 0) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA2444 + difference 0 5) (sourceB2444 + difference 5 0) sourceC2444) = raw32234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw32234; decide +kernel
    rw [ha]
    exact (canonical32234 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2444 + difference 1 0) (sourceB2444 + difference 0 1) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4477) := by
    have ha : (tripleCharges (sourceA2444 + difference 1 0) (sourceB2444 + difference 0 1) sourceC2444) = raw33550 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33550; decide +kernel
    rw [ha]
    exact (canonical33550 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2444 + difference 1 2) (sourceB2444 + difference 2 1) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4818) := by
    have ha : (tripleCharges (sourceA2444 + difference 1 2) (sourceB2444 + difference 2 1) sourceC2444) = raw33551 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33551; decide +kernel
    rw [ha]
    exact (canonical33551 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2444 + difference 1 3) (sourceB2444 + difference 3 1) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA2444 + difference 1 3) (sourceB2444 + difference 3 1) sourceC2444) = raw33552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33552; decide +kernel
    rw [ha]
    exact (canonical33552 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2444 + difference 1 4) (sourceB2444 + difference 4 1) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA2444 + difference 1 4) (sourceB2444 + difference 4 1) sourceC2444) = raw33553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33553; decide +kernel
    rw [ha]
    exact (canonical33553 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2444 + difference 1 5) (sourceB2444 + difference 5 1) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4882) := by
    have ha : (tripleCharges (sourceA2444 + difference 1 5) (sourceB2444 + difference 5 1) sourceC2444) = raw33554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33554; decide +kernel
    rw [ha]
    exact (canonical33554 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2444 + difference 2 0) (sourceB2444 + difference 0 2) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4469) := by
    have ha : (tripleCharges (sourceA2444 + difference 2 0) (sourceB2444 + difference 0 2) sourceC2444) = raw33555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33555; decide +kernel
    rw [ha]
    exact (canonical33555 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2444 + difference 2 1) (sourceB2444 + difference 1 2) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2444 + difference 2 1) (sourceB2444 + difference 1 2) sourceC2444) = raw32235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw32235; decide +kernel
    rw [ha]
    exact (canonical32235 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2444 + difference 2 3) (sourceB2444 + difference 3 2) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA2444 + difference 2 3) (sourceB2444 + difference 3 2) sourceC2444) = raw32480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw32480; decide +kernel
    rw [ha]
    exact (canonical32480 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2444 + difference 2 4) (sourceB2444 + difference 4 2) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA2444 + difference 2 4) (sourceB2444 + difference 4 2) sourceC2444) = raw33556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33556; decide +kernel
    rw [ha]
    exact (canonical33556 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2444 + difference 2 5) (sourceB2444 + difference 5 2) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4854) := by
    have ha : (tripleCharges (sourceA2444 + difference 2 5) (sourceB2444 + difference 5 2) sourceC2444) = raw33557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33557; decide +kernel
    rw [ha]
    exact (canonical33557 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2444 + difference 3 0) (sourceB2444 + difference 0 3) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4471) := by
    have ha : (tripleCharges (sourceA2444 + difference 3 0) (sourceB2444 + difference 0 3) sourceC2444) = raw33558 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33558; decide +kernel
    rw [ha]
    exact (canonical33558 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2444 + difference 3 1) (sourceB2444 + difference 1 3) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2444 + difference 3 1) (sourceB2444 + difference 1 3) sourceC2444) = raw32240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw32240; decide +kernel
    rw [ha]
    exact (canonical32240 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2444 + difference 3 2) (sourceB2444 + difference 2 3) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4813) := by
    have ha : (tripleCharges (sourceA2444 + difference 3 2) (sourceB2444 + difference 2 3) sourceC2444) = raw33559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33559; decide +kernel
    rw [ha]
    exact (canonical33559 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2444 + difference 3 4) (sourceB2444 + difference 4 3) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA2444 + difference 3 4) (sourceB2444 + difference 4 3) sourceC2444) = raw33560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33560; decide +kernel
    rw [ha]
    exact (canonical33560 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2444 + difference 3 5) (sourceB2444 + difference 5 3) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4870) := by
    have ha : (tripleCharges (sourceA2444 + difference 3 5) (sourceB2444 + difference 5 3) sourceC2444) = raw33561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33561; decide +kernel
    rw [ha]
    exact (canonical33561 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2444 + difference 4 0) (sourceB2444 + difference 0 4) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4471) := by
    have ha : (tripleCharges (sourceA2444 + difference 4 0) (sourceB2444 + difference 0 4) sourceC2444) = raw33562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33562; decide +kernel
    rw [ha]
    exact (canonical33562 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2444 + difference 4 1) (sourceB2444 + difference 1 4) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2444 + difference 4 1) (sourceB2444 + difference 1 4) sourceC2444) = raw32245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw32245; decide +kernel
    rw [ha]
    exact (canonical32245 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2444 + difference 4 2) (sourceB2444 + difference 2 4) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4813) := by
    have ha : (tripleCharges (sourceA2444 + difference 4 2) (sourceB2444 + difference 2 4) sourceC2444) = raw33563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33563; decide +kernel
    rw [ha]
    exact (canonical33563 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2444 + difference 4 3) (sourceB2444 + difference 3 4) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA2444 + difference 4 3) (sourceB2444 + difference 3 4) sourceC2444) = raw33564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33564; decide +kernel
    rw [ha]
    exact (canonical33564 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2444 + difference 4 5) (sourceB2444 + difference 5 4) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4870) := by
    have ha : (tripleCharges (sourceA2444 + difference 4 5) (sourceB2444 + difference 5 4) sourceC2444) = raw33565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33565; decide +kernel
    rw [ha]
    exact (canonical33565 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2444 + difference 5 0) (sourceB2444 + difference 0 5) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA2444 + difference 5 0) (sourceB2444 + difference 0 5) sourceC2444) = raw33566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33566; decide +kernel
    rw [ha]
    exact (canonical33566 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2444 + difference 5 1) (sourceB2444 + difference 1 5) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2444 + difference 5 1) (sourceB2444 + difference 1 5) sourceC2444) = raw32250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw32250; decide +kernel
    rw [ha]
    exact (canonical32250 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2444 + difference 5 2) (sourceB2444 + difference 2 5) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA2444 + difference 5 2) (sourceB2444 + difference 2 5) sourceC2444) = raw32902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw32902; decide +kernel
    rw [ha]
    exact (canonical32902 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2444 + difference 5 3) (sourceB2444 + difference 3 5) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2444 + difference 5 3) (sourceB2444 + difference 3 5) sourceC2444) = raw33567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33567; decide +kernel
    rw [ha]
    exact (canonical33567 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2444 + difference 5 4) (sourceB2444 + difference 4 5) sourceC2444) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2444 + difference 5 4) (sourceB2444 + difference 4 5) sourceC2444) = raw33568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2444 sourceB2444 sourceC2444 difference raw33568; decide +kernel
    rw [ha]
    exact (canonical33568 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2444 sourceB2444 sourceC2444
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2444, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2445 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2445 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2445 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceForm2445 : Integer.Sparse Master := [(Sum.inr 4364, 1), (Sum.inr 4367, 1), (Sum.inr 4369, 1), (Sum.inr 4372, 1), (Sum.inr 4458, 1), (Sum.inr 4696, 1), (Sum.inr 4699, 1), (Sum.inr 4701, 1), (Sum.inr 4703, 1), (Sum.inr 4772, 1), (Sum.inr 4774, 1), (Sum.inr 4775, 1), (Sum.inr 4802, 1), (Sum.inr 4851, 1), (Sum.inr 4853, 1), (Sum.inr 4856, 1), (Sum.inr 4864, 1), (Sum.inr 4866, 2), (Sum.inr 4869, 1), (Sum.inr 4871, 1), (Sum.inr 4875, 1), (Sum.inr 4888, 1), (Sum.inr 4893, 1), (Sum.inr 4895, 1), (Sum.inr 5255, 1), (Sum.inr 5288, 1), (Sum.inr 5289, 1), (Sum.inr 5290, 1), (Sum.inr 5304, 1)]

theorem sourceEq2445 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2445 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2445 + difference 0 1) (sourceB2445 + difference 1 0) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5288) := by
    have ha : (tripleCharges (sourceA2445 + difference 0 1) (sourceB2445 + difference 1 0) sourceC2445) = raw33569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33569; decide +kernel
    rw [ha]
    exact (canonical33569 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2445 + difference 0 2) (sourceB2445 + difference 2 0) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA2445 + difference 0 2) (sourceB2445 + difference 2 0) sourceC2445) = raw33570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33570; decide +kernel
    rw [ha]
    exact (canonical33570 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2445 + difference 0 3) (sourceB2445 + difference 3 0) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA2445 + difference 0 3) (sourceB2445 + difference 3 0) sourceC2445) = raw33571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33571; decide +kernel
    rw [ha]
    exact (canonical33571 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2445 + difference 0 4) (sourceB2445 + difference 4 0) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA2445 + difference 0 4) (sourceB2445 + difference 4 0) sourceC2445) = raw33572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33572; decide +kernel
    rw [ha]
    exact (canonical33572 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2445 + difference 0 5) (sourceB2445 + difference 5 0) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA2445 + difference 0 5) (sourceB2445 + difference 5 0) sourceC2445) = raw33573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33573; decide +kernel
    rw [ha]
    exact (canonical33573 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2445 + difference 1 0) (sourceB2445 + difference 0 1) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA2445 + difference 1 0) (sourceB2445 + difference 0 1) sourceC2445) = raw33574 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33574; decide +kernel
    rw [ha]
    exact (canonical33574 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2445 + difference 1 2) (sourceB2445 + difference 2 1) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2445 + difference 1 2) (sourceB2445 + difference 2 1) sourceC2445) = raw25136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw25136; decide +kernel
    rw [ha]
    exact (canonical25136 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2445 + difference 1 3) (sourceB2445 + difference 3 1) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2445 + difference 1 3) (sourceB2445 + difference 3 1) sourceC2445) = raw25137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw25137; decide +kernel
    rw [ha]
    exact (canonical25137 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2445 + difference 1 4) (sourceB2445 + difference 4 1) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2445 + difference 1 4) (sourceB2445 + difference 4 1) sourceC2445) = raw25138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw25138; decide +kernel
    rw [ha]
    exact (canonical25138 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2445 + difference 1 5) (sourceB2445 + difference 5 1) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA2445 + difference 1 5) (sourceB2445 + difference 5 1) sourceC2445) = raw25139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw25139; decide +kernel
    rw [ha]
    exact (canonical25139 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2445 + difference 2 0) (sourceB2445 + difference 0 2) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4364) := by
    have ha : (tripleCharges (sourceA2445 + difference 2 0) (sourceB2445 + difference 0 2) sourceC2445) = raw25146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw25146; decide +kernel
    rw [ha]
    exact (canonical25146 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2445 + difference 2 1) (sourceB2445 + difference 1 2) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4696) := by
    have ha : (tripleCharges (sourceA2445 + difference 2 1) (sourceB2445 + difference 1 2) sourceC2445) = raw33575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33575; decide +kernel
    rw [ha]
    exact (canonical33575 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2445 + difference 2 3) (sourceB2445 + difference 3 2) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA2445 + difference 2 3) (sourceB2445 + difference 3 2) sourceC2445) = raw33576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33576; decide +kernel
    rw [ha]
    exact (canonical33576 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2445 + difference 2 4) (sourceB2445 + difference 4 2) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2445 + difference 2 4) (sourceB2445 + difference 4 2) sourceC2445) = raw33577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33577; decide +kernel
    rw [ha]
    exact (canonical33577 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2445 + difference 2 5) (sourceB2445 + difference 5 2) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA2445 + difference 2 5) (sourceB2445 + difference 5 2) sourceC2445) = raw33578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33578; decide +kernel
    rw [ha]
    exact (canonical33578 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2445 + difference 3 0) (sourceB2445 + difference 0 3) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4369) := by
    have ha : (tripleCharges (sourceA2445 + difference 3 0) (sourceB2445 + difference 0 3) sourceC2445) = raw25151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw25151; decide +kernel
    rw [ha]
    exact (canonical25151 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2445 + difference 3 1) (sourceB2445 + difference 1 3) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4701) := by
    have ha : (tripleCharges (sourceA2445 + difference 3 1) (sourceB2445 + difference 1 3) sourceC2445) = raw33579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33579; decide +kernel
    rw [ha]
    exact (canonical33579 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2445 + difference 3 2) (sourceB2445 + difference 2 3) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4774) := by
    have ha : (tripleCharges (sourceA2445 + difference 3 2) (sourceB2445 + difference 2 3) sourceC2445) = raw33580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33580; decide +kernel
    rw [ha]
    exact (canonical33580 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2445 + difference 3 4) (sourceB2445 + difference 4 3) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA2445 + difference 3 4) (sourceB2445 + difference 4 3) sourceC2445) = raw33581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33581; decide +kernel
    rw [ha]
    exact (canonical33581 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2445 + difference 3 5) (sourceB2445 + difference 5 3) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2445 + difference 3 5) (sourceB2445 + difference 5 3) sourceC2445) = raw33582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33582; decide +kernel
    rw [ha]
    exact (canonical33582 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2445 + difference 4 0) (sourceB2445 + difference 0 4) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4372) := by
    have ha : (tripleCharges (sourceA2445 + difference 4 0) (sourceB2445 + difference 0 4) sourceC2445) = raw25156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw25156; decide +kernel
    rw [ha]
    exact (canonical25156 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2445 + difference 4 1) (sourceB2445 + difference 1 4) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4703) := by
    have ha : (tripleCharges (sourceA2445 + difference 4 1) (sourceB2445 + difference 1 4) sourceC2445) = raw33583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33583; decide +kernel
    rw [ha]
    exact (canonical33583 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2445 + difference 4 2) (sourceB2445 + difference 2 4) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4775) := by
    have ha : (tripleCharges (sourceA2445 + difference 4 2) (sourceB2445 + difference 2 4) sourceC2445) = raw33584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33584; decide +kernel
    rw [ha]
    exact (canonical33584 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2445 + difference 4 3) (sourceB2445 + difference 3 4) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2445 + difference 4 3) (sourceB2445 + difference 3 4) sourceC2445) = raw33585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33585; decide +kernel
    rw [ha]
    exact (canonical33585 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2445 + difference 4 5) (sourceB2445 + difference 5 4) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2445 + difference 4 5) (sourceB2445 + difference 5 4) sourceC2445) = raw33586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33586; decide +kernel
    rw [ha]
    exact (canonical33586 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2445 + difference 5 0) (sourceB2445 + difference 0 5) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA2445 + difference 5 0) (sourceB2445 + difference 0 5) sourceC2445) = raw25161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw25161; decide +kernel
    rw [ha]
    exact (canonical25161 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2445 + difference 5 1) (sourceB2445 + difference 1 5) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4699) := by
    have ha : (tripleCharges (sourceA2445 + difference 5 1) (sourceB2445 + difference 1 5) sourceC2445) = raw33587 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33587; decide +kernel
    rw [ha]
    exact (canonical33587 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2445 + difference 5 2) (sourceB2445 + difference 2 5) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4772) := by
    have ha : (tripleCharges (sourceA2445 + difference 5 2) (sourceB2445 + difference 2 5) sourceC2445) = raw33588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33588; decide +kernel
    rw [ha]
    exact (canonical33588 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2445 + difference 5 3) (sourceB2445 + difference 3 5) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA2445 + difference 5 3) (sourceB2445 + difference 3 5) sourceC2445) = raw33589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33589; decide +kernel
    rw [ha]
    exact (canonical33589 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2445 + difference 5 4) (sourceB2445 + difference 4 5) sourceC2445) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2445 + difference 5 4) (sourceB2445 + difference 4 5) sourceC2445) = raw33590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2445 sourceB2445 sourceC2445 difference raw33590; decide +kernel
    rw [ha]
    exact (canonical33590 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2445 sourceB2445 sourceC2445
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2445, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2446 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2446 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2446 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceForm2446 : Integer.Sparse Master := [(Sum.inr 1703, 1), (Sum.inr 1720, 1), (Sum.inr 1721, 1), (Sum.inr 1724, 1), (Sum.inr 1734, 1), (Sum.inr 2198, 1), (Sum.inr 2199, 1), (Sum.inr 2202, 1), (Sum.inr 2211, 1), (Sum.inr 2238, 1), (Sum.inr 2240, 1), (Sum.inr 2241, 1), (Sum.inr 2256, 1), (Sum.inr 2257, 1), (Sum.inr 2259, 1), (Sum.inr 2260, 2), (Sum.inr 2262, 1), (Sum.inr 2263, 1), (Sum.inr 2272, 1), (Sum.inr 2274, 1), (Sum.inr 2275, 1), (Sum.inr 2287, 1), (Sum.inr 2288, 1), (Sum.inr 2291, 1), (Sum.inr 2718, 1), (Sum.inr 2760, 1), (Sum.inr 2763, 1), (Sum.inr 2764, 1), (Sum.inr 2782, 1)]

theorem sourceEq2446 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2446 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2446 + difference 0 1) (sourceB2446 + difference 1 0) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2760) := by
    have ha : (tripleCharges (sourceA2446 + difference 0 1) (sourceB2446 + difference 1 0) sourceC2446) = raw33591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33591; decide +kernel
    rw [ha]
    exact (canonical33591 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2446 + difference 0 2) (sourceB2446 + difference 2 0) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA2446 + difference 0 2) (sourceB2446 + difference 2 0) sourceC2446) = raw33592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33592; decide +kernel
    rw [ha]
    exact (canonical33592 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2446 + difference 0 3) (sourceB2446 + difference 3 0) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA2446 + difference 0 3) (sourceB2446 + difference 3 0) sourceC2446) = raw33593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33593; decide +kernel
    rw [ha]
    exact (canonical33593 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2446 + difference 0 4) (sourceB2446 + difference 4 0) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA2446 + difference 0 4) (sourceB2446 + difference 4 0) sourceC2446) = raw33594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33594; decide +kernel
    rw [ha]
    exact (canonical33594 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2446 + difference 0 5) (sourceB2446 + difference 5 0) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA2446 + difference 0 5) (sourceB2446 + difference 5 0) sourceC2446) = raw33595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33595; decide +kernel
    rw [ha]
    exact (canonical33595 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2446 + difference 1 0) (sourceB2446 + difference 0 1) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA2446 + difference 1 0) (sourceB2446 + difference 0 1) sourceC2446) = raw33596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33596; decide +kernel
    rw [ha]
    exact (canonical33596 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2446 + difference 1 2) (sourceB2446 + difference 2 1) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA2446 + difference 1 2) (sourceB2446 + difference 2 1) sourceC2446) = raw25196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25196; decide +kernel
    rw [ha]
    exact (canonical25196 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2446 + difference 1 3) (sourceB2446 + difference 3 1) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA2446 + difference 1 3) (sourceB2446 + difference 3 1) sourceC2446) = raw25197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25197; decide +kernel
    rw [ha]
    exact (canonical25197 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2446 + difference 1 4) (sourceB2446 + difference 4 1) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA2446 + difference 1 4) (sourceB2446 + difference 4 1) sourceC2446) = raw25198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25198; decide +kernel
    rw [ha]
    exact (canonical25198 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2446 + difference 1 5) (sourceB2446 + difference 5 1) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA2446 + difference 1 5) (sourceB2446 + difference 5 1) sourceC2446) = raw25199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25199; decide +kernel
    rw [ha]
    exact (canonical25199 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2446 + difference 2 0) (sourceB2446 + difference 0 2) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1703) := by
    have ha : (tripleCharges (sourceA2446 + difference 2 0) (sourceB2446 + difference 0 2) sourceC2446) = raw25206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25206; decide +kernel
    rw [ha]
    exact (canonical25206 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2446 + difference 2 1) (sourceB2446 + difference 1 2) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2238) := by
    have ha : (tripleCharges (sourceA2446 + difference 2 1) (sourceB2446 + difference 1 2) sourceC2446) = raw33597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33597; decide +kernel
    rw [ha]
    exact (canonical33597 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2446 + difference 2 3) (sourceB2446 + difference 3 2) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA2446 + difference 2 3) (sourceB2446 + difference 3 2) sourceC2446) = raw33598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33598; decide +kernel
    rw [ha]
    exact (canonical33598 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2446 + difference 2 4) (sourceB2446 + difference 4 2) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2446 + difference 2 4) (sourceB2446 + difference 4 2) sourceC2446) = raw33599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33599; decide +kernel
    rw [ha]
    exact (canonical33599 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2446 + difference 2 5) (sourceB2446 + difference 5 2) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA2446 + difference 2 5) (sourceB2446 + difference 5 2) sourceC2446) = raw33600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33600; decide +kernel
    rw [ha]
    exact (canonical33600 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2446 + difference 3 0) (sourceB2446 + difference 0 3) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA2446 + difference 3 0) (sourceB2446 + difference 0 3) sourceC2446) = raw25211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25211; decide +kernel
    rw [ha]
    exact (canonical25211 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2446 + difference 3 1) (sourceB2446 + difference 1 3) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2257) := by
    have ha : (tripleCharges (sourceA2446 + difference 3 1) (sourceB2446 + difference 1 3) sourceC2446) = raw33601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33601; decide +kernel
    rw [ha]
    exact (canonical33601 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2446 + difference 3 2) (sourceB2446 + difference 2 3) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2199) := by
    have ha : (tripleCharges (sourceA2446 + difference 3 2) (sourceB2446 + difference 2 3) sourceC2446) = raw33602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33602; decide +kernel
    rw [ha]
    exact (canonical33602 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2446 + difference 3 4) (sourceB2446 + difference 4 3) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA2446 + difference 3 4) (sourceB2446 + difference 4 3) sourceC2446) = raw33603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33603; decide +kernel
    rw [ha]
    exact (canonical33603 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2446 + difference 3 5) (sourceB2446 + difference 5 3) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2446 + difference 3 5) (sourceB2446 + difference 5 3) sourceC2446) = raw33604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33604; decide +kernel
    rw [ha]
    exact (canonical33604 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2446 + difference 4 0) (sourceB2446 + difference 0 4) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA2446 + difference 4 0) (sourceB2446 + difference 0 4) sourceC2446) = raw25216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25216; decide +kernel
    rw [ha]
    exact (canonical25216 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2446 + difference 4 1) (sourceB2446 + difference 1 4) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2272) := by
    have ha : (tripleCharges (sourceA2446 + difference 4 1) (sourceB2446 + difference 1 4) sourceC2446) = raw33605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33605; decide +kernel
    rw [ha]
    exact (canonical33605 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2446 + difference 4 2) (sourceB2446 + difference 2 4) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2211) := by
    have ha : (tripleCharges (sourceA2446 + difference 4 2) (sourceB2446 + difference 2 4) sourceC2446) = raw33606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33606; decide +kernel
    rw [ha]
    exact (canonical33606 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2446 + difference 4 3) (sourceB2446 + difference 3 4) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2446 + difference 4 3) (sourceB2446 + difference 3 4) sourceC2446) = raw33607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33607; decide +kernel
    rw [ha]
    exact (canonical33607 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2446 + difference 4 5) (sourceB2446 + difference 5 4) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA2446 + difference 4 5) (sourceB2446 + difference 5 4) sourceC2446) = raw33608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33608; decide +kernel
    rw [ha]
    exact (canonical33608 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2446 + difference 5 0) (sourceB2446 + difference 0 5) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA2446 + difference 5 0) (sourceB2446 + difference 0 5) sourceC2446) = raw25221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25221; decide +kernel
    rw [ha]
    exact (canonical25221 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2446 + difference 5 1) (sourceB2446 + difference 1 5) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2256) := by
    have ha : (tripleCharges (sourceA2446 + difference 5 1) (sourceB2446 + difference 1 5) sourceC2446) = raw33609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33609; decide +kernel
    rw [ha]
    exact (canonical33609 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2446 + difference 5 2) (sourceB2446 + difference 2 5) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2198) := by
    have ha : (tripleCharges (sourceA2446 + difference 5 2) (sourceB2446 + difference 2 5) sourceC2446) = raw33610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33610; decide +kernel
    rw [ha]
    exact (canonical33610 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2446 + difference 5 3) (sourceB2446 + difference 3 5) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA2446 + difference 5 3) (sourceB2446 + difference 3 5) sourceC2446) = raw33611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33611; decide +kernel
    rw [ha]
    exact (canonical33611 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2446 + difference 5 4) (sourceB2446 + difference 4 5) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA2446 + difference 5 4) (sourceB2446 + difference 4 5) sourceC2446) = raw33612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33612; decide +kernel
    rw [ha]
    exact (canonical33612 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2446 sourceB2446 sourceC2446
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2446, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2447 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2447 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2447 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceForm2447 : Integer.Sparse Master := [(Sum.inr 1822, 1), (Sum.inr 1825, 1), (Sum.inr 1827, 1), (Sum.inr 1829, 1), (Sum.inr 2107, 1), (Sum.inr 3096, 1), (Sum.inr 4083, -1)]

theorem sourceEq2447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2447 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2447 + difference 0 1) (sourceB2447 + difference 1 0) sourceC2447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3096) := by
    have ha : (tripleCharges (sourceA2447 + difference 0 1) (sourceB2447 + difference 1 0) sourceC2447) = raw33613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2447 sourceB2447 sourceC2447 difference raw33613; decide +kernel
    rw [ha]
    exact (canonical33613 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2447 + difference 1 1) (sourceB2447 + difference 1 1) sourceC2447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2447 + difference 1 1) (sourceB2447 + difference 1 1) sourceC2447) = raw25236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2447 sourceB2447 sourceC2447 difference raw25236; decide +kernel
    rw [ha]
    exact (canonical25236 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2447 + difference 2 1) (sourceB2447 + difference 1 2) sourceC2447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1822) := by
    have ha : (tripleCharges (sourceA2447 + difference 2 1) (sourceB2447 + difference 1 2) sourceC2447) = raw33614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2447 sourceB2447 sourceC2447 difference raw33614; decide +kernel
    rw [ha]
    exact (canonical33614 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2447 + difference 3 1) (sourceB2447 + difference 1 3) sourceC2447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1827) := by
    have ha : (tripleCharges (sourceA2447 + difference 3 1) (sourceB2447 + difference 1 3) sourceC2447) = raw33615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2447 sourceB2447 sourceC2447 difference raw33615; decide +kernel
    rw [ha]
    exact (canonical33615 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2447 + difference 4 1) (sourceB2447 + difference 1 4) sourceC2447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1829) := by
    have ha : (tripleCharges (sourceA2447 + difference 4 1) (sourceB2447 + difference 1 4) sourceC2447) = raw29343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2447 sourceB2447 sourceC2447 difference raw29343; decide +kernel
    rw [ha]
    exact (canonical29343 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2447 + difference 5 1) (sourceB2447 + difference 1 5) sourceC2447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1825) := by
    have ha : (tripleCharges (sourceA2447 + difference 5 1) (sourceB2447 + difference 1 5) sourceC2447) = raw27399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2447 sourceB2447 sourceC2447 difference raw27399; decide +kernel
    rw [ha]
    exact (canonical27399 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2447 + sourceB2447) sourceC2447) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2447 + sourceB2447) sourceC2447) = raw25231 := by
      apply Matrix.ext; unfold doubleCharges sourceA2447 sourceB2447 sourceC2447 raw25231; decide +kernel
    rw [ha]
    exact (canonical25231 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2447 sourceB2447 sourceC2447
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2447, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2448 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2448 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2448 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceForm2448 : Integer.Sparse Master := [(Sum.inr 4232, 1), (Sum.inr 4233, 1), (Sum.inr 4234, 1), (Sum.inr 4239, 1), (Sum.inr 4268, 1), (Sum.inr 4679, 1), (Sum.inr 4681, 1), (Sum.inr 4684, 1), (Sum.inr 4689, 1), (Sum.inr 4721, 1), (Sum.inr 4722, 1), (Sum.inr 4725, 1), (Sum.inr 4740, 1), (Sum.inr 4826, 1), (Sum.inr 4827, 1), (Sum.inr 4828, 1), (Sum.inr 4839, 1), (Sum.inr 4864, 1), (Sum.inr 4865, 1), (Sum.inr 4866, 2), (Sum.inr 4868, 1), (Sum.inr 4875, 1), (Sum.inr 4889, 1), (Sum.inr 4896, 1), (Sum.inr 5388, 1), (Sum.inr 5401, 1), (Sum.inr 5438, 1), (Sum.inr 5450, 1), (Sum.inr 5451, 1)]

theorem sourceEq2448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2448 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2448 + difference 0 1) (sourceB2448 + difference 1 0) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2448 + difference 0 1) (sourceB2448 + difference 1 0) sourceC2448) = raw16289 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw16289; decide +kernel
    rw [ha]
    exact (canonical16289 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2448 + difference 0 2) (sourceB2448 + difference 2 0) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA2448 + difference 0 2) (sourceB2448 + difference 2 0) sourceC2448) = raw16290 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw16290; decide +kernel
    rw [ha]
    exact (canonical16290 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2448 + difference 0 3) (sourceB2448 + difference 3 0) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2448 + difference 0 3) (sourceB2448 + difference 3 0) sourceC2448) = raw10900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10900; decide +kernel
    rw [ha]
    exact (canonical10900 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2448 + difference 0 4) (sourceB2448 + difference 4 0) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2448 + difference 0 4) (sourceB2448 + difference 4 0) sourceC2448) = raw16291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw16291; decide +kernel
    rw [ha]
    exact (canonical16291 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2448 + difference 0 5) (sourceB2448 + difference 5 0) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2448 + difference 0 5) (sourceB2448 + difference 5 0) sourceC2448) = raw16292 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw16292; decide +kernel
    rw [ha]
    exact (canonical16292 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2448 + difference 1 0) (sourceB2448 + difference 0 1) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA2448 + difference 1 0) (sourceB2448 + difference 0 1) sourceC2448) = raw10915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10915; decide +kernel
    rw [ha]
    exact (canonical10915 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2448 + difference 1 2) (sourceB2448 + difference 2 1) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2448 + difference 1 2) (sourceB2448 + difference 2 1) sourceC2448) = raw10917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10917; decide +kernel
    rw [ha]
    exact (canonical10917 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2448 + difference 1 3) (sourceB2448 + difference 3 1) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA2448 + difference 1 3) (sourceB2448 + difference 3 1) sourceC2448) = raw16284 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw16284; decide +kernel
    rw [ha]
    exact (canonical16284 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2448 + difference 1 4) (sourceB2448 + difference 4 1) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2448 + difference 1 4) (sourceB2448 + difference 4 1) sourceC2448) = raw10918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10918; decide +kernel
    rw [ha]
    exact (canonical10918 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2448 + difference 1 5) (sourceB2448 + difference 5 1) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2448 + difference 1 5) (sourceB2448 + difference 5 1) sourceC2448) = raw10919 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10919; decide +kernel
    rw [ha]
    exact (canonical10919 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2448 + difference 2 0) (sourceB2448 + difference 0 2) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4232) := by
    have ha : (tripleCharges (sourceA2448 + difference 2 0) (sourceB2448 + difference 0 2) sourceC2448) = raw33616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33616; decide +kernel
    rw [ha]
    exact (canonical33616 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2448 + difference 2 1) (sourceB2448 + difference 1 2) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2448 + difference 2 1) (sourceB2448 + difference 1 2) sourceC2448) = raw33617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33617; decide +kernel
    rw [ha]
    exact (canonical33617 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2448 + difference 2 3) (sourceB2448 + difference 3 2) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2448 + difference 2 3) (sourceB2448 + difference 3 2) sourceC2448) = raw10911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10911; decide +kernel
    rw [ha]
    exact (canonical10911 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2448 + difference 2 4) (sourceB2448 + difference 4 2) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA2448 + difference 2 4) (sourceB2448 + difference 4 2) sourceC2448) = raw33618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33618; decide +kernel
    rw [ha]
    exact (canonical33618 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2448 + difference 2 5) (sourceB2448 + difference 5 2) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA2448 + difference 2 5) (sourceB2448 + difference 5 2) sourceC2448) = raw33619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33619; decide +kernel
    rw [ha]
    exact (canonical33619 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2448 + difference 3 0) (sourceB2448 + difference 0 3) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4234) := by
    have ha : (tripleCharges (sourceA2448 + difference 3 0) (sourceB2448 + difference 0 3) sourceC2448) = raw33620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33620; decide +kernel
    rw [ha]
    exact (canonical33620 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2448 + difference 3 1) (sourceB2448 + difference 1 3) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2448 + difference 3 1) (sourceB2448 + difference 1 3) sourceC2448) = raw33621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33621; decide +kernel
    rw [ha]
    exact (canonical33621 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2448 + difference 3 2) (sourceB2448 + difference 2 3) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4722) := by
    have ha : (tripleCharges (sourceA2448 + difference 3 2) (sourceB2448 + difference 2 3) sourceC2448) = raw33622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33622; decide +kernel
    rw [ha]
    exact (canonical33622 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2448 + difference 3 4) (sourceB2448 + difference 4 3) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2448 + difference 3 4) (sourceB2448 + difference 4 3) sourceC2448) = raw33623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33623; decide +kernel
    rw [ha]
    exact (canonical33623 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2448 + difference 3 5) (sourceB2448 + difference 5 3) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2448 + difference 3 5) (sourceB2448 + difference 5 3) sourceC2448) = raw33624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33624; decide +kernel
    rw [ha]
    exact (canonical33624 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2448 + difference 4 0) (sourceB2448 + difference 0 4) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4239) := by
    have ha : (tripleCharges (sourceA2448 + difference 4 0) (sourceB2448 + difference 0 4) sourceC2448) = raw31204 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw31204; decide +kernel
    rw [ha]
    exact (canonical31204 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2448 + difference 4 1) (sourceB2448 + difference 1 4) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4689) := by
    have ha : (tripleCharges (sourceA2448 + difference 4 1) (sourceB2448 + difference 1 4) sourceC2448) = raw31205 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw31205; decide +kernel
    rw [ha]
    exact (canonical31205 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2448 + difference 4 2) (sourceB2448 + difference 2 4) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4725) := by
    have ha : (tripleCharges (sourceA2448 + difference 4 2) (sourceB2448 + difference 2 4) sourceC2448) = raw31206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw31206; decide +kernel
    rw [ha]
    exact (canonical31206 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2448 + difference 4 3) (sourceB2448 + difference 3 4) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA2448 + difference 4 3) (sourceB2448 + difference 3 4) sourceC2448) = raw10921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10921; decide +kernel
    rw [ha]
    exact (canonical10921 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2448 + difference 4 5) (sourceB2448 + difference 5 4) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2448 + difference 4 5) (sourceB2448 + difference 5 4) sourceC2448) = raw31207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw31207; decide +kernel
    rw [ha]
    exact (canonical31207 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2448 + difference 5 0) (sourceB2448 + difference 0 5) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4233) := by
    have ha : (tripleCharges (sourceA2448 + difference 5 0) (sourceB2448 + difference 0 5) sourceC2448) = raw33625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33625; decide +kernel
    rw [ha]
    exact (canonical33625 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2448 + difference 5 1) (sourceB2448 + difference 1 5) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2448 + difference 5 1) (sourceB2448 + difference 1 5) sourceC2448) = raw33626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33626; decide +kernel
    rw [ha]
    exact (canonical33626 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2448 + difference 5 2) (sourceB2448 + difference 2 5) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4721) := by
    have ha : (tripleCharges (sourceA2448 + difference 5 2) (sourceB2448 + difference 2 5) sourceC2448) = raw33627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33627; decide +kernel
    rw [ha]
    exact (canonical33627 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2448 + difference 5 3) (sourceB2448 + difference 3 5) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2448 + difference 5 3) (sourceB2448 + difference 3 5) sourceC2448) = raw10926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10926; decide +kernel
    rw [ha]
    exact (canonical10926 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2448 + difference 5 4) (sourceB2448 + difference 4 5) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA2448 + difference 5 4) (sourceB2448 + difference 4 5) sourceC2448) = raw33628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33628; decide +kernel
    rw [ha]
    exact (canonical33628 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2448 sourceB2448 sourceC2448
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2448, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2449 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2449 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2449 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceForm2449 : Integer.Sparse Master := [(Sum.inr 732, 1), (Sum.inr 733, 1), (Sum.inr 734, 1), (Sum.inr 739, 1), (Sum.inr 824, 1), (Sum.inr 1805, 1), (Sum.inr 1807, 1), (Sum.inr 1810, 1), (Sum.inr 1815, 1), (Sum.inr 1875, 1), (Sum.inr 1876, 1), (Sum.inr 1879, 1), (Sum.inr 1922, 1), (Sum.inr 2077, 1), (Sum.inr 2079, 1), (Sum.inr 2082, 1), (Sum.inr 2105, 1), (Sum.inr 2106, 1), (Sum.inr 2107, 2), (Sum.inr 2109, 1), (Sum.inr 2116, 1), (Sum.inr 2216, 1), (Sum.inr 2277, 1), (Sum.inr 2278, 1), (Sum.inr 3737, 1), (Sum.inr 3787, 1), (Sum.inr 3876, 1), (Sum.inr 3887, 1), (Sum.inr 3888, 1)]

theorem sourceEq2449 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2449 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2449 + difference 0 1) (sourceB2449 + difference 1 0) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3737) := by
    have ha : (tripleCharges (sourceA2449 + difference 0 1) (sourceB2449 + difference 1 0) sourceC2449) = raw16311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw16311; decide +kernel
    rw [ha]
    exact (canonical16311 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2449 + difference 0 2) (sourceB2449 + difference 2 0) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3787) := by
    have ha : (tripleCharges (sourceA2449 + difference 0 2) (sourceB2449 + difference 2 0) sourceC2449) = raw16312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw16312; decide +kernel
    rw [ha]
    exact (canonical16312 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2449 + difference 0 3) (sourceB2449 + difference 3 0) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA2449 + difference 0 3) (sourceB2449 + difference 3 0) sourceC2449) = raw10930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw10930; decide +kernel
    rw [ha]
    exact (canonical10930 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2449 + difference 0 4) (sourceB2449 + difference 4 0) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA2449 + difference 0 4) (sourceB2449 + difference 4 0) sourceC2449) = raw16313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw16313; decide +kernel
    rw [ha]
    exact (canonical16313 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2449 + difference 0 5) (sourceB2449 + difference 5 0) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA2449 + difference 0 5) (sourceB2449 + difference 5 0) sourceC2449) = raw16314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw16314; decide +kernel
    rw [ha]
    exact (canonical16314 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2449 + difference 1 0) (sourceB2449 + difference 0 1) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 824) := by
    have ha : (tripleCharges (sourceA2449 + difference 1 0) (sourceB2449 + difference 0 1) sourceC2449) = raw10945 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw10945; decide +kernel
    rw [ha]
    exact (canonical10945 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2449 + difference 1 2) (sourceB2449 + difference 2 1) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1922) := by
    have ha : (tripleCharges (sourceA2449 + difference 1 2) (sourceB2449 + difference 2 1) sourceC2449) = raw10947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw10947; decide +kernel
    rw [ha]
    exact (canonical10947 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2449 + difference 1 3) (sourceB2449 + difference 3 1) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA2449 + difference 1 3) (sourceB2449 + difference 3 1) sourceC2449) = raw16306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw16306; decide +kernel
    rw [ha]
    exact (canonical16306 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2449 + difference 1 4) (sourceB2449 + difference 4 1) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA2449 + difference 1 4) (sourceB2449 + difference 4 1) sourceC2449) = raw10948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw10948; decide +kernel
    rw [ha]
    exact (canonical10948 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2449 + difference 1 5) (sourceB2449 + difference 5 1) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA2449 + difference 1 5) (sourceB2449 + difference 5 1) sourceC2449) = raw10949 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw10949; decide +kernel
    rw [ha]
    exact (canonical10949 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2449 + difference 2 0) (sourceB2449 + difference 0 2) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 732) := by
    have ha : (tripleCharges (sourceA2449 + difference 2 0) (sourceB2449 + difference 0 2) sourceC2449) = raw33629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw33629; decide +kernel
    rw [ha]
    exact (canonical33629 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2449 + difference 2 1) (sourceB2449 + difference 1 2) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1805) := by
    have ha : (tripleCharges (sourceA2449 + difference 2 1) (sourceB2449 + difference 1 2) sourceC2449) = raw33630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw33630; decide +kernel
    rw [ha]
    exact (canonical33630 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2449 + difference 2 3) (sourceB2449 + difference 3 2) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2449 + difference 2 3) (sourceB2449 + difference 3 2) sourceC2449) = raw10941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw10941; decide +kernel
    rw [ha]
    exact (canonical10941 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2449 + difference 2 4) (sourceB2449 + difference 4 2) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2077) := by
    have ha : (tripleCharges (sourceA2449 + difference 2 4) (sourceB2449 + difference 4 2) sourceC2449) = raw33631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw33631; decide +kernel
    rw [ha]
    exact (canonical33631 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2449 + difference 2 5) (sourceB2449 + difference 5 2) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2105) := by
    have ha : (tripleCharges (sourceA2449 + difference 2 5) (sourceB2449 + difference 5 2) sourceC2449) = raw33632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw33632; decide +kernel
    rw [ha]
    exact (canonical33632 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2449 + difference 3 0) (sourceB2449 + difference 0 3) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 734) := by
    have ha : (tripleCharges (sourceA2449 + difference 3 0) (sourceB2449 + difference 0 3) sourceC2449) = raw33633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw33633; decide +kernel
    rw [ha]
    exact (canonical33633 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2449 + difference 3 1) (sourceB2449 + difference 1 3) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1810) := by
    have ha : (tripleCharges (sourceA2449 + difference 3 1) (sourceB2449 + difference 1 3) sourceC2449) = raw33634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw33634; decide +kernel
    rw [ha]
    exact (canonical33634 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2449 + difference 3 2) (sourceB2449 + difference 2 3) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1876) := by
    have ha : (tripleCharges (sourceA2449 + difference 3 2) (sourceB2449 + difference 2 3) sourceC2449) = raw33635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw33635; decide +kernel
    rw [ha]
    exact (canonical33635 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2449 + difference 3 4) (sourceB2449 + difference 4 3) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA2449 + difference 3 4) (sourceB2449 + difference 4 3) sourceC2449) = raw33636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw33636; decide +kernel
    rw [ha]
    exact (canonical33636 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2449 + difference 3 5) (sourceB2449 + difference 5 3) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA2449 + difference 3 5) (sourceB2449 + difference 5 3) sourceC2449) = raw33637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw33637; decide +kernel
    rw [ha]
    exact (canonical33637 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2449 + difference 4 0) (sourceB2449 + difference 0 4) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 739) := by
    have ha : (tripleCharges (sourceA2449 + difference 4 0) (sourceB2449 + difference 0 4) sourceC2449) = raw31221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw31221; decide +kernel
    rw [ha]
    exact (canonical31221 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2449 + difference 4 1) (sourceB2449 + difference 1 4) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1815) := by
    have ha : (tripleCharges (sourceA2449 + difference 4 1) (sourceB2449 + difference 1 4) sourceC2449) = raw31222 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw31222; decide +kernel
    rw [ha]
    exact (canonical31222 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2449 + difference 4 2) (sourceB2449 + difference 2 4) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1879) := by
    have ha : (tripleCharges (sourceA2449 + difference 4 2) (sourceB2449 + difference 2 4) sourceC2449) = raw31223 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw31223; decide +kernel
    rw [ha]
    exact (canonical31223 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2449 + difference 4 3) (sourceB2449 + difference 3 4) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA2449 + difference 4 3) (sourceB2449 + difference 3 4) sourceC2449) = raw10951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw10951; decide +kernel
    rw [ha]
    exact (canonical10951 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2449 + difference 4 5) (sourceB2449 + difference 5 4) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2449 + difference 4 5) (sourceB2449 + difference 5 4) sourceC2449) = raw31224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw31224; decide +kernel
    rw [ha]
    exact (canonical31224 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2449 + difference 5 0) (sourceB2449 + difference 0 5) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 733) := by
    have ha : (tripleCharges (sourceA2449 + difference 5 0) (sourceB2449 + difference 0 5) sourceC2449) = raw33638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw33638; decide +kernel
    rw [ha]
    exact (canonical33638 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2449 + difference 5 1) (sourceB2449 + difference 1 5) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1807) := by
    have ha : (tripleCharges (sourceA2449 + difference 5 1) (sourceB2449 + difference 1 5) sourceC2449) = raw33639 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw33639; decide +kernel
    rw [ha]
    exact (canonical33639 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2449 + difference 5 2) (sourceB2449 + difference 2 5) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1875) := by
    have ha : (tripleCharges (sourceA2449 + difference 5 2) (sourceB2449 + difference 2 5) sourceC2449) = raw33640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw33640; decide +kernel
    rw [ha]
    exact (canonical33640 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2449 + difference 5 3) (sourceB2449 + difference 3 5) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA2449 + difference 5 3) (sourceB2449 + difference 3 5) sourceC2449) = raw10956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw10956; decide +kernel
    rw [ha]
    exact (canonical10956 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2449 + difference 5 4) (sourceB2449 + difference 4 5) sourceC2449) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA2449 + difference 5 4) (sourceB2449 + difference 4 5) sourceC2449) = raw33641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2449 sourceB2449 sourceC2449 difference raw33641; decide +kernel
    rw [ha]
    exact (canonical33641 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2449 sourceB2449 sourceC2449
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2449, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2450 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB2450 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2450 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2450 : Integer.Sparse Master := [(Sum.inr 4449, 1), (Sum.inr 4452, 1), (Sum.inr 4453, 1), (Sum.inr 4462, 1), (Sum.inr 4489, 1), (Sum.inr 4798, 1), (Sum.inr 4799, 1), (Sum.inr 4802, 1), (Sum.inr 4806, 1), (Sum.inr 4826, 1), (Sum.inr 4834, 1), (Sum.inr 4835, 1), (Sum.inr 4838, 1), (Sum.inr 4849, 1), (Sum.inr 4851, 1), (Sum.inr 4852, 1), (Sum.inr 4860, 1), (Sum.inr 4861, 1), (Sum.inr 4865, 1), (Sum.inr 4866, 1), (Sum.inr 4867, 1), (Sum.inr 4869, 1), (Sum.inr 4870, 1), (Sum.inr 4879, 1), (Sum.inr 4880, 1), (Sum.inr 5169, 1), (Sum.inr 5185, 1), (Sum.inr 5199, 1), (Sum.inr 5203, 1), (Sum.inr 5204, 1)]

theorem sourceEq2450 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2450 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2450 + difference 0 1) (sourceB2450 + difference 1 0) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2450 + difference 0 1) (sourceB2450 + difference 1 0) sourceC2450) = raw32254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32254; decide +kernel
    rw [ha]
    exact (canonical32254 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2450 + difference 0 2) (sourceB2450 + difference 2 0) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA2450 + difference 0 2) (sourceB2450 + difference 2 0) sourceC2450) = raw32905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32905; decide +kernel
    rw [ha]
    exact (canonical32905 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2450 + difference 0 3) (sourceB2450 + difference 3 0) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2450 + difference 0 3) (sourceB2450 + difference 3 0) sourceC2450) = raw32318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32318; decide +kernel
    rw [ha]
    exact (canonical32318 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2450 + difference 0 4) (sourceB2450 + difference 4 0) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA2450 + difference 0 4) (sourceB2450 + difference 4 0) sourceC2450) = raw32826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32826; decide +kernel
    rw [ha]
    exact (canonical32826 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2450 + difference 0 5) (sourceB2450 + difference 5 0) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2450 + difference 0 5) (sourceB2450 + difference 5 0) sourceC2450) = raw32233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32233; decide +kernel
    rw [ha]
    exact (canonical32233 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2450 + difference 1 0) (sourceB2450 + difference 0 1) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4462) := by
    have ha : (tripleCharges (sourceA2450 + difference 1 0) (sourceB2450 + difference 0 1) sourceC2450) = raw33642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33642; decide +kernel
    rw [ha]
    exact (canonical33642 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2450 + difference 1 2) (sourceB2450 + difference 2 1) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4806) := by
    have ha : (tripleCharges (sourceA2450 + difference 1 2) (sourceB2450 + difference 2 1) sourceC2450) = raw33643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33643; decide +kernel
    rw [ha]
    exact (canonical33643 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2450 + difference 1 3) (sourceB2450 + difference 3 1) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA2450 + difference 1 3) (sourceB2450 + difference 3 1) sourceC2450) = raw33644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33644; decide +kernel
    rw [ha]
    exact (canonical33644 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2450 + difference 1 4) (sourceB2450 + difference 4 1) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4870) := by
    have ha : (tripleCharges (sourceA2450 + difference 1 4) (sourceB2450 + difference 4 1) sourceC2450) = raw33645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33645; decide +kernel
    rw [ha]
    exact (canonical33645 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2450 + difference 1 5) (sourceB2450 + difference 5 1) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA2450 + difference 1 5) (sourceB2450 + difference 5 1) sourceC2450) = raw33553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33553; decide +kernel
    rw [ha]
    exact (canonical33553 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2450 + difference 2 0) (sourceB2450 + difference 0 2) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4449) := by
    have ha : (tripleCharges (sourceA2450 + difference 2 0) (sourceB2450 + difference 0 2) sourceC2450) = raw33646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33646; decide +kernel
    rw [ha]
    exact (canonical33646 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2450 + difference 2 1) (sourceB2450 + difference 1 2) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2450 + difference 2 1) (sourceB2450 + difference 1 2) sourceC2450) = raw32327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32327; decide +kernel
    rw [ha]
    exact (canonical32327 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2450 + difference 2 3) (sourceB2450 + difference 3 2) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA2450 + difference 2 3) (sourceB2450 + difference 3 2) sourceC2450) = raw32317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32317; decide +kernel
    rw [ha]
    exact (canonical32317 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2450 + difference 2 4) (sourceB2450 + difference 4 2) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4849) := by
    have ha : (tripleCharges (sourceA2450 + difference 2 4) (sourceB2450 + difference 4 2) sourceC2450) = raw33647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33647; decide +kernel
    rw [ha]
    exact (canonical33647 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2450 + difference 2 5) (sourceB2450 + difference 5 2) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA2450 + difference 2 5) (sourceB2450 + difference 5 2) sourceC2450) = raw33556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33556; decide +kernel
    rw [ha]
    exact (canonical33556 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2450 + difference 3 0) (sourceB2450 + difference 0 3) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4453) := by
    have ha : (tripleCharges (sourceA2450 + difference 3 0) (sourceB2450 + difference 0 3) sourceC2450) = raw33648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33648; decide +kernel
    rw [ha]
    exact (canonical33648 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2450 + difference 3 1) (sourceB2450 + difference 1 3) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2450 + difference 3 1) (sourceB2450 + difference 1 3) sourceC2450) = raw33649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33649; decide +kernel
    rw [ha]
    exact (canonical33649 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2450 + difference 3 2) (sourceB2450 + difference 2 3) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4799) := by
    have ha : (tripleCharges (sourceA2450 + difference 3 2) (sourceB2450 + difference 2 3) sourceC2450) = raw33650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33650; decide +kernel
    rw [ha]
    exact (canonical33650 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2450 + difference 3 4) (sourceB2450 + difference 4 3) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4861) := by
    have ha : (tripleCharges (sourceA2450 + difference 3 4) (sourceB2450 + difference 4 3) sourceC2450) = raw33651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33651; decide +kernel
    rw [ha]
    exact (canonical33651 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2450 + difference 3 5) (sourceB2450 + difference 5 3) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA2450 + difference 3 5) (sourceB2450 + difference 5 3) sourceC2450) = raw33560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33560; decide +kernel
    rw [ha]
    exact (canonical33560 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2450 + difference 4 0) (sourceB2450 + difference 0 4) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA2450 + difference 4 0) (sourceB2450 + difference 0 4) sourceC2450) = raw33566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33566; decide +kernel
    rw [ha]
    exact (canonical33566 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2450 + difference 4 1) (sourceB2450 + difference 1 4) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2450 + difference 4 1) (sourceB2450 + difference 1 4) sourceC2450) = raw32250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32250; decide +kernel
    rw [ha]
    exact (canonical32250 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2450 + difference 4 2) (sourceB2450 + difference 2 4) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA2450 + difference 4 2) (sourceB2450 + difference 2 4) sourceC2450) = raw32902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32902; decide +kernel
    rw [ha]
    exact (canonical32902 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2450 + difference 4 3) (sourceB2450 + difference 3 4) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2450 + difference 4 3) (sourceB2450 + difference 3 4) sourceC2450) = raw33567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33567; decide +kernel
    rw [ha]
    exact (canonical33567 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2450 + difference 4 5) (sourceB2450 + difference 5 4) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2450 + difference 4 5) (sourceB2450 + difference 5 4) sourceC2450) = raw32230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32230; decide +kernel
    rw [ha]
    exact (canonical32230 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2450 + difference 5 0) (sourceB2450 + difference 0 5) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA2450 + difference 5 0) (sourceB2450 + difference 0 5) sourceC2450) = raw33652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33652; decide +kernel
    rw [ha]
    exact (canonical33652 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2450 + difference 5 1) (sourceB2450 + difference 1 5) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2450 + difference 5 1) (sourceB2450 + difference 1 5) sourceC2450) = raw32835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32835; decide +kernel
    rw [ha]
    exact (canonical32835 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2450 + difference 5 2) (sourceB2450 + difference 2 5) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2450 + difference 5 2) (sourceB2450 + difference 2 5) sourceC2450) = raw32999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32999; decide +kernel
    rw [ha]
    exact (canonical32999 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2450 + difference 5 3) (sourceB2450 + difference 3 5) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2450 + difference 5 3) (sourceB2450 + difference 3 5) sourceC2450) = raw33653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33653; decide +kernel
    rw [ha]
    exact (canonical33653 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2450 + difference 5 4) (sourceB2450 + difference 4 5) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2450 + difference 5 4) (sourceB2450 + difference 4 5) sourceC2450) = raw32822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32822; decide +kernel
    rw [ha]
    exact (canonical32822 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2450 sourceB2450 sourceC2450
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2450, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2451 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2451 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2451 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm2451 : Integer.Sparse Master := [(Sum.inr 4363, 1), (Sum.inr 4365, 1), (Sum.inr 4368, 2), (Sum.inr 4457, 1), (Sum.inr 4695, 1), (Sum.inr 4697, 1), (Sum.inr 4700, 2), (Sum.inr 4771, 1), (Sum.inr 4773, 2), (Sum.inr 4801, 1), (Sum.inr 4863, 1), (Sum.inr 4865, 2), (Sum.inr 4867, 2), (Sum.inr 4868, 2), (Sum.inr 4874, 2), (Sum.inr 4888, 1), (Sum.inr 4894, 2), (Sum.inr 5249, 1), (Sum.inr 5279, 1), (Sum.inr 5282, 1), (Sum.inr 5291, 2)]

theorem sourceEq2451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2451 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2451 + difference 0 1) (sourceB2451 + difference 1 0) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5279) := by
    have ha : (tripleCharges (sourceA2451 + difference 0 1) (sourceB2451 + difference 1 0) sourceC2451) = raw33654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33654; decide +kernel
    rw [ha]
    exact (canonical33654 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2451 + difference 0 2) (sourceB2451 + difference 2 0) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA2451 + difference 0 2) (sourceB2451 + difference 2 0) sourceC2451) = raw33655 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33655; decide +kernel
    rw [ha]
    exact (canonical33655 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2451 + difference 0 3) (sourceB2451 + difference 3 0) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA2451 + difference 0 3) (sourceB2451 + difference 3 0) sourceC2451) = raw11471 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw11471; decide +kernel
    rw [ha]
    exact (canonical11471 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2451 + difference 0 4) (sourceB2451 + difference 4 0) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA2451 + difference 0 4) (sourceB2451 + difference 4 0) sourceC2451) = raw33656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33656; decide +kernel
    rw [ha]
    exact (canonical33656 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2451 + difference 0 5) (sourceB2451 + difference 5 0) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA2451 + difference 0 5) (sourceB2451 + difference 5 0) sourceC2451) = raw33657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33657; decide +kernel
    rw [ha]
    exact (canonical33657 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2451 + difference 1 0) (sourceB2451 + difference 0 1) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA2451 + difference 1 0) (sourceB2451 + difference 0 1) sourceC2451) = raw11486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw11486; decide +kernel
    rw [ha]
    exact (canonical11486 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2451 + difference 1 2) (sourceB2451 + difference 2 1) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2451 + difference 1 2) (sourceB2451 + difference 2 1) sourceC2451) = raw11488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw11488; decide +kernel
    rw [ha]
    exact (canonical11488 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2451 + difference 1 3) (sourceB2451 + difference 3 1) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA2451 + difference 1 3) (sourceB2451 + difference 3 1) sourceC2451) = raw21373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw21373; decide +kernel
    rw [ha]
    exact (canonical21373 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2451 + difference 1 4) (sourceB2451 + difference 4 1) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA2451 + difference 1 4) (sourceB2451 + difference 4 1) sourceC2451) = raw11489 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw11489; decide +kernel
    rw [ha]
    exact (canonical11489 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2451 + difference 1 5) (sourceB2451 + difference 5 1) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2451 + difference 1 5) (sourceB2451 + difference 5 1) sourceC2451) = raw11490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw11490; decide +kernel
    rw [ha]
    exact (canonical11490 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2451 + difference 2 0) (sourceB2451 + difference 0 2) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4363) := by
    have ha : (tripleCharges (sourceA2451 + difference 2 0) (sourceB2451 + difference 0 2) sourceC2451) = raw25357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw25357; decide +kernel
    rw [ha]
    exact (canonical25357 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2451 + difference 2 1) (sourceB2451 + difference 1 2) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4695) := by
    have ha : (tripleCharges (sourceA2451 + difference 2 1) (sourceB2451 + difference 1 2) sourceC2451) = raw33658 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33658; decide +kernel
    rw [ha]
    exact (canonical33658 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2451 + difference 2 3) (sourceB2451 + difference 3 2) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2451 + difference 2 3) (sourceB2451 + difference 3 2) sourceC2451) = raw11482 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw11482; decide +kernel
    rw [ha]
    exact (canonical11482 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2451 + difference 2 4) (sourceB2451 + difference 4 2) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2451 + difference 2 4) (sourceB2451 + difference 4 2) sourceC2451) = raw33659 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33659; decide +kernel
    rw [ha]
    exact (canonical33659 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2451 + difference 2 5) (sourceB2451 + difference 5 2) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4863) := by
    have ha : (tripleCharges (sourceA2451 + difference 2 5) (sourceB2451 + difference 5 2) sourceC2451) = raw33660 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33660; decide +kernel
    rw [ha]
    exact (canonical33660 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2451 + difference 3 0) (sourceB2451 + difference 0 3) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA2451 + difference 3 0) (sourceB2451 + difference 0 3) sourceC2451) = raw25361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw25361; decide +kernel
    rw [ha]
    exact (canonical25361 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2451 + difference 3 1) (sourceB2451 + difference 1 3) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4700) := by
    have ha : (tripleCharges (sourceA2451 + difference 3 1) (sourceB2451 + difference 1 3) sourceC2451) = raw33661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33661; decide +kernel
    rw [ha]
    exact (canonical33661 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2451 + difference 3 2) (sourceB2451 + difference 2 3) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4773) := by
    have ha : (tripleCharges (sourceA2451 + difference 3 2) (sourceB2451 + difference 2 3) sourceC2451) = raw33662 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33662; decide +kernel
    rw [ha]
    exact (canonical33662 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2451 + difference 3 4) (sourceB2451 + difference 4 3) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2451 + difference 3 4) (sourceB2451 + difference 4 3) sourceC2451) = raw33663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33663; decide +kernel
    rw [ha]
    exact (canonical33663 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2451 + difference 3 5) (sourceB2451 + difference 5 3) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA2451 + difference 3 5) (sourceB2451 + difference 5 3) sourceC2451) = raw33664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33664; decide +kernel
    rw [ha]
    exact (canonical33664 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2451 + difference 4 0) (sourceB2451 + difference 0 4) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA2451 + difference 4 0) (sourceB2451 + difference 0 4) sourceC2451) = raw25366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw25366; decide +kernel
    rw [ha]
    exact (canonical25366 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2451 + difference 4 1) (sourceB2451 + difference 1 4) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4700) := by
    have ha : (tripleCharges (sourceA2451 + difference 4 1) (sourceB2451 + difference 1 4) sourceC2451) = raw33665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33665; decide +kernel
    rw [ha]
    exact (canonical33665 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2451 + difference 4 2) (sourceB2451 + difference 2 4) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4773) := by
    have ha : (tripleCharges (sourceA2451 + difference 4 2) (sourceB2451 + difference 2 4) sourceC2451) = raw33666 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33666; decide +kernel
    rw [ha]
    exact (canonical33666 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2451 + difference 4 3) (sourceB2451 + difference 3 4) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2451 + difference 4 3) (sourceB2451 + difference 3 4) sourceC2451) = raw11492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw11492; decide +kernel
    rw [ha]
    exact (canonical11492 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2451 + difference 4 5) (sourceB2451 + difference 5 4) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA2451 + difference 4 5) (sourceB2451 + difference 5 4) sourceC2451) = raw33667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33667; decide +kernel
    rw [ha]
    exact (canonical33667 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2451 + difference 5 0) (sourceB2451 + difference 0 5) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4365) := by
    have ha : (tripleCharges (sourceA2451 + difference 5 0) (sourceB2451 + difference 0 5) sourceC2451) = raw21383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw21383; decide +kernel
    rw [ha]
    exact (canonical21383 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2451 + difference 5 1) (sourceB2451 + difference 1 5) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4697) := by
    have ha : (tripleCharges (sourceA2451 + difference 5 1) (sourceB2451 + difference 1 5) sourceC2451) = raw33668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33668; decide +kernel
    rw [ha]
    exact (canonical33668 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2451 + difference 5 2) (sourceB2451 + difference 2 5) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4771) := by
    have ha : (tripleCharges (sourceA2451 + difference 5 2) (sourceB2451 + difference 2 5) sourceC2451) = raw33669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33669; decide +kernel
    rw [ha]
    exact (canonical33669 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2451 + difference 5 3) (sourceB2451 + difference 3 5) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2451 + difference 5 3) (sourceB2451 + difference 3 5) sourceC2451) = raw11497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw11497; decide +kernel
    rw [ha]
    exact (canonical11497 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2451 + difference 5 4) (sourceB2451 + difference 4 5) sourceC2451) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2451 + difference 5 4) (sourceB2451 + difference 4 5) sourceC2451) = raw33670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2451 sourceB2451 sourceC2451 difference raw33670; decide +kernel
    rw [ha]
    exact (canonical33670 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2451 sourceB2451 sourceC2451
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2451, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2452 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2452 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2452 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm2452 : Integer.Sparse Master := [(Sum.inr 1319, 1), (Sum.inr 1320, 1), (Sum.inr 1321, 2), (Sum.inr 1414, 1), (Sum.inr 2895, 1), (Sum.inr 2899, 1), (Sum.inr 2966, 2), (Sum.inr 3066, 1), (Sum.inr 3078, 1), (Sum.inr 3079, 1), (Sum.inr 3103, 2), (Sum.inr 3130, 1), (Sum.inr 3131, 2), (Sum.inr 3163, 2), (Sum.inr 3179, 1), (Sum.inr 3180, 2), (Sum.inr 3185, 2), (Sum.inr 3187, 2), (Sum.inr 3205, 1), (Sum.inr 3227, 1), (Sum.inr 3230, 2)]

theorem sourceEq2452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2452 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2452 + difference 0 1) (sourceB2452 + difference 1 0) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3079) := by
    have ha : (tripleCharges (sourceA2452 + difference 0 1) (sourceB2452 + difference 1 0) sourceC2452) = raw33671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33671; decide +kernel
    rw [ha]
    exact (canonical33671 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2452 + difference 0 2) (sourceB2452 + difference 2 0) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3066) := by
    have ha : (tripleCharges (sourceA2452 + difference 0 2) (sourceB2452 + difference 2 0) sourceC2452) = raw33672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33672; decide +kernel
    rw [ha]
    exact (canonical33672 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2452 + difference 0 3) (sourceB2452 + difference 3 0) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA2452 + difference 0 3) (sourceB2452 + difference 3 0) sourceC2452) = raw33673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33673; decide +kernel
    rw [ha]
    exact (canonical33673 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2452 + difference 0 4) (sourceB2452 + difference 4 0) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA2452 + difference 0 4) (sourceB2452 + difference 4 0) sourceC2452) = raw33674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33674; decide +kernel
    rw [ha]
    exact (canonical33674 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2452 + difference 0 5) (sourceB2452 + difference 5 0) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA2452 + difference 0 5) (sourceB2452 + difference 5 0) sourceC2452) = raw33675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33675; decide +kernel
    rw [ha]
    exact (canonical33675 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2452 + difference 1 0) (sourceB2452 + difference 0 1) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA2452 + difference 1 0) (sourceB2452 + difference 0 1) sourceC2452) = raw21414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw21414; decide +kernel
    rw [ha]
    exact (canonical21414 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2452 + difference 1 2) (sourceB2452 + difference 2 1) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3205) := by
    have ha : (tripleCharges (sourceA2452 + difference 1 2) (sourceB2452 + difference 2 1) sourceC2452) = raw25370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw25370; decide +kernel
    rw [ha]
    exact (canonical25370 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2452 + difference 1 3) (sourceB2452 + difference 3 1) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA2452 + difference 1 3) (sourceB2452 + difference 3 1) sourceC2452) = raw21399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw21399; decide +kernel
    rw [ha]
    exact (canonical21399 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2452 + difference 1 4) (sourceB2452 + difference 4 1) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA2452 + difference 1 4) (sourceB2452 + difference 4 1) sourceC2452) = raw25371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw25371; decide +kernel
    rw [ha]
    exact (canonical25371 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2452 + difference 1 5) (sourceB2452 + difference 5 1) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA2452 + difference 1 5) (sourceB2452 + difference 5 1) sourceC2452) = raw25372 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw25372; decide +kernel
    rw [ha]
    exact (canonical25372 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2452 + difference 2 0) (sourceB2452 + difference 0 2) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1319) := by
    have ha : (tripleCharges (sourceA2452 + difference 2 0) (sourceB2452 + difference 0 2) sourceC2452) = raw25378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw25378; decide +kernel
    rw [ha]
    exact (canonical25378 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2452 + difference 2 1) (sourceB2452 + difference 1 2) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3130) := by
    have ha : (tripleCharges (sourceA2452 + difference 2 1) (sourceB2452 + difference 1 2) sourceC2452) = raw33676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33676; decide +kernel
    rw [ha]
    exact (canonical33676 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2452 + difference 2 3) (sourceB2452 + difference 3 2) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3185) := by
    have ha : (tripleCharges (sourceA2452 + difference 2 3) (sourceB2452 + difference 3 2) sourceC2452) = raw33677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33677; decide +kernel
    rw [ha]
    exact (canonical33677 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2452 + difference 2 4) (sourceB2452 + difference 4 2) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3185) := by
    have ha : (tripleCharges (sourceA2452 + difference 2 4) (sourceB2452 + difference 4 2) sourceC2452) = raw33678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33678; decide +kernel
    rw [ha]
    exact (canonical33678 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2452 + difference 2 5) (sourceB2452 + difference 5 2) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3179) := by
    have ha : (tripleCharges (sourceA2452 + difference 2 5) (sourceB2452 + difference 5 2) sourceC2452) = raw33679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33679; decide +kernel
    rw [ha]
    exact (canonical33679 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2452 + difference 3 0) (sourceB2452 + difference 0 3) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1321) := by
    have ha : (tripleCharges (sourceA2452 + difference 3 0) (sourceB2452 + difference 0 3) sourceC2452) = raw25382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw25382; decide +kernel
    rw [ha]
    exact (canonical25382 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2452 + difference 3 1) (sourceB2452 + difference 1 3) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3131) := by
    have ha : (tripleCharges (sourceA2452 + difference 3 1) (sourceB2452 + difference 1 3) sourceC2452) = raw33680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33680; decide +kernel
    rw [ha]
    exact (canonical33680 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2452 + difference 3 2) (sourceB2452 + difference 2 3) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3163) := by
    have ha : (tripleCharges (sourceA2452 + difference 3 2) (sourceB2452 + difference 2 3) sourceC2452) = raw33681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33681; decide +kernel
    rw [ha]
    exact (canonical33681 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2452 + difference 3 4) (sourceB2452 + difference 4 3) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3187) := by
    have ha : (tripleCharges (sourceA2452 + difference 3 4) (sourceB2452 + difference 4 3) sourceC2452) = raw33682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33682; decide +kernel
    rw [ha]
    exact (canonical33682 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2452 + difference 3 5) (sourceB2452 + difference 5 3) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA2452 + difference 3 5) (sourceB2452 + difference 5 3) sourceC2452) = raw33683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33683; decide +kernel
    rw [ha]
    exact (canonical33683 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2452 + difference 4 0) (sourceB2452 + difference 0 4) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1321) := by
    have ha : (tripleCharges (sourceA2452 + difference 4 0) (sourceB2452 + difference 0 4) sourceC2452) = raw25387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw25387; decide +kernel
    rw [ha]
    exact (canonical25387 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2452 + difference 4 1) (sourceB2452 + difference 1 4) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3131) := by
    have ha : (tripleCharges (sourceA2452 + difference 4 1) (sourceB2452 + difference 1 4) sourceC2452) = raw33684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33684; decide +kernel
    rw [ha]
    exact (canonical33684 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2452 + difference 4 2) (sourceB2452 + difference 2 4) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3163) := by
    have ha : (tripleCharges (sourceA2452 + difference 4 2) (sourceB2452 + difference 2 4) sourceC2452) = raw33685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33685; decide +kernel
    rw [ha]
    exact (canonical33685 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2452 + difference 4 3) (sourceB2452 + difference 3 4) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3187) := by
    have ha : (tripleCharges (sourceA2452 + difference 4 3) (sourceB2452 + difference 3 4) sourceC2452) = raw33686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33686; decide +kernel
    rw [ha]
    exact (canonical33686 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2452 + difference 4 5) (sourceB2452 + difference 5 4) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA2452 + difference 4 5) (sourceB2452 + difference 5 4) sourceC2452) = raw33687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33687; decide +kernel
    rw [ha]
    exact (canonical33687 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2452 + difference 5 0) (sourceB2452 + difference 0 5) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1320) := by
    have ha : (tripleCharges (sourceA2452 + difference 5 0) (sourceB2452 + difference 0 5) sourceC2452) = raw21411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw21411; decide +kernel
    rw [ha]
    exact (canonical21411 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2452 + difference 5 1) (sourceB2452 + difference 1 5) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2899) := by
    have ha : (tripleCharges (sourceA2452 + difference 5 1) (sourceB2452 + difference 1 5) sourceC2452) = raw33688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33688; decide +kernel
    rw [ha]
    exact (canonical33688 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2452 + difference 5 2) (sourceB2452 + difference 2 5) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2895) := by
    have ha : (tripleCharges (sourceA2452 + difference 5 2) (sourceB2452 + difference 2 5) sourceC2452) = raw33689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33689; decide +kernel
    rw [ha]
    exact (canonical33689 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2452 + difference 5 3) (sourceB2452 + difference 3 5) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2966) := by
    have ha : (tripleCharges (sourceA2452 + difference 5 3) (sourceB2452 + difference 3 5) sourceC2452) = raw21395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw21395; decide +kernel
    rw [ha]
    exact (canonical21395 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2452 + difference 5 4) (sourceB2452 + difference 4 5) sourceC2452) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2966) := by
    have ha : (tripleCharges (sourceA2452 + difference 5 4) (sourceB2452 + difference 4 5) sourceC2452) = raw33690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2452 sourceB2452 sourceC2452 difference raw33690; decide +kernel
    rw [ha]
    exact (canonical33690 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2452 sourceB2452 sourceC2452
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2452, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2453 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2453 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2453 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm2453 : Integer.Sparse Master := [(Sum.inr 1697, 1), (Sum.inr 1704, 1), (Sum.inr 1707, 1), (Sum.inr 1712, 2), (Sum.inr 2189, 1), (Sum.inr 2190, 1), (Sum.inr 2194, 2), (Sum.inr 2231, 1), (Sum.inr 2232, 1), (Sum.inr 2239, 1), (Sum.inr 2242, 2), (Sum.inr 2244, 1), (Sum.inr 2249, 2), (Sum.inr 2251, 2), (Sum.inr 2261, 2), (Sum.inr 2264, 2), (Sum.inr 2276, 2), (Sum.inr 2708, 1), (Sum.inr 2748, 1), (Sum.inr 2751, 1), (Sum.inr 2765, 2)]

theorem sourceEq2453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2453 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2453 + difference 0 1) (sourceB2453 + difference 1 0) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2748) := by
    have ha : (tripleCharges (sourceA2453 + difference 0 1) (sourceB2453 + difference 1 0) sourceC2453) = raw33691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33691; decide +kernel
    rw [ha]
    exact (canonical33691 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2453 + difference 0 2) (sourceB2453 + difference 2 0) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA2453 + difference 0 2) (sourceB2453 + difference 2 0) sourceC2453) = raw33692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33692; decide +kernel
    rw [ha]
    exact (canonical33692 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2453 + difference 0 3) (sourceB2453 + difference 3 0) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA2453 + difference 0 3) (sourceB2453 + difference 3 0) sourceC2453) = raw33693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33693; decide +kernel
    rw [ha]
    exact (canonical33693 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2453 + difference 0 4) (sourceB2453 + difference 4 0) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA2453 + difference 0 4) (sourceB2453 + difference 4 0) sourceC2453) = raw33694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33694; decide +kernel
    rw [ha]
    exact (canonical33694 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2453 + difference 0 5) (sourceB2453 + difference 5 0) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA2453 + difference 0 5) (sourceB2453 + difference 5 0) sourceC2453) = raw33695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33695; decide +kernel
    rw [ha]
    exact (canonical33695 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2453 + difference 1 0) (sourceB2453 + difference 0 1) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA2453 + difference 1 0) (sourceB2453 + difference 0 1) sourceC2453) = raw21444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw21444; decide +kernel
    rw [ha]
    exact (canonical21444 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2453 + difference 1 2) (sourceB2453 + difference 2 1) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA2453 + difference 1 2) (sourceB2453 + difference 2 1) sourceC2453) = raw25392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw25392; decide +kernel
    rw [ha]
    exact (canonical25392 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2453 + difference 1 3) (sourceB2453 + difference 3 1) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2453 + difference 1 3) (sourceB2453 + difference 3 1) sourceC2453) = raw21429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw21429; decide +kernel
    rw [ha]
    exact (canonical21429 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2453 + difference 1 4) (sourceB2453 + difference 4 1) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2453 + difference 1 4) (sourceB2453 + difference 4 1) sourceC2453) = raw25393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw25393; decide +kernel
    rw [ha]
    exact (canonical25393 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2453 + difference 1 5) (sourceB2453 + difference 5 1) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA2453 + difference 1 5) (sourceB2453 + difference 5 1) sourceC2453) = raw25394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw25394; decide +kernel
    rw [ha]
    exact (canonical25394 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2453 + difference 2 0) (sourceB2453 + difference 0 2) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1697) := by
    have ha : (tripleCharges (sourceA2453 + difference 2 0) (sourceB2453 + difference 0 2) sourceC2453) = raw25400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw25400; decide +kernel
    rw [ha]
    exact (canonical25400 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2453 + difference 2 1) (sourceB2453 + difference 1 2) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2231) := by
    have ha : (tripleCharges (sourceA2453 + difference 2 1) (sourceB2453 + difference 1 2) sourceC2453) = raw33696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33696; decide +kernel
    rw [ha]
    exact (canonical33696 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2453 + difference 2 3) (sourceB2453 + difference 3 2) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2453 + difference 2 3) (sourceB2453 + difference 3 2) sourceC2453) = raw33697 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33697; decide +kernel
    rw [ha]
    exact (canonical33697 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2453 + difference 2 4) (sourceB2453 + difference 4 2) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2453 + difference 2 4) (sourceB2453 + difference 4 2) sourceC2453) = raw33698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33698; decide +kernel
    rw [ha]
    exact (canonical33698 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2453 + difference 2 5) (sourceB2453 + difference 5 2) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2232) := by
    have ha : (tripleCharges (sourceA2453 + difference 2 5) (sourceB2453 + difference 5 2) sourceC2453) = raw33699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33699; decide +kernel
    rw [ha]
    exact (canonical33699 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2453 + difference 3 0) (sourceB2453 + difference 0 3) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA2453 + difference 3 0) (sourceB2453 + difference 0 3) sourceC2453) = raw25404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw25404; decide +kernel
    rw [ha]
    exact (canonical25404 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2453 + difference 3 1) (sourceB2453 + difference 1 3) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2249) := by
    have ha : (tripleCharges (sourceA2453 + difference 3 1) (sourceB2453 + difference 1 3) sourceC2453) = raw33700 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33700; decide +kernel
    rw [ha]
    exact (canonical33700 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2453 + difference 3 2) (sourceB2453 + difference 2 3) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2194) := by
    have ha : (tripleCharges (sourceA2453 + difference 3 2) (sourceB2453 + difference 2 3) sourceC2453) = raw33701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33701; decide +kernel
    rw [ha]
    exact (canonical33701 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2453 + difference 3 4) (sourceB2453 + difference 4 3) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA2453 + difference 3 4) (sourceB2453 + difference 4 3) sourceC2453) = raw33702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33702; decide +kernel
    rw [ha]
    exact (canonical33702 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2453 + difference 3 5) (sourceB2453 + difference 5 3) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA2453 + difference 3 5) (sourceB2453 + difference 5 3) sourceC2453) = raw33703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33703; decide +kernel
    rw [ha]
    exact (canonical33703 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2453 + difference 4 0) (sourceB2453 + difference 0 4) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA2453 + difference 4 0) (sourceB2453 + difference 0 4) sourceC2453) = raw25409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw25409; decide +kernel
    rw [ha]
    exact (canonical25409 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2453 + difference 4 1) (sourceB2453 + difference 1 4) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2249) := by
    have ha : (tripleCharges (sourceA2453 + difference 4 1) (sourceB2453 + difference 1 4) sourceC2453) = raw33704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33704; decide +kernel
    rw [ha]
    exact (canonical33704 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2453 + difference 4 2) (sourceB2453 + difference 2 4) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2194) := by
    have ha : (tripleCharges (sourceA2453 + difference 4 2) (sourceB2453 + difference 2 4) sourceC2453) = raw33705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33705; decide +kernel
    rw [ha]
    exact (canonical33705 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2453 + difference 4 3) (sourceB2453 + difference 3 4) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA2453 + difference 4 3) (sourceB2453 + difference 3 4) sourceC2453) = raw33706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33706; decide +kernel
    rw [ha]
    exact (canonical33706 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2453 + difference 4 5) (sourceB2453 + difference 5 4) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA2453 + difference 4 5) (sourceB2453 + difference 5 4) sourceC2453) = raw33707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33707; decide +kernel
    rw [ha]
    exact (canonical33707 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2453 + difference 5 0) (sourceB2453 + difference 0 5) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1704) := by
    have ha : (tripleCharges (sourceA2453 + difference 5 0) (sourceB2453 + difference 0 5) sourceC2453) = raw21441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw21441; decide +kernel
    rw [ha]
    exact (canonical21441 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2453 + difference 5 1) (sourceB2453 + difference 1 5) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2239) := by
    have ha : (tripleCharges (sourceA2453 + difference 5 1) (sourceB2453 + difference 1 5) sourceC2453) = raw33708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33708; decide +kernel
    rw [ha]
    exact (canonical33708 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2453 + difference 5 2) (sourceB2453 + difference 2 5) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2189) := by
    have ha : (tripleCharges (sourceA2453 + difference 5 2) (sourceB2453 + difference 2 5) sourceC2453) = raw33709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33709; decide +kernel
    rw [ha]
    exact (canonical33709 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2453 + difference 5 3) (sourceB2453 + difference 3 5) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA2453 + difference 5 3) (sourceB2453 + difference 3 5) sourceC2453) = raw21425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw21425; decide +kernel
    rw [ha]
    exact (canonical21425 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2453 + difference 5 4) (sourceB2453 + difference 4 5) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA2453 + difference 5 4) (sourceB2453 + difference 4 5) sourceC2453) = raw33710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33710; decide +kernel
    rw [ha]
    exact (canonical33710 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2453 sourceB2453 sourceC2453
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2453, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2454 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2454 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2454 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm2454 : Integer.Sparse Master := [(Sum.inr 1821, 1), (Sum.inr 1823, 1), (Sum.inr 1826, 2), (Sum.inr 2106, 1), (Sum.inr 3050, 1), (Sum.inr 4084, -1)]

theorem sourceEq2454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2454 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2454 + difference 0 1) (sourceB2454 + difference 1 0) sourceC2454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3050) := by
    have ha : (tripleCharges (sourceA2454 + difference 0 1) (sourceB2454 + difference 1 0) sourceC2454) = raw33711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2454 sourceB2454 sourceC2454 difference raw33711; decide +kernel
    rw [ha]
    exact (canonical33711 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2454 + difference 1 1) (sourceB2454 + difference 1 1) sourceC2454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA2454 + difference 1 1) (sourceB2454 + difference 1 1) sourceC2454) = raw25421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2454 sourceB2454 sourceC2454 difference raw25421; decide +kernel
    rw [ha]
    exact (canonical25421 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2454 + difference 2 1) (sourceB2454 + difference 1 2) sourceC2454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1821) := by
    have ha : (tripleCharges (sourceA2454 + difference 2 1) (sourceB2454 + difference 1 2) sourceC2454) = raw33712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2454 sourceB2454 sourceC2454 difference raw33712; decide +kernel
    rw [ha]
    exact (canonical33712 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2454 + difference 3 1) (sourceB2454 + difference 1 3) sourceC2454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1826) := by
    have ha : (tripleCharges (sourceA2454 + difference 3 1) (sourceB2454 + difference 1 3) sourceC2454) = raw33713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2454 sourceB2454 sourceC2454 difference raw33713; decide +kernel
    rw [ha]
    exact (canonical33713 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2454 + difference 4 1) (sourceB2454 + difference 1 4) sourceC2454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1826) := by
    have ha : (tripleCharges (sourceA2454 + difference 4 1) (sourceB2454 + difference 1 4) sourceC2454) = raw33714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2454 sourceB2454 sourceC2454 difference raw33714; decide +kernel
    rw [ha]
    exact (canonical33714 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2454 + difference 5 1) (sourceB2454 + difference 1 5) sourceC2454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1823) := by
    have ha : (tripleCharges (sourceA2454 + difference 5 1) (sourceB2454 + difference 1 5) sourceC2454) = raw33715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2454 sourceB2454 sourceC2454 difference raw33715; decide +kernel
    rw [ha]
    exact (canonical33715 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2454 + sourceB2454) sourceC2454) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2454 + sourceB2454) sourceC2454) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA2454 sourceB2454 sourceC2454 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2454 sourceB2454 sourceC2454
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2454, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2455 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2455 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2455 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm2455 : Integer.Sparse Master := [(Sum.inr 941, 1), (Sum.inr 1821, 1), (Sum.inr 2104, 1), (Sum.inr 2106, 3), (Sum.inr 4084, -1)]

theorem sourceEq2455 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2455 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2455 + difference 2 0) (sourceB2455 + difference 0 2) sourceC2455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 941) := by
    have ha : (tripleCharges (sourceA2455 + difference 2 0) (sourceB2455 + difference 0 2) sourceC2455) = raw25422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2455 sourceB2455 sourceC2455 difference raw25422; decide +kernel
    rw [ha]
    exact (canonical25422 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2455 + difference 2 1) (sourceB2455 + difference 1 2) sourceC2455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1821) := by
    have ha : (tripleCharges (sourceA2455 + difference 2 1) (sourceB2455 + difference 1 2) sourceC2455) = raw33712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2455 sourceB2455 sourceC2455 difference raw33712; decide +kernel
    rw [ha]
    exact (canonical33712 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2455 + difference 2 2) (sourceB2455 + difference 2 2) sourceC2455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA2455 + difference 2 2) (sourceB2455 + difference 2 2) sourceC2455) = raw25421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2455 sourceB2455 sourceC2455 difference raw25421; decide +kernel
    rw [ha]
    exact (canonical25421 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2455 + difference 2 3) (sourceB2455 + difference 3 2) sourceC2455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA2455 + difference 2 3) (sourceB2455 + difference 3 2) sourceC2455) = raw33716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2455 sourceB2455 sourceC2455 difference raw33716; decide +kernel
    rw [ha]
    exact (canonical33716 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2455 + difference 2 4) (sourceB2455 + difference 4 2) sourceC2455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA2455 + difference 2 4) (sourceB2455 + difference 4 2) sourceC2455) = raw33717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2455 sourceB2455 sourceC2455 difference raw33717; decide +kernel
    rw [ha]
    exact (canonical33717 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2455 + difference 2 5) (sourceB2455 + difference 5 2) sourceC2455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2104) := by
    have ha : (tripleCharges (sourceA2455 + difference 2 5) (sourceB2455 + difference 5 2) sourceC2455) = raw33718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2455 sourceB2455 sourceC2455 difference raw33718; decide +kernel
    rw [ha]
    exact (canonical33718 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2455 + sourceB2455) sourceC2455) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2455 + sourceB2455) sourceC2455) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA2455 sourceB2455 sourceC2455 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2455 sourceB2455 sourceC2455
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2455, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2456 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2456 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC2456 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceForm2456 : Integer.Sparse Master := [(Sum.inr 4230, 1), (Sum.inr 4231, 1), (Sum.inr 4234, 2), (Sum.inr 4255, 1), (Sum.inr 4676, 1), (Sum.inr 4678, 1), (Sum.inr 4684, 2), (Sum.inr 4720, 1), (Sum.inr 4722, 2), (Sum.inr 4731, 1), (Sum.inr 4798, 2), (Sum.inr 4800, 2), (Sum.inr 4810, 2), (Sum.inr 4828, 2), (Sum.inr 4864, 1), (Sum.inr 4866, 2), (Sum.inr 4889, 1), (Sum.inr 5387, 1), (Sum.inr 5400, 1), (Sum.inr 5432, 2), (Sum.inr 5450, 1)]

theorem sourceEq2456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2456 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2456 + difference 0 1) (sourceB2456 + difference 1 0) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2456 + difference 0 1) (sourceB2456 + difference 1 0) sourceC2456) = raw18198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18198; decide +kernel
    rw [ha]
    exact (canonical18198 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2456 + difference 0 2) (sourceB2456 + difference 2 0) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA2456 + difference 0 2) (sourceB2456 + difference 2 0) sourceC2456) = raw18199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18199; decide +kernel
    rw [ha]
    exact (canonical18199 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2456 + difference 0 3) (sourceB2456 + difference 3 0) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA2456 + difference 0 3) (sourceB2456 + difference 3 0) sourceC2456) = raw18506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18506; decide +kernel
    rw [ha]
    exact (canonical18506 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2456 + difference 0 4) (sourceB2456 + difference 4 0) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA2456 + difference 0 4) (sourceB2456 + difference 4 0) sourceC2456) = raw18200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18200; decide +kernel
    rw [ha]
    exact (canonical18200 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2456 + difference 0 5) (sourceB2456 + difference 5 0) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2456 + difference 0 5) (sourceB2456 + difference 5 0) sourceC2456) = raw18201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18201; decide +kernel
    rw [ha]
    exact (canonical18201 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2456 + difference 1 0) (sourceB2456 + difference 0 1) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4255) := by
    have ha : (tripleCharges (sourceA2456 + difference 1 0) (sourceB2456 + difference 0 1) sourceC2456) = raw33719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33719; decide +kernel
    rw [ha]
    exact (canonical33719 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2456 + difference 1 2) (sourceB2456 + difference 2 1) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4731) := by
    have ha : (tripleCharges (sourceA2456 + difference 1 2) (sourceB2456 + difference 2 1) sourceC2456) = raw33720 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33720; decide +kernel
    rw [ha]
    exact (canonical33720 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2456 + difference 1 3) (sourceB2456 + difference 3 1) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2456 + difference 1 3) (sourceB2456 + difference 3 1) sourceC2456) = raw18187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18187; decide +kernel
    rw [ha]
    exact (canonical18187 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2456 + difference 1 4) (sourceB2456 + difference 4 1) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2456 + difference 1 4) (sourceB2456 + difference 4 1) sourceC2456) = raw33721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33721; decide +kernel
    rw [ha]
    exact (canonical33721 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2456 + difference 1 5) (sourceB2456 + difference 5 1) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2456 + difference 1 5) (sourceB2456 + difference 5 1) sourceC2456) = raw18489 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18489; decide +kernel
    rw [ha]
    exact (canonical18489 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2456 + difference 2 0) (sourceB2456 + difference 0 2) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4230) := by
    have ha : (tripleCharges (sourceA2456 + difference 2 0) (sourceB2456 + difference 0 2) sourceC2456) = raw33722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33722; decide +kernel
    rw [ha]
    exact (canonical33722 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2456 + difference 2 1) (sourceB2456 + difference 1 2) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4676) := by
    have ha : (tripleCharges (sourceA2456 + difference 2 1) (sourceB2456 + difference 1 2) sourceC2456) = raw33723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33723; decide +kernel
    rw [ha]
    exact (canonical33723 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2456 + difference 2 3) (sourceB2456 + difference 3 2) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2456 + difference 2 3) (sourceB2456 + difference 3 2) sourceC2456) = raw18192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18192; decide +kernel
    rw [ha]
    exact (canonical18192 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2456 + difference 2 4) (sourceB2456 + difference 4 2) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2456 + difference 2 4) (sourceB2456 + difference 4 2) sourceC2456) = raw33724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33724; decide +kernel
    rw [ha]
    exact (canonical33724 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2456 + difference 2 5) (sourceB2456 + difference 5 2) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA2456 + difference 2 5) (sourceB2456 + difference 5 2) sourceC2456) = raw18493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18493; decide +kernel
    rw [ha]
    exact (canonical18493 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2456 + difference 3 0) (sourceB2456 + difference 0 3) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4234) := by
    have ha : (tripleCharges (sourceA2456 + difference 3 0) (sourceB2456 + difference 0 3) sourceC2456) = raw33725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33725; decide +kernel
    rw [ha]
    exact (canonical33725 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2456 + difference 3 1) (sourceB2456 + difference 1 3) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2456 + difference 3 1) (sourceB2456 + difference 1 3) sourceC2456) = raw33726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33726; decide +kernel
    rw [ha]
    exact (canonical33726 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2456 + difference 3 2) (sourceB2456 + difference 2 3) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4722) := by
    have ha : (tripleCharges (sourceA2456 + difference 3 2) (sourceB2456 + difference 2 3) sourceC2456) = raw33727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33727; decide +kernel
    rw [ha]
    exact (canonical33727 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2456 + difference 3 4) (sourceB2456 + difference 4 3) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2456 + difference 3 4) (sourceB2456 + difference 4 3) sourceC2456) = raw33728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33728; decide +kernel
    rw [ha]
    exact (canonical33728 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2456 + difference 3 5) (sourceB2456 + difference 5 3) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2456 + difference 3 5) (sourceB2456 + difference 5 3) sourceC2456) = raw18497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18497; decide +kernel
    rw [ha]
    exact (canonical18497 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2456 + difference 4 0) (sourceB2456 + difference 0 4) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4234) := by
    have ha : (tripleCharges (sourceA2456 + difference 4 0) (sourceB2456 + difference 0 4) sourceC2456) = raw33729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33729; decide +kernel
    rw [ha]
    exact (canonical33729 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2456 + difference 4 1) (sourceB2456 + difference 1 4) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2456 + difference 4 1) (sourceB2456 + difference 1 4) sourceC2456) = raw33730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33730; decide +kernel
    rw [ha]
    exact (canonical33730 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2456 + difference 4 2) (sourceB2456 + difference 2 4) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4722) := by
    have ha : (tripleCharges (sourceA2456 + difference 4 2) (sourceB2456 + difference 2 4) sourceC2456) = raw33731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33731; decide +kernel
    rw [ha]
    exact (canonical33731 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2456 + difference 4 3) (sourceB2456 + difference 3 4) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2456 + difference 4 3) (sourceB2456 + difference 3 4) sourceC2456) = raw18202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18202; decide +kernel
    rw [ha]
    exact (canonical18202 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2456 + difference 4 5) (sourceB2456 + difference 5 4) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2456 + difference 4 5) (sourceB2456 + difference 5 4) sourceC2456) = raw18502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18502; decide +kernel
    rw [ha]
    exact (canonical18502 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2456 + difference 5 0) (sourceB2456 + difference 0 5) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4231) := by
    have ha : (tripleCharges (sourceA2456 + difference 5 0) (sourceB2456 + difference 0 5) sourceC2456) = raw33732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33732; decide +kernel
    rw [ha]
    exact (canonical33732 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2456 + difference 5 1) (sourceB2456 + difference 1 5) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2456 + difference 5 1) (sourceB2456 + difference 1 5) sourceC2456) = raw33733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33733; decide +kernel
    rw [ha]
    exact (canonical33733 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2456 + difference 5 2) (sourceB2456 + difference 2 5) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4720) := by
    have ha : (tripleCharges (sourceA2456 + difference 5 2) (sourceB2456 + difference 2 5) sourceC2456) = raw33734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33734; decide +kernel
    rw [ha]
    exact (canonical33734 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2456 + difference 5 3) (sourceB2456 + difference 3 5) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4800) := by
    have ha : (tripleCharges (sourceA2456 + difference 5 3) (sourceB2456 + difference 3 5) sourceC2456) = raw18207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18207; decide +kernel
    rw [ha]
    exact (canonical18207 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2456 + difference 5 4) (sourceB2456 + difference 4 5) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4800) := by
    have ha : (tripleCharges (sourceA2456 + difference 5 4) (sourceB2456 + difference 4 5) sourceC2456) = raw33735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33735; decide +kernel
    rw [ha]
    exact (canonical33735 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2456 sourceB2456 sourceC2456
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2456, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2457 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2457 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC2457 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceForm2457 : Integer.Sparse Master := [(Sum.inr 730, 1), (Sum.inr 731, 1), (Sum.inr 734, 2), (Sum.inr 823, 1), (Sum.inr 1802, 1), (Sum.inr 1804, 1), (Sum.inr 1810, 2), (Sum.inr 1874, 1), (Sum.inr 1876, 2), (Sum.inr 1921, 1), (Sum.inr 2018, 2), (Sum.inr 2075, 2), (Sum.inr 2082, 2), (Sum.inr 2105, 1), (Sum.inr 2107, 2), (Sum.inr 2215, 2), (Sum.inr 2277, 1), (Sum.inr 3736, 1), (Sum.inr 3786, 1), (Sum.inr 3850, 2), (Sum.inr 3887, 1)]

theorem sourceEq2457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2457 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2457 + difference 0 1) (sourceB2457 + difference 1 0) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3736) := by
    have ha : (tripleCharges (sourceA2457 + difference 0 1) (sourceB2457 + difference 1 0) sourceC2457) = raw33736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33736; decide +kernel
    rw [ha]
    exact (canonical33736 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2457 + difference 0 2) (sourceB2457 + difference 2 0) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3786) := by
    have ha : (tripleCharges (sourceA2457 + difference 0 2) (sourceB2457 + difference 2 0) sourceC2457) = raw33737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33737; decide +kernel
    rw [ha]
    exact (canonical33737 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2457 + difference 0 3) (sourceB2457 + difference 3 0) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA2457 + difference 0 3) (sourceB2457 + difference 3 0) sourceC2457) = raw33738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33738; decide +kernel
    rw [ha]
    exact (canonical33738 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2457 + difference 0 4) (sourceB2457 + difference 4 0) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA2457 + difference 0 4) (sourceB2457 + difference 4 0) sourceC2457) = raw33739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33739; decide +kernel
    rw [ha]
    exact (canonical33739 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2457 + difference 0 5) (sourceB2457 + difference 5 0) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA2457 + difference 0 5) (sourceB2457 + difference 5 0) sourceC2457) = raw33740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33740; decide +kernel
    rw [ha]
    exact (canonical33740 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2457 + difference 1 0) (sourceB2457 + difference 0 1) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 823) := by
    have ha : (tripleCharges (sourceA2457 + difference 1 0) (sourceB2457 + difference 0 1) sourceC2457) = raw33741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33741; decide +kernel
    rw [ha]
    exact (canonical33741 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2457 + difference 1 2) (sourceB2457 + difference 2 1) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1921) := by
    have ha : (tripleCharges (sourceA2457 + difference 1 2) (sourceB2457 + difference 2 1) sourceC2457) = raw33742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33742; decide +kernel
    rw [ha]
    exact (canonical33742 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2457 + difference 1 3) (sourceB2457 + difference 3 1) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2457 + difference 1 3) (sourceB2457 + difference 3 1) sourceC2457) = raw33743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33743; decide +kernel
    rw [ha]
    exact (canonical33743 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2457 + difference 1 4) (sourceB2457 + difference 4 1) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2457 + difference 1 4) (sourceB2457 + difference 4 1) sourceC2457) = raw33744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33744; decide +kernel
    rw [ha]
    exact (canonical33744 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2457 + difference 1 5) (sourceB2457 + difference 5 1) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA2457 + difference 1 5) (sourceB2457 + difference 5 1) sourceC2457) = raw33745 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33745; decide +kernel
    rw [ha]
    exact (canonical33745 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2457 + difference 2 0) (sourceB2457 + difference 0 2) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 730) := by
    have ha : (tripleCharges (sourceA2457 + difference 2 0) (sourceB2457 + difference 0 2) sourceC2457) = raw33746 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33746; decide +kernel
    rw [ha]
    exact (canonical33746 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2457 + difference 2 1) (sourceB2457 + difference 1 2) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1802) := by
    have ha : (tripleCharges (sourceA2457 + difference 2 1) (sourceB2457 + difference 1 2) sourceC2457) = raw33747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33747; decide +kernel
    rw [ha]
    exact (canonical33747 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2457 + difference 2 3) (sourceB2457 + difference 3 2) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2075) := by
    have ha : (tripleCharges (sourceA2457 + difference 2 3) (sourceB2457 + difference 3 2) sourceC2457) = raw33748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33748; decide +kernel
    rw [ha]
    exact (canonical33748 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2457 + difference 2 4) (sourceB2457 + difference 4 2) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2075) := by
    have ha : (tripleCharges (sourceA2457 + difference 2 4) (sourceB2457 + difference 4 2) sourceC2457) = raw33749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33749; decide +kernel
    rw [ha]
    exact (canonical33749 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2457 + difference 2 5) (sourceB2457 + difference 5 2) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2105) := by
    have ha : (tripleCharges (sourceA2457 + difference 2 5) (sourceB2457 + difference 5 2) sourceC2457) = raw33750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33750; decide +kernel
    rw [ha]
    exact (canonical33750 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2457 + difference 3 0) (sourceB2457 + difference 0 3) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 734) := by
    have ha : (tripleCharges (sourceA2457 + difference 3 0) (sourceB2457 + difference 0 3) sourceC2457) = raw33751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33751; decide +kernel
    rw [ha]
    exact (canonical33751 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2457 + difference 3 1) (sourceB2457 + difference 1 3) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1810) := by
    have ha : (tripleCharges (sourceA2457 + difference 3 1) (sourceB2457 + difference 1 3) sourceC2457) = raw33752 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33752; decide +kernel
    rw [ha]
    exact (canonical33752 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2457 + difference 3 2) (sourceB2457 + difference 2 3) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1876) := by
    have ha : (tripleCharges (sourceA2457 + difference 3 2) (sourceB2457 + difference 2 3) sourceC2457) = raw33753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33753; decide +kernel
    rw [ha]
    exact (canonical33753 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2457 + difference 3 4) (sourceB2457 + difference 4 3) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA2457 + difference 3 4) (sourceB2457 + difference 4 3) sourceC2457) = raw33754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33754; decide +kernel
    rw [ha]
    exact (canonical33754 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2457 + difference 3 5) (sourceB2457 + difference 5 3) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2457 + difference 3 5) (sourceB2457 + difference 5 3) sourceC2457) = raw33755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33755; decide +kernel
    rw [ha]
    exact (canonical33755 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2457 + difference 4 0) (sourceB2457 + difference 0 4) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 734) := by
    have ha : (tripleCharges (sourceA2457 + difference 4 0) (sourceB2457 + difference 0 4) sourceC2457) = raw33756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33756; decide +kernel
    rw [ha]
    exact (canonical33756 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2457 + difference 4 1) (sourceB2457 + difference 1 4) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1810) := by
    have ha : (tripleCharges (sourceA2457 + difference 4 1) (sourceB2457 + difference 1 4) sourceC2457) = raw33757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33757; decide +kernel
    rw [ha]
    exact (canonical33757 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2457 + difference 4 2) (sourceB2457 + difference 2 4) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1876) := by
    have ha : (tripleCharges (sourceA2457 + difference 4 2) (sourceB2457 + difference 2 4) sourceC2457) = raw33758 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33758; decide +kernel
    rw [ha]
    exact (canonical33758 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2457 + difference 4 3) (sourceB2457 + difference 3 4) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA2457 + difference 4 3) (sourceB2457 + difference 3 4) sourceC2457) = raw33759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33759; decide +kernel
    rw [ha]
    exact (canonical33759 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2457 + difference 4 5) (sourceB2457 + difference 5 4) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2457 + difference 4 5) (sourceB2457 + difference 5 4) sourceC2457) = raw33760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33760; decide +kernel
    rw [ha]
    exact (canonical33760 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2457 + difference 5 0) (sourceB2457 + difference 0 5) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 731) := by
    have ha : (tripleCharges (sourceA2457 + difference 5 0) (sourceB2457 + difference 0 5) sourceC2457) = raw33761 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33761; decide +kernel
    rw [ha]
    exact (canonical33761 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2457 + difference 5 1) (sourceB2457 + difference 1 5) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1804) := by
    have ha : (tripleCharges (sourceA2457 + difference 5 1) (sourceB2457 + difference 1 5) sourceC2457) = raw33762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33762; decide +kernel
    rw [ha]
    exact (canonical33762 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2457 + difference 5 2) (sourceB2457 + difference 2 5) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1874) := by
    have ha : (tripleCharges (sourceA2457 + difference 5 2) (sourceB2457 + difference 2 5) sourceC2457) = raw33763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33763; decide +kernel
    rw [ha]
    exact (canonical33763 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2457 + difference 5 3) (sourceB2457 + difference 3 5) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2018) := by
    have ha : (tripleCharges (sourceA2457 + difference 5 3) (sourceB2457 + difference 3 5) sourceC2457) = raw33764 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33764; decide +kernel
    rw [ha]
    exact (canonical33764 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2457 + difference 5 4) (sourceB2457 + difference 4 5) sourceC2457) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2018) := by
    have ha : (tripleCharges (sourceA2457 + difference 5 4) (sourceB2457 + difference 4 5) sourceC2457) = raw33765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2457 sourceB2457 sourceC2457 difference raw33765; decide +kernel
    rw [ha]
    exact (canonical33765 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2457 sourceB2457 sourceC2457
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2457, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2458 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceB2458 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC2458 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2458 : Integer.Sparse Master := [(Sum.inr 4435, 1), (Sum.inr 4437, 1), (Sum.inr 4443, 1), (Sum.inr 4452, 2), (Sum.inr 4791, 1), (Sum.inr 4794, 1), (Sum.inr 4798, 2), (Sum.inr 4801, 1), (Sum.inr 4832, 1), (Sum.inr 4834, 2), (Sum.inr 4848, 2), (Sum.inr 4850, 2), (Sum.inr 4851, 1), (Sum.inr 4855, 2), (Sum.inr 4860, 2), (Sum.inr 4866, 2), (Sum.inr 4879, 1), (Sum.inr 5168, 1), (Sum.inr 5184, 1), (Sum.inr 5198, 2), (Sum.inr 5203, 1)]

theorem sourceEq2458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2458 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2458 + difference 0 1) (sourceB2458 + difference 1 0) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2458 + difference 0 1) (sourceB2458 + difference 1 0) sourceC2458) = raw32335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32335; decide +kernel
    rw [ha]
    exact (canonical32335 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2458 + difference 0 2) (sourceB2458 + difference 2 0) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA2458 + difference 0 2) (sourceB2458 + difference 2 0) sourceC2458) = raw33001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33001; decide +kernel
    rw [ha]
    exact (canonical33001 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2458 + difference 0 3) (sourceB2458 + difference 3 0) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA2458 + difference 0 3) (sourceB2458 + difference 3 0) sourceC2458) = raw33766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33766; decide +kernel
    rw [ha]
    exact (canonical33766 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2458 + difference 0 4) (sourceB2458 + difference 4 0) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA2458 + difference 0 4) (sourceB2458 + difference 4 0) sourceC2458) = raw32824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32824; decide +kernel
    rw [ha]
    exact (canonical32824 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2458 + difference 0 5) (sourceB2458 + difference 5 0) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2458 + difference 0 5) (sourceB2458 + difference 5 0) sourceC2458) = raw32318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32318; decide +kernel
    rw [ha]
    exact (canonical32318 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2458 + difference 1 0) (sourceB2458 + difference 0 1) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4443) := by
    have ha : (tripleCharges (sourceA2458 + difference 1 0) (sourceB2458 + difference 0 1) sourceC2458) = raw33767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33767; decide +kernel
    rw [ha]
    exact (canonical33767 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2458 + difference 1 2) (sourceB2458 + difference 2 1) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4794) := by
    have ha : (tripleCharges (sourceA2458 + difference 1 2) (sourceB2458 + difference 2 1) sourceC2458) = raw33768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33768; decide +kernel
    rw [ha]
    exact (canonical33768 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2458 + difference 1 3) (sourceB2458 + difference 3 1) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4855) := by
    have ha : (tripleCharges (sourceA2458 + difference 1 3) (sourceB2458 + difference 3 1) sourceC2458) = raw33769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33769; decide +kernel
    rw [ha]
    exact (canonical33769 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2458 + difference 1 4) (sourceB2458 + difference 4 1) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4855) := by
    have ha : (tripleCharges (sourceA2458 + difference 1 4) (sourceB2458 + difference 4 1) sourceC2458) = raw33770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33770; decide +kernel
    rw [ha]
    exact (canonical33770 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2458 + difference 1 5) (sourceB2458 + difference 5 1) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA2458 + difference 1 5) (sourceB2458 + difference 5 1) sourceC2458) = raw33644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33644; decide +kernel
    rw [ha]
    exact (canonical33644 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2458 + difference 2 0) (sourceB2458 + difference 0 2) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4435) := by
    have ha : (tripleCharges (sourceA2458 + difference 2 0) (sourceB2458 + difference 0 2) sourceC2458) = raw33771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33771; decide +kernel
    rw [ha]
    exact (canonical33771 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2458 + difference 2 1) (sourceB2458 + difference 1 2) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2458 + difference 2 1) (sourceB2458 + difference 1 2) sourceC2458) = raw32333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32333; decide +kernel
    rw [ha]
    exact (canonical32333 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2458 + difference 2 3) (sourceB2458 + difference 3 2) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4848) := by
    have ha : (tripleCharges (sourceA2458 + difference 2 3) (sourceB2458 + difference 3 2) sourceC2458) = raw33772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33772; decide +kernel
    rw [ha]
    exact (canonical33772 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2458 + difference 2 4) (sourceB2458 + difference 4 2) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4848) := by
    have ha : (tripleCharges (sourceA2458 + difference 2 4) (sourceB2458 + difference 4 2) sourceC2458) = raw33773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33773; decide +kernel
    rw [ha]
    exact (canonical33773 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2458 + difference 2 5) (sourceB2458 + difference 5 2) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA2458 + difference 2 5) (sourceB2458 + difference 5 2) sourceC2458) = raw32317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32317; decide +kernel
    rw [ha]
    exact (canonical32317 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2458 + difference 3 0) (sourceB2458 + difference 0 3) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA2458 + difference 3 0) (sourceB2458 + difference 0 3) sourceC2458) = raw33652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33652; decide +kernel
    rw [ha]
    exact (canonical33652 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2458 + difference 3 1) (sourceB2458 + difference 1 3) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2458 + difference 3 1) (sourceB2458 + difference 1 3) sourceC2458) = raw32835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32835; decide +kernel
    rw [ha]
    exact (canonical32835 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2458 + difference 3 2) (sourceB2458 + difference 2 3) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2458 + difference 3 2) (sourceB2458 + difference 2 3) sourceC2458) = raw32999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32999; decide +kernel
    rw [ha]
    exact (canonical32999 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2458 + difference 3 4) (sourceB2458 + difference 4 3) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2458 + difference 3 4) (sourceB2458 + difference 4 3) sourceC2458) = raw32822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw32822; decide +kernel
    rw [ha]
    exact (canonical32822 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2458 + difference 3 5) (sourceB2458 + difference 5 3) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2458 + difference 3 5) (sourceB2458 + difference 5 3) sourceC2458) = raw33568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33568; decide +kernel
    rw [ha]
    exact (canonical33568 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2458 + difference 4 0) (sourceB2458 + difference 0 4) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA2458 + difference 4 0) (sourceB2458 + difference 0 4) sourceC2458) = raw33774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33774; decide +kernel
    rw [ha]
    exact (canonical33774 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2458 + difference 4 1) (sourceB2458 + difference 1 4) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2458 + difference 4 1) (sourceB2458 + difference 1 4) sourceC2458) = raw33775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33775; decide +kernel
    rw [ha]
    exact (canonical33775 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2458 + difference 4 2) (sourceB2458 + difference 2 4) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2458 + difference 4 2) (sourceB2458 + difference 2 4) sourceC2458) = raw33776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33776; decide +kernel
    rw [ha]
    exact (canonical33776 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2458 + difference 4 3) (sourceB2458 + difference 3 4) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2458 + difference 4 3) (sourceB2458 + difference 3 4) sourceC2458) = raw33777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33777; decide +kernel
    rw [ha]
    exact (canonical33777 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2458 + difference 4 5) (sourceB2458 + difference 5 4) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2458 + difference 4 5) (sourceB2458 + difference 5 4) sourceC2458) = raw33567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33567; decide +kernel
    rw [ha]
    exact (canonical33567 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2458 + difference 5 0) (sourceB2458 + difference 0 5) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4437) := by
    have ha : (tripleCharges (sourceA2458 + difference 5 0) (sourceB2458 + difference 0 5) sourceC2458) = raw33778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33778; decide +kernel
    rw [ha]
    exact (canonical33778 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2458 + difference 5 1) (sourceB2458 + difference 1 5) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2458 + difference 5 1) (sourceB2458 + difference 1 5) sourceC2458) = raw33779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33779; decide +kernel
    rw [ha]
    exact (canonical33779 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2458 + difference 5 2) (sourceB2458 + difference 2 5) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4791) := by
    have ha : (tripleCharges (sourceA2458 + difference 5 2) (sourceB2458 + difference 2 5) sourceC2458) = raw33780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33780; decide +kernel
    rw [ha]
    exact (canonical33780 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2458 + difference 5 3) (sourceB2458 + difference 3 5) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4850) := by
    have ha : (tripleCharges (sourceA2458 + difference 5 3) (sourceB2458 + difference 3 5) sourceC2458) = raw33781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33781; decide +kernel
    rw [ha]
    exact (canonical33781 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2458 + difference 5 4) (sourceB2458 + difference 4 5) sourceC2458) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4850) := by
    have ha : (tripleCharges (sourceA2458 + difference 5 4) (sourceB2458 + difference 4 5) sourceC2458) = raw33782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2458 sourceB2458 sourceC2458 difference raw33782; decide +kernel
    rw [ha]
    exact (canonical33782 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2458 sourceB2458 sourceC2458
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2458, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2459 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2459 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceC2459 : Charge := ![3, -1, 1, -1, -1, -1]
def sourceForm2459 : Integer.Sparse Master := [(Sum.inr 2077, 1), (Sum.inr 3070, 1), (Sum.inr 3446, 1), (Sum.inr 3558, 2), (Sum.inr 3563, 1), (Sum.inr 4079, -1)]

theorem sourceEq2459 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2459 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2459 + difference 0 0) (sourceB2459 + difference 0 0) sourceC2459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2077) := by
    have ha : (tripleCharges (sourceA2459 + difference 0 0) (sourceB2459 + difference 0 0) sourceC2459) = raw25524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2459 sourceB2459 sourceC2459 difference raw25524; decide +kernel
    rw [ha]
    exact (canonical25524 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2459 + difference 0 1) (sourceB2459 + difference 1 0) sourceC2459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3070) := by
    have ha : (tripleCharges (sourceA2459 + difference 0 1) (sourceB2459 + difference 1 0) sourceC2459) = raw33783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2459 sourceB2459 sourceC2459 difference raw33783; decide +kernel
    rw [ha]
    exact (canonical33783 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2459 + difference 0 2) (sourceB2459 + difference 2 0) sourceC2459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3446) := by
    have ha : (tripleCharges (sourceA2459 + difference 0 2) (sourceB2459 + difference 2 0) sourceC2459) = raw33784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2459 sourceB2459 sourceC2459 difference raw33784; decide +kernel
    rw [ha]
    exact (canonical33784 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2459 + difference 0 3) (sourceB2459 + difference 3 0) sourceC2459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA2459 + difference 0 3) (sourceB2459 + difference 3 0) sourceC2459) = raw33785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2459 sourceB2459 sourceC2459 difference raw33785; decide +kernel
    rw [ha]
    exact (canonical33785 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2459 + difference 0 4) (sourceB2459 + difference 4 0) sourceC2459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA2459 + difference 0 4) (sourceB2459 + difference 4 0) sourceC2459) = raw33786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2459 sourceB2459 sourceC2459 difference raw33786; decide +kernel
    rw [ha]
    exact (canonical33786 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2459 + difference 0 5) (sourceB2459 + difference 5 0) sourceC2459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3563) := by
    have ha : (tripleCharges (sourceA2459 + difference 0 5) (sourceB2459 + difference 5 0) sourceC2459) = raw33787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2459 sourceB2459 sourceC2459 difference raw33787; decide +kernel
    rw [ha]
    exact (canonical33787 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2459 + sourceB2459) sourceC2459) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA2459 + sourceB2459) sourceC2459) = raw25529 := by
      apply Matrix.ext; unfold doubleCharges sourceA2459 sourceB2459 sourceC2459 raw25529; decide +kernel
    rw [ha]
    exact (canonical25529 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2459 sourceB2459 sourceC2459
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2459, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2460 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2460 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceC2460 : Charge := ![3, -1, 1, -1, -1, -1]
def sourceForm2460 : Integer.Sparse Master := [(Sum.inr 1877, 1), (Sum.inr 1879, 2), (Sum.inr 1912, 1), (Sum.inr 2077, 1), (Sum.inr 3446, 1), (Sum.inr 4079, -1)]

theorem sourceEq2460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2460 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2460 + difference 0 2) (sourceB2460 + difference 2 0) sourceC2460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3446) := by
    have ha : (tripleCharges (sourceA2460 + difference 0 2) (sourceB2460 + difference 2 0) sourceC2460) = raw33784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2460 sourceB2460 sourceC2460 difference raw33784; decide +kernel
    rw [ha]
    exact (canonical33784 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2460 + difference 1 2) (sourceB2460 + difference 2 1) sourceC2460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1912) := by
    have ha : (tripleCharges (sourceA2460 + difference 1 2) (sourceB2460 + difference 2 1) sourceC2460) = raw25525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2460 sourceB2460 sourceC2460 difference raw25525; decide +kernel
    rw [ha]
    exact (canonical25525 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2460 + difference 2 2) (sourceB2460 + difference 2 2) sourceC2460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2077) := by
    have ha : (tripleCharges (sourceA2460 + difference 2 2) (sourceB2460 + difference 2 2) sourceC2460) = raw25524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2460 sourceB2460 sourceC2460 difference raw25524; decide +kernel
    rw [ha]
    exact (canonical25524 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2460 + difference 3 2) (sourceB2460 + difference 2 3) sourceC2460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1879) := by
    have ha : (tripleCharges (sourceA2460 + difference 3 2) (sourceB2460 + difference 2 3) sourceC2460) = raw33788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2460 sourceB2460 sourceC2460 difference raw33788; decide +kernel
    rw [ha]
    exact (canonical33788 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2460 + difference 4 2) (sourceB2460 + difference 2 4) sourceC2460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1879) := by
    have ha : (tripleCharges (sourceA2460 + difference 4 2) (sourceB2460 + difference 2 4) sourceC2460) = raw33789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2460 sourceB2460 sourceC2460 difference raw33789; decide +kernel
    rw [ha]
    exact (canonical33789 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2460 + difference 5 2) (sourceB2460 + difference 2 5) sourceC2460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1877) := by
    have ha : (tripleCharges (sourceA2460 + difference 5 2) (sourceB2460 + difference 2 5) sourceC2460) = raw33790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2460 sourceB2460 sourceC2460 difference raw33790; decide +kernel
    rw [ha]
    exact (canonical33790 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2460 + sourceB2460) sourceC2460) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA2460 + sourceB2460) sourceC2460) = raw25529 := by
      apply Matrix.ext; unfold doubleCharges sourceA2460 sourceB2460 sourceC2460 raw25529; decide +kernel
    rw [ha]
    exact (canonical25529 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2460 sourceB2460 sourceC2460
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2460, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2461 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2461 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2461 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm2461 : Integer.Sparse Master := [(Sum.inr 4331, 1), (Sum.inr 4332, 2), (Sum.inr 4351, 1), (Sum.inr 4461, 1), (Sum.inr 4667, 1), (Sum.inr 4668, 2), (Sum.inr 4685, 1), (Sum.inr 4765, 1), (Sum.inr 4775, 2), (Sum.inr 4793, 2), (Sum.inr 4795, 2), (Sum.inr 4802, 2), (Sum.inr 4805, 2), (Sum.inr 4833, 1), (Sum.inr 4869, 1), (Sum.inr 4889, 2), (Sum.inr 4893, 1), (Sum.inr 5231, 1), (Sum.inr 5257, 1), (Sum.inr 5263, 1), (Sum.inr 5265, 2)]

theorem sourceEq2461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2461 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2461 + difference 0 1) (sourceB2461 + difference 1 0) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA2461 + difference 0 1) (sourceB2461 + difference 1 0) sourceC2461) = raw33791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33791; decide +kernel
    rw [ha]
    exact (canonical33791 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2461 + difference 0 2) (sourceB2461 + difference 2 0) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA2461 + difference 0 2) (sourceB2461 + difference 2 0) sourceC2461) = raw33792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33792; decide +kernel
    rw [ha]
    exact (canonical33792 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2461 + difference 0 3) (sourceB2461 + difference 3 0) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA2461 + difference 0 3) (sourceB2461 + difference 3 0) sourceC2461) = raw33793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33793; decide +kernel
    rw [ha]
    exact (canonical33793 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2461 + difference 0 4) (sourceB2461 + difference 4 0) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA2461 + difference 0 4) (sourceB2461 + difference 4 0) sourceC2461) = raw33794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33794; decide +kernel
    rw [ha]
    exact (canonical33794 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2461 + difference 0 5) (sourceB2461 + difference 5 0) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA2461 + difference 0 5) (sourceB2461 + difference 5 0) sourceC2461) = raw33795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33795; decide +kernel
    rw [ha]
    exact (canonical33795 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2461 + difference 1 0) (sourceB2461 + difference 0 1) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA2461 + difference 1 0) (sourceB2461 + difference 0 1) sourceC2461) = raw27198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw27198; decide +kernel
    rw [ha]
    exact (canonical27198 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2461 + difference 1 2) (sourceB2461 + difference 2 1) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2461 + difference 1 2) (sourceB2461 + difference 2 1) sourceC2461) = raw33796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33796; decide +kernel
    rw [ha]
    exact (canonical33796 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2461 + difference 1 3) (sourceB2461 + difference 3 1) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2461 + difference 1 3) (sourceB2461 + difference 3 1) sourceC2461) = raw3762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw3762; decide +kernel
    rw [ha]
    exact (canonical3762 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2461 + difference 1 4) (sourceB2461 + difference 4 1) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2461 + difference 1 4) (sourceB2461 + difference 4 1) sourceC2461) = raw3757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw3757; decide +kernel
    rw [ha]
    exact (canonical3757 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2461 + difference 1 5) (sourceB2461 + difference 5 1) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA2461 + difference 1 5) (sourceB2461 + difference 5 1) sourceC2461) = raw27172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw27172; decide +kernel
    rw [ha]
    exact (canonical27172 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2461 + difference 2 0) (sourceB2461 + difference 0 2) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4351) := by
    have ha : (tripleCharges (sourceA2461 + difference 2 0) (sourceB2461 + difference 0 2) sourceC2461) = raw27197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw27197; decide +kernel
    rw [ha]
    exact (canonical27197 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2461 + difference 2 1) (sourceB2461 + difference 1 2) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4685) := by
    have ha : (tripleCharges (sourceA2461 + difference 2 1) (sourceB2461 + difference 1 2) sourceC2461) = raw33797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33797; decide +kernel
    rw [ha]
    exact (canonical33797 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2461 + difference 2 3) (sourceB2461 + difference 3 2) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2461 + difference 2 3) (sourceB2461 + difference 3 2) sourceC2461) = raw33798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33798; decide +kernel
    rw [ha]
    exact (canonical33798 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2461 + difference 2 4) (sourceB2461 + difference 4 2) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2461 + difference 2 4) (sourceB2461 + difference 4 2) sourceC2461) = raw33799 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33799; decide +kernel
    rw [ha]
    exact (canonical33799 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2461 + difference 2 5) (sourceB2461 + difference 5 2) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA2461 + difference 2 5) (sourceB2461 + difference 5 2) sourceC2461) = raw27171 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw27171; decide +kernel
    rw [ha]
    exact (canonical27171 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2461 + difference 3 0) (sourceB2461 + difference 0 3) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4332) := by
    have ha : (tripleCharges (sourceA2461 + difference 3 0) (sourceB2461 + difference 0 3) sourceC2461) = raw33800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33800; decide +kernel
    rw [ha]
    exact (canonical33800 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2461 + difference 3 1) (sourceB2461 + difference 1 3) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4668) := by
    have ha : (tripleCharges (sourceA2461 + difference 3 1) (sourceB2461 + difference 1 3) sourceC2461) = raw33801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33801; decide +kernel
    rw [ha]
    exact (canonical33801 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2461 + difference 3 2) (sourceB2461 + difference 2 3) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4775) := by
    have ha : (tripleCharges (sourceA2461 + difference 3 2) (sourceB2461 + difference 2 3) sourceC2461) = raw33802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33802; decide +kernel
    rw [ha]
    exact (canonical33802 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2461 + difference 3 4) (sourceB2461 + difference 4 3) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA2461 + difference 3 4) (sourceB2461 + difference 4 3) sourceC2461) = raw33803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33803; decide +kernel
    rw [ha]
    exact (canonical33803 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2461 + difference 3 5) (sourceB2461 + difference 5 3) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2461 + difference 3 5) (sourceB2461 + difference 5 3) sourceC2461) = raw33804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33804; decide +kernel
    rw [ha]
    exact (canonical33804 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2461 + difference 4 0) (sourceB2461 + difference 0 4) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4332) := by
    have ha : (tripleCharges (sourceA2461 + difference 4 0) (sourceB2461 + difference 0 4) sourceC2461) = raw33805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33805; decide +kernel
    rw [ha]
    exact (canonical33805 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2461 + difference 4 1) (sourceB2461 + difference 1 4) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4668) := by
    have ha : (tripleCharges (sourceA2461 + difference 4 1) (sourceB2461 + difference 1 4) sourceC2461) = raw33806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33806; decide +kernel
    rw [ha]
    exact (canonical33806 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2461 + difference 4 2) (sourceB2461 + difference 2 4) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4775) := by
    have ha : (tripleCharges (sourceA2461 + difference 4 2) (sourceB2461 + difference 2 4) sourceC2461) = raw33807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33807; decide +kernel
    rw [ha]
    exact (canonical33807 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2461 + difference 4 3) (sourceB2461 + difference 3 4) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA2461 + difference 4 3) (sourceB2461 + difference 3 4) sourceC2461) = raw33808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33808; decide +kernel
    rw [ha]
    exact (canonical33808 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2461 + difference 4 5) (sourceB2461 + difference 5 4) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2461 + difference 4 5) (sourceB2461 + difference 5 4) sourceC2461) = raw33809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33809; decide +kernel
    rw [ha]
    exact (canonical33809 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2461 + difference 5 0) (sourceB2461 + difference 0 5) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4331) := by
    have ha : (tripleCharges (sourceA2461 + difference 5 0) (sourceB2461 + difference 0 5) sourceC2461) = raw33810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33810; decide +kernel
    rw [ha]
    exact (canonical33810 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2461 + difference 5 1) (sourceB2461 + difference 1 5) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4667) := by
    have ha : (tripleCharges (sourceA2461 + difference 5 1) (sourceB2461 + difference 1 5) sourceC2461) = raw33811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33811; decide +kernel
    rw [ha]
    exact (canonical33811 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2461 + difference 5 2) (sourceB2461 + difference 2 5) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4765) := by
    have ha : (tripleCharges (sourceA2461 + difference 5 2) (sourceB2461 + difference 2 5) sourceC2461) = raw33812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33812; decide +kernel
    rw [ha]
    exact (canonical33812 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2461 + difference 5 3) (sourceB2461 + difference 3 5) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4793) := by
    have ha : (tripleCharges (sourceA2461 + difference 5 3) (sourceB2461 + difference 3 5) sourceC2461) = raw3759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw3759; decide +kernel
    rw [ha]
    exact (canonical3759 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2461 + difference 5 4) (sourceB2461 + difference 4 5) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4793) := by
    have ha : (tripleCharges (sourceA2461 + difference 5 4) (sourceB2461 + difference 4 5) sourceC2461) = raw3754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw3754; decide +kernel
    rw [ha]
    exact (canonical3754 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2461 sourceB2461 sourceC2461
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2461, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2462 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2462 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2462 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm2462 : Integer.Sparse Master := [(Sum.inr 1678, 2), (Sum.inr 1680, 1), (Sum.inr 1684, 1), (Sum.inr 1737, 1), (Sum.inr 2154, 2), (Sum.inr 2156, 1), (Sum.inr 2160, 1), (Sum.inr 2179, 1), (Sum.inr 2202, 2), (Sum.inr 2204, 1), (Sum.inr 2211, 2), (Sum.inr 2213, 2), (Sum.inr 2214, 2), (Sum.inr 2219, 2), (Sum.inr 2263, 1), (Sum.inr 2275, 1), (Sum.inr 2277, 2), (Sum.inr 2676, 1), (Sum.inr 2721, 1), (Sum.inr 2728, 1), (Sum.inr 2730, 2)]

theorem sourceEq2462 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2462 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2462 + difference 0 1) (sourceB2462 + difference 1 0) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA2462 + difference 0 1) (sourceB2462 + difference 1 0) sourceC2462) = raw33813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33813; decide +kernel
    rw [ha]
    exact (canonical33813 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2462 + difference 0 2) (sourceB2462 + difference 2 0) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA2462 + difference 0 2) (sourceB2462 + difference 2 0) sourceC2462) = raw33814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33814; decide +kernel
    rw [ha]
    exact (canonical33814 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2462 + difference 0 3) (sourceB2462 + difference 3 0) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA2462 + difference 0 3) (sourceB2462 + difference 3 0) sourceC2462) = raw33815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33815; decide +kernel
    rw [ha]
    exact (canonical33815 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2462 + difference 0 4) (sourceB2462 + difference 4 0) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA2462 + difference 0 4) (sourceB2462 + difference 4 0) sourceC2462) = raw33816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33816; decide +kernel
    rw [ha]
    exact (canonical33816 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2462 + difference 0 5) (sourceB2462 + difference 5 0) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA2462 + difference 0 5) (sourceB2462 + difference 5 0) sourceC2462) = raw33817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33817; decide +kernel
    rw [ha]
    exact (canonical33817 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2462 + difference 1 0) (sourceB2462 + difference 0 1) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA2462 + difference 1 0) (sourceB2462 + difference 0 1) sourceC2462) = raw33818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33818; decide +kernel
    rw [ha]
    exact (canonical33818 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2462 + difference 1 2) (sourceB2462 + difference 2 1) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA2462 + difference 1 2) (sourceB2462 + difference 2 1) sourceC2462) = raw33819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33819; decide +kernel
    rw [ha]
    exact (canonical33819 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2462 + difference 1 3) (sourceB2462 + difference 3 1) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA2462 + difference 1 3) (sourceB2462 + difference 3 1) sourceC2462) = raw3822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw3822; decide +kernel
    rw [ha]
    exact (canonical3822 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2462 + difference 1 4) (sourceB2462 + difference 4 1) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA2462 + difference 1 4) (sourceB2462 + difference 4 1) sourceC2462) = raw3817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw3817; decide +kernel
    rw [ha]
    exact (canonical3817 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2462 + difference 1 5) (sourceB2462 + difference 5 1) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA2462 + difference 1 5) (sourceB2462 + difference 5 1) sourceC2462) = raw33820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33820; decide +kernel
    rw [ha]
    exact (canonical33820 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2462 + difference 2 0) (sourceB2462 + difference 0 2) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1680) := by
    have ha : (tripleCharges (sourceA2462 + difference 2 0) (sourceB2462 + difference 0 2) sourceC2462) = raw33821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33821; decide +kernel
    rw [ha]
    exact (canonical33821 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2462 + difference 2 1) (sourceB2462 + difference 1 2) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2156) := by
    have ha : (tripleCharges (sourceA2462 + difference 2 1) (sourceB2462 + difference 1 2) sourceC2462) = raw33822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33822; decide +kernel
    rw [ha]
    exact (canonical33822 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2462 + difference 2 3) (sourceB2462 + difference 3 2) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA2462 + difference 2 3) (sourceB2462 + difference 3 2) sourceC2462) = raw33823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33823; decide +kernel
    rw [ha]
    exact (canonical33823 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2462 + difference 2 4) (sourceB2462 + difference 4 2) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA2462 + difference 2 4) (sourceB2462 + difference 4 2) sourceC2462) = raw33824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33824; decide +kernel
    rw [ha]
    exact (canonical33824 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2462 + difference 2 5) (sourceB2462 + difference 5 2) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2204) := by
    have ha : (tripleCharges (sourceA2462 + difference 2 5) (sourceB2462 + difference 5 2) sourceC2462) = raw33825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33825; decide +kernel
    rw [ha]
    exact (canonical33825 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2462 + difference 3 0) (sourceB2462 + difference 0 3) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA2462 + difference 3 0) (sourceB2462 + difference 0 3) sourceC2462) = raw33826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33826; decide +kernel
    rw [ha]
    exact (canonical33826 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2462 + difference 3 1) (sourceB2462 + difference 1 3) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2154) := by
    have ha : (tripleCharges (sourceA2462 + difference 3 1) (sourceB2462 + difference 1 3) sourceC2462) = raw33827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33827; decide +kernel
    rw [ha]
    exact (canonical33827 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2462 + difference 3 2) (sourceB2462 + difference 2 3) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2211) := by
    have ha : (tripleCharges (sourceA2462 + difference 3 2) (sourceB2462 + difference 2 3) sourceC2462) = raw33828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33828; decide +kernel
    rw [ha]
    exact (canonical33828 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2462 + difference 3 4) (sourceB2462 + difference 4 3) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2462 + difference 3 4) (sourceB2462 + difference 4 3) sourceC2462) = raw33829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33829; decide +kernel
    rw [ha]
    exact (canonical33829 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2462 + difference 3 5) (sourceB2462 + difference 5 3) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA2462 + difference 3 5) (sourceB2462 + difference 5 3) sourceC2462) = raw33830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33830; decide +kernel
    rw [ha]
    exact (canonical33830 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2462 + difference 4 0) (sourceB2462 + difference 0 4) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA2462 + difference 4 0) (sourceB2462 + difference 0 4) sourceC2462) = raw33831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33831; decide +kernel
    rw [ha]
    exact (canonical33831 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2462 + difference 4 1) (sourceB2462 + difference 1 4) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2154) := by
    have ha : (tripleCharges (sourceA2462 + difference 4 1) (sourceB2462 + difference 1 4) sourceC2462) = raw33832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33832; decide +kernel
    rw [ha]
    exact (canonical33832 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2462 + difference 4 2) (sourceB2462 + difference 2 4) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2211) := by
    have ha : (tripleCharges (sourceA2462 + difference 4 2) (sourceB2462 + difference 2 4) sourceC2462) = raw33833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33833; decide +kernel
    rw [ha]
    exact (canonical33833 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2462 + difference 4 3) (sourceB2462 + difference 3 4) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2462 + difference 4 3) (sourceB2462 + difference 3 4) sourceC2462) = raw33834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33834; decide +kernel
    rw [ha]
    exact (canonical33834 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2462 + difference 4 5) (sourceB2462 + difference 5 4) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA2462 + difference 4 5) (sourceB2462 + difference 5 4) sourceC2462) = raw33835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33835; decide +kernel
    rw [ha]
    exact (canonical33835 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2462 + difference 5 0) (sourceB2462 + difference 0 5) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1684) := by
    have ha : (tripleCharges (sourceA2462 + difference 5 0) (sourceB2462 + difference 0 5) sourceC2462) = raw33836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33836; decide +kernel
    rw [ha]
    exact (canonical33836 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2462 + difference 5 1) (sourceB2462 + difference 1 5) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2160) := by
    have ha : (tripleCharges (sourceA2462 + difference 5 1) (sourceB2462 + difference 1 5) sourceC2462) = raw33837 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33837; decide +kernel
    rw [ha]
    exact (canonical33837 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2462 + difference 5 2) (sourceB2462 + difference 2 5) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2179) := by
    have ha : (tripleCharges (sourceA2462 + difference 5 2) (sourceB2462 + difference 2 5) sourceC2462) = raw33838 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33838; decide +kernel
    rw [ha]
    exact (canonical33838 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2462 + difference 5 3) (sourceB2462 + difference 3 5) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2219) := by
    have ha : (tripleCharges (sourceA2462 + difference 5 3) (sourceB2462 + difference 3 5) sourceC2462) = raw3819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw3819; decide +kernel
    rw [ha]
    exact (canonical3819 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2462 + difference 5 4) (sourceB2462 + difference 4 5) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2219) := by
    have ha : (tripleCharges (sourceA2462 + difference 5 4) (sourceB2462 + difference 4 5) sourceC2462) = raw3814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw3814; decide +kernel
    rw [ha]
    exact (canonical3814 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2462 sourceB2462 sourceC2462
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2462, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2463 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2463 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2463 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm2463 : Integer.Sparse Master := [(Sum.inr 1793, 1), (Sum.inr 1794, 2), (Sum.inr 1811, 1), (Sum.inr 2023, 1), (Sum.inr 3378, 1), (Sum.inr 4083, -1)]

theorem sourceEq2463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2463 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2463 + difference 0 1) (sourceB2463 + difference 1 0) sourceC2463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3378) := by
    have ha : (tripleCharges (sourceA2463 + difference 0 1) (sourceB2463 + difference 1 0) sourceC2463) = raw33839 := by
      apply Matrix.ext; unfold tripleCharges sourceA2463 sourceB2463 sourceC2463 difference raw33839; decide +kernel
    rw [ha]
    exact (canonical33839 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2463 + difference 1 1) (sourceB2463 + difference 1 1) sourceC2463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA2463 + difference 1 1) (sourceB2463 + difference 1 1) sourceC2463) = raw33840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2463 sourceB2463 sourceC2463 difference raw33840; decide +kernel
    rw [ha]
    exact (canonical33840 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2463 + difference 2 1) (sourceB2463 + difference 1 2) sourceC2463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1811) := by
    have ha : (tripleCharges (sourceA2463 + difference 2 1) (sourceB2463 + difference 1 2) sourceC2463) = raw33841 := by
      apply Matrix.ext; unfold tripleCharges sourceA2463 sourceB2463 sourceC2463 difference raw33841; decide +kernel
    rw [ha]
    exact (canonical33841 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2463 + difference 3 1) (sourceB2463 + difference 1 3) sourceC2463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1794) := by
    have ha : (tripleCharges (sourceA2463 + difference 3 1) (sourceB2463 + difference 1 3) sourceC2463) = raw33842 := by
      apply Matrix.ext; unfold tripleCharges sourceA2463 sourceB2463 sourceC2463 difference raw33842; decide +kernel
    rw [ha]
    exact (canonical33842 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2463 + difference 4 1) (sourceB2463 + difference 1 4) sourceC2463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1794) := by
    have ha : (tripleCharges (sourceA2463 + difference 4 1) (sourceB2463 + difference 1 4) sourceC2463) = raw33843 := by
      apply Matrix.ext; unfold tripleCharges sourceA2463 sourceB2463 sourceC2463 difference raw33843; decide +kernel
    rw [ha]
    exact (canonical33843 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2463 + difference 5 1) (sourceB2463 + difference 1 5) sourceC2463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1793) := by
    have ha : (tripleCharges (sourceA2463 + difference 5 1) (sourceB2463 + difference 1 5) sourceC2463) = raw33844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2463 sourceB2463 sourceC2463 difference raw33844; decide +kernel
    rw [ha]
    exact (canonical33844 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2463 + sourceB2463) sourceC2463) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2463 + sourceB2463) sourceC2463) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA2463 sourceB2463 sourceC2463 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2463 sourceB2463 sourceC2463
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2463, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
