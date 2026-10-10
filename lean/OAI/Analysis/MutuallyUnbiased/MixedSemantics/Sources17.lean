import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical75

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA544 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB544 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC544 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceForm544 : Integer.Sparse Master := [(Sum.inr 995, 1), (Sum.inr 997, 1), (Sum.inr 1001, 2), (Sum.inr 1078, 1), (Sum.inr 2396, 1), (Sum.inr 2397, 1), (Sum.inr 2401, 2), (Sum.inr 2457, 1), (Sum.inr 2460, 2), (Sum.inr 2507, 1), (Sum.inr 2700, 2), (Sum.inr 2702, 2), (Sum.inr 2706, 2), (Sum.inr 2730, 1), (Sum.inr 2731, 2), (Sum.inr 2738, 2), (Sum.inr 2775, 1), (Sum.inr 3571, 1), (Sum.inr 3580, 1), (Sum.inr 3581, 2), (Sum.inr 3887, 1)]

theorem sourceEq544 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm544 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA544 + difference 0 1) (sourceB544 + difference 1 0) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA544 + difference 0 1) (sourceB544 + difference 1 0) sourceC544) = raw9312 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9312; decide +kernel
    rw [ha]
    exact (canonical9312 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA544 + difference 0 2) (sourceB544 + difference 2 0) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA544 + difference 0 2) (sourceB544 + difference 2 0) sourceC544) = raw9313 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9313; decide +kernel
    rw [ha]
    exact (canonical9313 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA544 + difference 0 3) (sourceB544 + difference 3 0) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA544 + difference 0 3) (sourceB544 + difference 3 0) sourceC544) = raw9314 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9314; decide +kernel
    rw [ha]
    exact (canonical9314 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA544 + difference 0 4) (sourceB544 + difference 4 0) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2775) := by
    have ha : (tripleCharges (sourceA544 + difference 0 4) (sourceB544 + difference 4 0) sourceC544) = raw9315 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9315; decide +kernel
    rw [ha]
    exact (canonical9315 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA544 + difference 0 5) (sourceB544 + difference 5 0) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA544 + difference 0 5) (sourceB544 + difference 5 0) sourceC544) = raw9316 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9316; decide +kernel
    rw [ha]
    exact (canonical9316 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA544 + difference 1 0) (sourceB544 + difference 0 1) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2457) := by
    have ha : (tripleCharges (sourceA544 + difference 1 0) (sourceB544 + difference 0 1) sourceC544) = raw9317 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9317; decide +kernel
    rw [ha]
    exact (canonical9317 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA544 + difference 1 2) (sourceB544 + difference 2 1) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2460) := by
    have ha : (tripleCharges (sourceA544 + difference 1 2) (sourceB544 + difference 2 1) sourceC544) = raw9318 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9318; decide +kernel
    rw [ha]
    exact (canonical9318 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA544 + difference 1 3) (sourceB544 + difference 3 1) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2460) := by
    have ha : (tripleCharges (sourceA544 + difference 1 3) (sourceB544 + difference 3 1) sourceC544) = raw9319 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9319; decide +kernel
    rw [ha]
    exact (canonical9319 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA544 + difference 1 4) (sourceB544 + difference 4 1) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2507) := by
    have ha : (tripleCharges (sourceA544 + difference 1 4) (sourceB544 + difference 4 1) sourceC544) = raw9320 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9320; decide +kernel
    rw [ha]
    exact (canonical9320 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA544 + difference 1 5) (sourceB544 + difference 5 1) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA544 + difference 1 5) (sourceB544 + difference 5 1) sourceC544) = raw9321 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9321; decide +kernel
    rw [ha]
    exact (canonical9321 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA544 + difference 2 0) (sourceB544 + difference 0 2) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA544 + difference 2 0) (sourceB544 + difference 0 2) sourceC544) = raw9322 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9322; decide +kernel
    rw [ha]
    exact (canonical9322 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA544 + difference 2 1) (sourceB544 + difference 1 2) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA544 + difference 2 1) (sourceB544 + difference 1 2) sourceC544) = raw9323 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9323; decide +kernel
    rw [ha]
    exact (canonical9323 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA544 + difference 2 3) (sourceB544 + difference 3 2) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA544 + difference 2 3) (sourceB544 + difference 3 2) sourceC544) = raw9324 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9324; decide +kernel
    rw [ha]
    exact (canonical9324 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA544 + difference 2 4) (sourceB544 + difference 4 2) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA544 + difference 2 4) (sourceB544 + difference 4 2) sourceC544) = raw9325 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9325; decide +kernel
    rw [ha]
    exact (canonical9325 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA544 + difference 2 5) (sourceB544 + difference 5 2) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA544 + difference 2 5) (sourceB544 + difference 5 2) sourceC544) = raw9326 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9326; decide +kernel
    rw [ha]
    exact (canonical9326 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA544 + difference 3 0) (sourceB544 + difference 0 3) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA544 + difference 3 0) (sourceB544 + difference 0 3) sourceC544) = raw9327 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9327; decide +kernel
    rw [ha]
    exact (canonical9327 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA544 + difference 3 1) (sourceB544 + difference 1 3) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA544 + difference 3 1) (sourceB544 + difference 1 3) sourceC544) = raw9328 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9328; decide +kernel
    rw [ha]
    exact (canonical9328 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA544 + difference 3 2) (sourceB544 + difference 2 3) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA544 + difference 3 2) (sourceB544 + difference 2 3) sourceC544) = raw9329 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9329; decide +kernel
    rw [ha]
    exact (canonical9329 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA544 + difference 3 4) (sourceB544 + difference 4 3) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA544 + difference 3 4) (sourceB544 + difference 4 3) sourceC544) = raw9330 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9330; decide +kernel
    rw [ha]
    exact (canonical9330 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA544 + difference 3 5) (sourceB544 + difference 5 3) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA544 + difference 3 5) (sourceB544 + difference 5 3) sourceC544) = raw9331 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9331; decide +kernel
    rw [ha]
    exact (canonical9331 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA544 + difference 4 0) (sourceB544 + difference 0 4) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2397) := by
    have ha : (tripleCharges (sourceA544 + difference 4 0) (sourceB544 + difference 0 4) sourceC544) = raw9332 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9332; decide +kernel
    rw [ha]
    exact (canonical9332 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA544 + difference 4 1) (sourceB544 + difference 1 4) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2396) := by
    have ha : (tripleCharges (sourceA544 + difference 4 1) (sourceB544 + difference 1 4) sourceC544) = raw9333 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9333; decide +kernel
    rw [ha]
    exact (canonical9333 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA544 + difference 4 2) (sourceB544 + difference 2 4) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2401) := by
    have ha : (tripleCharges (sourceA544 + difference 4 2) (sourceB544 + difference 2 4) sourceC544) = raw9334 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9334; decide +kernel
    rw [ha]
    exact (canonical9334 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA544 + difference 4 3) (sourceB544 + difference 3 4) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2401) := by
    have ha : (tripleCharges (sourceA544 + difference 4 3) (sourceB544 + difference 3 4) sourceC544) = raw9335 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9335; decide +kernel
    rw [ha]
    exact (canonical9335 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA544 + difference 4 5) (sourceB544 + difference 5 4) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA544 + difference 4 5) (sourceB544 + difference 5 4) sourceC544) = raw9336 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9336; decide +kernel
    rw [ha]
    exact (canonical9336 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA544 + difference 5 0) (sourceB544 + difference 0 5) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 997) := by
    have ha : (tripleCharges (sourceA544 + difference 5 0) (sourceB544 + difference 0 5) sourceC544) = raw9337 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9337; decide +kernel
    rw [ha]
    exact (canonical9337 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA544 + difference 5 1) (sourceB544 + difference 1 5) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 995) := by
    have ha : (tripleCharges (sourceA544 + difference 5 1) (sourceB544 + difference 1 5) sourceC544) = raw9338 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9338; decide +kernel
    rw [ha]
    exact (canonical9338 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA544 + difference 5 2) (sourceB544 + difference 2 5) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1001) := by
    have ha : (tripleCharges (sourceA544 + difference 5 2) (sourceB544 + difference 2 5) sourceC544) = raw9339 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9339; decide +kernel
    rw [ha]
    exact (canonical9339 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA544 + difference 5 3) (sourceB544 + difference 3 5) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1001) := by
    have ha : (tripleCharges (sourceA544 + difference 5 3) (sourceB544 + difference 3 5) sourceC544) = raw9340 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9340; decide +kernel
    rw [ha]
    exact (canonical9340 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA544 + difference 5 4) (sourceB544 + difference 4 5) sourceC544) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1078) := by
    have ha : (tripleCharges (sourceA544 + difference 5 4) (sourceB544 + difference 4 5) sourceC544) = raw9341 := by
      apply Matrix.ext; unfold tripleCharges sourceA544 sourceB544 sourceC544 difference raw9341; decide +kernel
    rw [ha]
    exact (canonical9341 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA544 sourceB544 sourceC544
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm544, Integer.Sparse.eval]
  linarith only [hs]

def sourceA545 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB545 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC545 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceForm545 : Integer.Sparse Master := [(Sum.inr 1250, 1), (Sum.inr 1252, 1), (Sum.inr 1253, 1), (Sum.inr 1270, 2), (Sum.inr 2754, 1), (Sum.inr 4091, -1)]

theorem sourceEq545 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm545 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA545 + difference 0 0) (sourceB545 + difference 0 0) sourceC545) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA545 + difference 0 0) (sourceB545 + difference 0 0) sourceC545) = raw9342 := by
      apply Matrix.ext; unfold tripleCharges sourceA545 sourceB545 sourceC545 difference raw9342; decide +kernel
    rw [ha]
    exact (canonical9342 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA545 + difference 1 0) (sourceB545 + difference 0 1) sourceC545) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1250) := by
    have ha : (tripleCharges (sourceA545 + difference 1 0) (sourceB545 + difference 0 1) sourceC545) = raw9343 := by
      apply Matrix.ext; unfold tripleCharges sourceA545 sourceB545 sourceC545 difference raw9343; decide +kernel
    rw [ha]
    exact (canonical9343 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA545 + difference 2 0) (sourceB545 + difference 0 2) sourceC545) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA545 + difference 2 0) (sourceB545 + difference 0 2) sourceC545) = raw9344 := by
      apply Matrix.ext; unfold tripleCharges sourceA545 sourceB545 sourceC545 difference raw9344; decide +kernel
    rw [ha]
    exact (canonical9344 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA545 + difference 3 0) (sourceB545 + difference 0 3) sourceC545) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA545 + difference 3 0) (sourceB545 + difference 0 3) sourceC545) = raw9345 := by
      apply Matrix.ext; unfold tripleCharges sourceA545 sourceB545 sourceC545 difference raw9345; decide +kernel
    rw [ha]
    exact (canonical9345 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA545 + difference 4 0) (sourceB545 + difference 0 4) sourceC545) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1253) := by
    have ha : (tripleCharges (sourceA545 + difference 4 0) (sourceB545 + difference 0 4) sourceC545) = raw9346 := by
      apply Matrix.ext; unfold tripleCharges sourceA545 sourceB545 sourceC545 difference raw9346; decide +kernel
    rw [ha]
    exact (canonical9346 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA545 + difference 5 0) (sourceB545 + difference 0 5) sourceC545) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1252) := by
    have ha : (tripleCharges (sourceA545 + difference 5 0) (sourceB545 + difference 0 5) sourceC545) = raw9347 := by
      apply Matrix.ext; unfold tripleCharges sourceA545 sourceB545 sourceC545 difference raw9347; decide +kernel
    rw [ha]
    exact (canonical9347 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA545 + sourceB545) sourceC545) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA545 + sourceB545) sourceC545) = raw9348 := by
      apply Matrix.ext; unfold doubleCharges sourceA545 sourceB545 sourceC545 raw9348; decide +kernel
    rw [ha]
    exact (canonical9348 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA545 sourceB545 sourceC545
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm545, Integer.Sparse.eval]
  linarith only [hs]

def sourceA546 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB546 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC546 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceForm546 : Integer.Sparse Master := [(Sum.inr 1250, 1), (Sum.inr 2625, 2), (Sum.inr 2746, 1), (Sum.inr 2750, 1), (Sum.inr 2754, 1), (Sum.inr 4091, -1)]

theorem sourceEq546 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm546 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA546 + difference 1 0) (sourceB546 + difference 0 1) sourceC546) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1250) := by
    have ha : (tripleCharges (sourceA546 + difference 1 0) (sourceB546 + difference 0 1) sourceC546) = raw9343 := by
      apply Matrix.ext; unfold tripleCharges sourceA546 sourceB546 sourceC546 difference raw9343; decide +kernel
    rw [ha]
    exact (canonical9343 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA546 + difference 1 1) (sourceB546 + difference 1 1) sourceC546) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA546 + difference 1 1) (sourceB546 + difference 1 1) sourceC546) = raw9342 := by
      apply Matrix.ext; unfold tripleCharges sourceA546 sourceB546 sourceC546 difference raw9342; decide +kernel
    rw [ha]
    exact (canonical9342 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA546 + difference 1 2) (sourceB546 + difference 2 1) sourceC546) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2625) := by
    have ha : (tripleCharges (sourceA546 + difference 1 2) (sourceB546 + difference 2 1) sourceC546) = raw9349 := by
      apply Matrix.ext; unfold tripleCharges sourceA546 sourceB546 sourceC546 difference raw9349; decide +kernel
    rw [ha]
    exact (canonical9349 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA546 + difference 1 3) (sourceB546 + difference 3 1) sourceC546) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2625) := by
    have ha : (tripleCharges (sourceA546 + difference 1 3) (sourceB546 + difference 3 1) sourceC546) = raw9350 := by
      apply Matrix.ext; unfold tripleCharges sourceA546 sourceB546 sourceC546 difference raw9350; decide +kernel
    rw [ha]
    exact (canonical9350 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA546 + difference 1 4) (sourceB546 + difference 4 1) sourceC546) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2746) := by
    have ha : (tripleCharges (sourceA546 + difference 1 4) (sourceB546 + difference 4 1) sourceC546) = raw9351 := by
      apply Matrix.ext; unfold tripleCharges sourceA546 sourceB546 sourceC546 difference raw9351; decide +kernel
    rw [ha]
    exact (canonical9351 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA546 + difference 1 5) (sourceB546 + difference 5 1) sourceC546) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA546 + difference 1 5) (sourceB546 + difference 5 1) sourceC546) = raw9352 := by
      apply Matrix.ext; unfold tripleCharges sourceA546 sourceB546 sourceC546 difference raw9352; decide +kernel
    rw [ha]
    exact (canonical9352 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA546 + sourceB546) sourceC546) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA546 + sourceB546) sourceC546) = raw9348 := by
      apply Matrix.ext; unfold doubleCharges sourceA546 sourceB546 sourceC546 raw9348; decide +kernel
    rw [ha]
    exact (canonical9348 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA546 sourceB546 sourceC546
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm546, Integer.Sparse.eval]
  linarith only [hs]

def sourceA547 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB547 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC547 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceForm547 : Integer.Sparse Master := [(Sum.inr 1421, 1), (Sum.inr 2564, 1), (Sum.inr 2573, 2), (Sum.inr 2754, 1), (Sum.inr 3037, 1), (Sum.inr 4091, -1)]

theorem sourceEq547 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm547 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA547 + difference 0 1) (sourceB547 + difference 1 0) sourceC547) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA547 + difference 0 1) (sourceB547 + difference 1 0) sourceC547) = raw9353 := by
      apply Matrix.ext; unfold tripleCharges sourceA547 sourceB547 sourceC547 difference raw9353; decide +kernel
    rw [ha]
    exact (canonical9353 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA547 + difference 1 1) (sourceB547 + difference 1 1) sourceC547) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA547 + difference 1 1) (sourceB547 + difference 1 1) sourceC547) = raw9342 := by
      apply Matrix.ext; unfold tripleCharges sourceA547 sourceB547 sourceC547 difference raw9342; decide +kernel
    rw [ha]
    exact (canonical9342 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA547 + difference 2 1) (sourceB547 + difference 1 2) sourceC547) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA547 + difference 2 1) (sourceB547 + difference 1 2) sourceC547) = raw9354 := by
      apply Matrix.ext; unfold tripleCharges sourceA547 sourceB547 sourceC547 difference raw9354; decide +kernel
    rw [ha]
    exact (canonical9354 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA547 + difference 3 1) (sourceB547 + difference 1 3) sourceC547) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA547 + difference 3 1) (sourceB547 + difference 1 3) sourceC547) = raw9355 := by
      apply Matrix.ext; unfold tripleCharges sourceA547 sourceB547 sourceC547 difference raw9355; decide +kernel
    rw [ha]
    exact (canonical9355 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA547 + difference 4 1) (sourceB547 + difference 1 4) sourceC547) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2564) := by
    have ha : (tripleCharges (sourceA547 + difference 4 1) (sourceB547 + difference 1 4) sourceC547) = raw9356 := by
      apply Matrix.ext; unfold tripleCharges sourceA547 sourceB547 sourceC547 difference raw9356; decide +kernel
    rw [ha]
    exact (canonical9356 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA547 + difference 5 1) (sourceB547 + difference 1 5) sourceC547) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1421) := by
    have ha : (tripleCharges (sourceA547 + difference 5 1) (sourceB547 + difference 1 5) sourceC547) = raw9357 := by
      apply Matrix.ext; unfold tripleCharges sourceA547 sourceB547 sourceC547 difference raw9357; decide +kernel
    rw [ha]
    exact (canonical9357 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA547 + sourceB547) sourceC547) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA547 + sourceB547) sourceC547) = raw9348 := by
      apply Matrix.ext; unfold doubleCharges sourceA547 sourceB547 sourceC547 raw9348; decide +kernel
    rw [ha]
    exact (canonical9348 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA547 sourceB547 sourceC547
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm547, Integer.Sparse.eval]
  linarith only [hs]

def sourceA548 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB548 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC548 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceForm548 : Integer.Sparse Master := [(Sum.inr 1270, 1), (Sum.inr 2573, 1), (Sum.inr 2641, 1), (Sum.inr 2754, 2), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

theorem sourceEq548 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm548 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA548 + difference 2 0) (sourceB548 + difference 0 2) sourceC548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA548 + difference 2 0) (sourceB548 + difference 0 2) sourceC548) = raw9344 := by
      apply Matrix.ext; unfold tripleCharges sourceA548 sourceB548 sourceC548 difference raw9344; decide +kernel
    rw [ha]
    exact (canonical9344 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA548 + difference 2 1) (sourceB548 + difference 1 2) sourceC548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA548 + difference 2 1) (sourceB548 + difference 1 2) sourceC548) = raw9354 := by
      apply Matrix.ext; unfold tripleCharges sourceA548 sourceB548 sourceC548 difference raw9354; decide +kernel
    rw [ha]
    exact (canonical9354 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA548 + difference 2 2) (sourceB548 + difference 2 2) sourceC548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA548 + difference 2 2) (sourceB548 + difference 2 2) sourceC548) = raw9342 := by
      apply Matrix.ext; unfold tripleCharges sourceA548 sourceB548 sourceC548 difference raw9342; decide +kernel
    rw [ha]
    exact (canonical9342 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA548 + difference 2 3) (sourceB548 + difference 3 2) sourceC548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2641) := by
    have ha : (tripleCharges (sourceA548 + difference 2 3) (sourceB548 + difference 3 2) sourceC548) = raw9358 := by
      apply Matrix.ext; unfold tripleCharges sourceA548 sourceB548 sourceC548 difference raw9358; decide +kernel
    rw [ha]
    exact (canonical9358 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA548 + difference 2 4) (sourceB548 + difference 4 2) sourceC548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA548 + difference 2 4) (sourceB548 + difference 4 2) sourceC548) = raw9359 := by
      apply Matrix.ext; unfold tripleCharges sourceA548 sourceB548 sourceC548 difference raw9359; decide +kernel
    rw [ha]
    exact (canonical9359 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA548 + difference 2 5) (sourceB548 + difference 5 2) sourceC548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA548 + difference 2 5) (sourceB548 + difference 5 2) sourceC548) = raw9360 := by
      apply Matrix.ext; unfold tripleCharges sourceA548 sourceB548 sourceC548 difference raw9360; decide +kernel
    rw [ha]
    exact (canonical9360 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA548 + sourceB548) sourceC548) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA548 + sourceB548) sourceC548) = raw9348 := by
      apply Matrix.ext; unfold doubleCharges sourceA548 sourceB548 sourceC548 raw9348; decide +kernel
    rw [ha]
    exact (canonical9348 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA548 sourceB548 sourceC548
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm548, Integer.Sparse.eval]
  linarith only [hs]

def sourceA549 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB549 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC549 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceForm549 : Integer.Sparse Master := [(Sum.inr 4441, 1), (Sum.inr 4442, 1), (Sum.inr 4443, 1), (Sum.inr 4462, 2), (Sum.inr 4792, 1), (Sum.inr 4807, 2), (Sum.inr 4890, 1), (Sum.inr 5066, 1), (Sum.inr 5077, 2), (Sum.inr 5150, 2), (Sum.inr 5151, 2), (Sum.inr 5173, 2), (Sum.inr 5256, 1), (Sum.inr 5270, 1), (Sum.inr 5271, 2), (Sum.inr 5278, 1), (Sum.inr 5279, 1), (Sum.inr 5288, 2), (Sum.inr 5290, 1), (Sum.inr 5295, 2), (Sum.inr 5306, 1)]

theorem sourceEq549 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm549 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA549 + difference 0 1) (sourceB549 + difference 1 0) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA549 + difference 0 1) (sourceB549 + difference 1 0) sourceC549) = raw9361 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9361; decide +kernel
    rw [ha]
    exact (canonical9361 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA549 + difference 0 2) (sourceB549 + difference 2 0) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA549 + difference 0 2) (sourceB549 + difference 2 0) sourceC549) = raw9362 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9362; decide +kernel
    rw [ha]
    exact (canonical9362 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA549 + difference 0 3) (sourceB549 + difference 3 0) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA549 + difference 0 3) (sourceB549 + difference 3 0) sourceC549) = raw9363 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9363; decide +kernel
    rw [ha]
    exact (canonical9363 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA549 + difference 0 4) (sourceB549 + difference 4 0) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA549 + difference 0 4) (sourceB549 + difference 4 0) sourceC549) = raw9364 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9364; decide +kernel
    rw [ha]
    exact (canonical9364 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA549 + difference 0 5) (sourceB549 + difference 5 0) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA549 + difference 0 5) (sourceB549 + difference 5 0) sourceC549) = raw9365 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9365; decide +kernel
    rw [ha]
    exact (canonical9365 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA549 + difference 1 0) (sourceB549 + difference 0 1) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4441) := by
    have ha : (tripleCharges (sourceA549 + difference 1 0) (sourceB549 + difference 0 1) sourceC549) = raw9366 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9366; decide +kernel
    rw [ha]
    exact (canonical9366 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA549 + difference 1 2) (sourceB549 + difference 2 1) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA549 + difference 1 2) (sourceB549 + difference 2 1) sourceC549) = raw9367 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9367; decide +kernel
    rw [ha]
    exact (canonical9367 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA549 + difference 1 3) (sourceB549 + difference 3 1) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA549 + difference 1 3) (sourceB549 + difference 3 1) sourceC549) = raw9368 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9368; decide +kernel
    rw [ha]
    exact (canonical9368 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA549 + difference 1 4) (sourceB549 + difference 4 1) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA549 + difference 1 4) (sourceB549 + difference 4 1) sourceC549) = raw9369 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9369; decide +kernel
    rw [ha]
    exact (canonical9369 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA549 + difference 1 5) (sourceB549 + difference 5 1) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5278) := by
    have ha : (tripleCharges (sourceA549 + difference 1 5) (sourceB549 + difference 5 1) sourceC549) = raw9370 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9370; decide +kernel
    rw [ha]
    exact (canonical9370 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA549 + difference 2 0) (sourceB549 + difference 0 2) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4462) := by
    have ha : (tripleCharges (sourceA549 + difference 2 0) (sourceB549 + difference 0 2) sourceC549) = raw9371 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9371; decide +kernel
    rw [ha]
    exact (canonical9371 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA549 + difference 2 1) (sourceB549 + difference 1 2) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5077) := by
    have ha : (tripleCharges (sourceA549 + difference 2 1) (sourceB549 + difference 1 2) sourceC549) = raw9372 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9372; decide +kernel
    rw [ha]
    exact (canonical9372 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA549 + difference 2 3) (sourceB549 + difference 3 2) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA549 + difference 2 3) (sourceB549 + difference 3 2) sourceC549) = raw9373 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9373; decide +kernel
    rw [ha]
    exact (canonical9373 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA549 + difference 2 4) (sourceB549 + difference 4 2) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA549 + difference 2 4) (sourceB549 + difference 4 2) sourceC549) = raw9374 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9374; decide +kernel
    rw [ha]
    exact (canonical9374 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA549 + difference 2 5) (sourceB549 + difference 5 2) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5288) := by
    have ha : (tripleCharges (sourceA549 + difference 2 5) (sourceB549 + difference 5 2) sourceC549) = raw9375 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9375; decide +kernel
    rw [ha]
    exact (canonical9375 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA549 + difference 3 0) (sourceB549 + difference 0 3) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4462) := by
    have ha : (tripleCharges (sourceA549 + difference 3 0) (sourceB549 + difference 0 3) sourceC549) = raw9376 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9376; decide +kernel
    rw [ha]
    exact (canonical9376 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA549 + difference 3 1) (sourceB549 + difference 1 3) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5077) := by
    have ha : (tripleCharges (sourceA549 + difference 3 1) (sourceB549 + difference 1 3) sourceC549) = raw9377 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9377; decide +kernel
    rw [ha]
    exact (canonical9377 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA549 + difference 3 2) (sourceB549 + difference 2 3) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA549 + difference 3 2) (sourceB549 + difference 2 3) sourceC549) = raw9378 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9378; decide +kernel
    rw [ha]
    exact (canonical9378 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA549 + difference 3 4) (sourceB549 + difference 4 3) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA549 + difference 3 4) (sourceB549 + difference 4 3) sourceC549) = raw9379 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9379; decide +kernel
    rw [ha]
    exact (canonical9379 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA549 + difference 3 5) (sourceB549 + difference 5 3) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5288) := by
    have ha : (tripleCharges (sourceA549 + difference 3 5) (sourceB549 + difference 5 3) sourceC549) = raw9380 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9380; decide +kernel
    rw [ha]
    exact (canonical9380 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA549 + difference 4 0) (sourceB549 + difference 0 4) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4443) := by
    have ha : (tripleCharges (sourceA549 + difference 4 0) (sourceB549 + difference 0 4) sourceC549) = raw9381 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9381; decide +kernel
    rw [ha]
    exact (canonical9381 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA549 + difference 4 1) (sourceB549 + difference 1 4) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5066) := by
    have ha : (tripleCharges (sourceA549 + difference 4 1) (sourceB549 + difference 1 4) sourceC549) = raw9382 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9382; decide +kernel
    rw [ha]
    exact (canonical9382 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA549 + difference 4 2) (sourceB549 + difference 2 4) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA549 + difference 4 2) (sourceB549 + difference 2 4) sourceC549) = raw9383 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9383; decide +kernel
    rw [ha]
    exact (canonical9383 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA549 + difference 4 3) (sourceB549 + difference 3 4) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA549 + difference 4 3) (sourceB549 + difference 3 4) sourceC549) = raw9384 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9384; decide +kernel
    rw [ha]
    exact (canonical9384 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA549 + difference 4 5) (sourceB549 + difference 5 4) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5279) := by
    have ha : (tripleCharges (sourceA549 + difference 4 5) (sourceB549 + difference 5 4) sourceC549) = raw9385 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9385; decide +kernel
    rw [ha]
    exact (canonical9385 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA549 + difference 5 0) (sourceB549 + difference 0 5) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA549 + difference 5 0) (sourceB549 + difference 0 5) sourceC549) = raw9386 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9386; decide +kernel
    rw [ha]
    exact (canonical9386 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA549 + difference 5 1) (sourceB549 + difference 1 5) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA549 + difference 5 1) (sourceB549 + difference 1 5) sourceC549) = raw9387 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9387; decide +kernel
    rw [ha]
    exact (canonical9387 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA549 + difference 5 2) (sourceB549 + difference 2 5) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA549 + difference 5 2) (sourceB549 + difference 2 5) sourceC549) = raw9388 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9388; decide +kernel
    rw [ha]
    exact (canonical9388 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA549 + difference 5 3) (sourceB549 + difference 3 5) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA549 + difference 5 3) (sourceB549 + difference 3 5) sourceC549) = raw9389 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9389; decide +kernel
    rw [ha]
    exact (canonical9389 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA549 + difference 5 4) (sourceB549 + difference 4 5) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA549 + difference 5 4) (sourceB549 + difference 4 5) sourceC549) = raw9390 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9390; decide +kernel
    rw [ha]
    exact (canonical9390 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA549 sourceB549 sourceC549
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm549, Integer.Sparse.eval]
  linarith only [hs]

def sourceA550 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB550 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC550 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceForm550 : Integer.Sparse Master := [(Sum.inr 1023, 1), (Sum.inr 1024, 1), (Sum.inr 1025, 1), (Sum.inr 1045, 2), (Sum.inr 2471, 1), (Sum.inr 2472, 1), (Sum.inr 2484, 2), (Sum.inr 2573, 2), (Sum.inr 2574, 2), (Sum.inr 2575, 2), (Sum.inr 2600, 2), (Sum.inr 2747, 1), (Sum.inr 2748, 1), (Sum.inr 2754, 1), (Sum.inr 2755, 1), (Sum.inr 2760, 2), (Sum.inr 2764, 1), (Sum.inr 2769, 2), (Sum.inr 3085, 1), (Sum.inr 3109, 2), (Sum.inr 3120, 1)]

theorem sourceEq550 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm550 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA550 + difference 0 1) (sourceB550 + difference 1 0) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA550 + difference 0 1) (sourceB550 + difference 1 0) sourceC550) = raw9391 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9391; decide +kernel
    rw [ha]
    exact (canonical9391 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA550 + difference 0 2) (sourceB550 + difference 2 0) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA550 + difference 0 2) (sourceB550 + difference 2 0) sourceC550) = raw9392 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9392; decide +kernel
    rw [ha]
    exact (canonical9392 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA550 + difference 0 3) (sourceB550 + difference 3 0) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA550 + difference 0 3) (sourceB550 + difference 3 0) sourceC550) = raw9393 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9393; decide +kernel
    rw [ha]
    exact (canonical9393 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA550 + difference 0 4) (sourceB550 + difference 4 0) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA550 + difference 0 4) (sourceB550 + difference 4 0) sourceC550) = raw9394 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9394; decide +kernel
    rw [ha]
    exact (canonical9394 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA550 + difference 0 5) (sourceB550 + difference 5 0) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA550 + difference 0 5) (sourceB550 + difference 5 0) sourceC550) = raw9395 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9395; decide +kernel
    rw [ha]
    exact (canonical9395 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA550 + difference 1 0) (sourceB550 + difference 0 1) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1023) := by
    have ha : (tripleCharges (sourceA550 + difference 1 0) (sourceB550 + difference 0 1) sourceC550) = raw9396 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9396; decide +kernel
    rw [ha]
    exact (canonical9396 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA550 + difference 1 2) (sourceB550 + difference 2 1) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA550 + difference 1 2) (sourceB550 + difference 2 1) sourceC550) = raw9397 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9397; decide +kernel
    rw [ha]
    exact (canonical9397 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA550 + difference 1 3) (sourceB550 + difference 3 1) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA550 + difference 1 3) (sourceB550 + difference 3 1) sourceC550) = raw9398 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9398; decide +kernel
    rw [ha]
    exact (canonical9398 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA550 + difference 1 4) (sourceB550 + difference 4 1) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA550 + difference 1 4) (sourceB550 + difference 4 1) sourceC550) = raw9399 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9399; decide +kernel
    rw [ha]
    exact (canonical9399 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA550 + difference 1 5) (sourceB550 + difference 5 1) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2747) := by
    have ha : (tripleCharges (sourceA550 + difference 1 5) (sourceB550 + difference 5 1) sourceC550) = raw9400 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9400; decide +kernel
    rw [ha]
    exact (canonical9400 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA550 + difference 2 0) (sourceB550 + difference 0 2) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1045) := by
    have ha : (tripleCharges (sourceA550 + difference 2 0) (sourceB550 + difference 0 2) sourceC550) = raw9401 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9401; decide +kernel
    rw [ha]
    exact (canonical9401 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA550 + difference 2 1) (sourceB550 + difference 1 2) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2484) := by
    have ha : (tripleCharges (sourceA550 + difference 2 1) (sourceB550 + difference 1 2) sourceC550) = raw9402 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9402; decide +kernel
    rw [ha]
    exact (canonical9402 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA550 + difference 2 3) (sourceB550 + difference 3 2) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2600) := by
    have ha : (tripleCharges (sourceA550 + difference 2 3) (sourceB550 + difference 3 2) sourceC550) = raw9403 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9403; decide +kernel
    rw [ha]
    exact (canonical9403 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA550 + difference 2 4) (sourceB550 + difference 4 2) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA550 + difference 2 4) (sourceB550 + difference 4 2) sourceC550) = raw9404 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9404; decide +kernel
    rw [ha]
    exact (canonical9404 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA550 + difference 2 5) (sourceB550 + difference 5 2) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2760) := by
    have ha : (tripleCharges (sourceA550 + difference 2 5) (sourceB550 + difference 5 2) sourceC550) = raw9405 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9405; decide +kernel
    rw [ha]
    exact (canonical9405 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA550 + difference 3 0) (sourceB550 + difference 0 3) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1045) := by
    have ha : (tripleCharges (sourceA550 + difference 3 0) (sourceB550 + difference 0 3) sourceC550) = raw9406 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9406; decide +kernel
    rw [ha]
    exact (canonical9406 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA550 + difference 3 1) (sourceB550 + difference 1 3) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2484) := by
    have ha : (tripleCharges (sourceA550 + difference 3 1) (sourceB550 + difference 1 3) sourceC550) = raw9407 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9407; decide +kernel
    rw [ha]
    exact (canonical9407 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA550 + difference 3 2) (sourceB550 + difference 2 3) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2600) := by
    have ha : (tripleCharges (sourceA550 + difference 3 2) (sourceB550 + difference 2 3) sourceC550) = raw9408 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9408; decide +kernel
    rw [ha]
    exact (canonical9408 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA550 + difference 3 4) (sourceB550 + difference 4 3) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA550 + difference 3 4) (sourceB550 + difference 4 3) sourceC550) = raw9409 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9409; decide +kernel
    rw [ha]
    exact (canonical9409 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA550 + difference 3 5) (sourceB550 + difference 5 3) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2760) := by
    have ha : (tripleCharges (sourceA550 + difference 3 5) (sourceB550 + difference 5 3) sourceC550) = raw9410 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9410; decide +kernel
    rw [ha]
    exact (canonical9410 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA550 + difference 4 0) (sourceB550 + difference 0 4) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1025) := by
    have ha : (tripleCharges (sourceA550 + difference 4 0) (sourceB550 + difference 0 4) sourceC550) = raw9411 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9411; decide +kernel
    rw [ha]
    exact (canonical9411 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA550 + difference 4 1) (sourceB550 + difference 1 4) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2472) := by
    have ha : (tripleCharges (sourceA550 + difference 4 1) (sourceB550 + difference 1 4) sourceC550) = raw9412 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9412; decide +kernel
    rw [ha]
    exact (canonical9412 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA550 + difference 4 2) (sourceB550 + difference 2 4) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2575) := by
    have ha : (tripleCharges (sourceA550 + difference 4 2) (sourceB550 + difference 2 4) sourceC550) = raw9413 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9413; decide +kernel
    rw [ha]
    exact (canonical9413 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA550 + difference 4 3) (sourceB550 + difference 3 4) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2575) := by
    have ha : (tripleCharges (sourceA550 + difference 4 3) (sourceB550 + difference 3 4) sourceC550) = raw9414 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9414; decide +kernel
    rw [ha]
    exact (canonical9414 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA550 + difference 4 5) (sourceB550 + difference 5 4) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2748) := by
    have ha : (tripleCharges (sourceA550 + difference 4 5) (sourceB550 + difference 5 4) sourceC550) = raw9415 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9415; decide +kernel
    rw [ha]
    exact (canonical9415 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA550 + difference 5 0) (sourceB550 + difference 0 5) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA550 + difference 5 0) (sourceB550 + difference 0 5) sourceC550) = raw9416 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9416; decide +kernel
    rw [ha]
    exact (canonical9416 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA550 + difference 5 1) (sourceB550 + difference 1 5) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA550 + difference 5 1) (sourceB550 + difference 1 5) sourceC550) = raw9417 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9417; decide +kernel
    rw [ha]
    exact (canonical9417 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA550 + difference 5 2) (sourceB550 + difference 2 5) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA550 + difference 5 2) (sourceB550 + difference 2 5) sourceC550) = raw9418 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9418; decide +kernel
    rw [ha]
    exact (canonical9418 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA550 + difference 5 3) (sourceB550 + difference 3 5) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA550 + difference 5 3) (sourceB550 + difference 3 5) sourceC550) = raw9419 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9419; decide +kernel
    rw [ha]
    exact (canonical9419 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA550 + difference 5 4) (sourceB550 + difference 4 5) sourceC550) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA550 + difference 5 4) (sourceB550 + difference 4 5) sourceC550) = raw9420 := by
      apply Matrix.ext; unfold tripleCharges sourceA550 sourceB550 sourceC550 difference raw9420; decide +kernel
    rw [ha]
    exact (canonical9420 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA550 sourceB550 sourceC550
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm550, Integer.Sparse.eval]
  linarith only [hs]

def sourceA551 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB551 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC551 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceForm551 : Integer.Sparse Master := [(Sum.inr 1654, 1), (Sum.inr 1655, 1), (Sum.inr 1656, 2), (Sum.inr 1744, 1), (Sum.inr 2201, 1), (Sum.inr 2224, 2), (Sum.inr 2290, 1), (Sum.inr 2668, 1), (Sum.inr 2681, 2), (Sum.inr 2700, 2), (Sum.inr 2717, 2), (Sum.inr 2720, 1), (Sum.inr 2735, 2), (Sum.inr 2738, 1), (Sum.inr 2739, 2), (Sum.inr 2781, 2), (Sum.inr 2784, 1), (Sum.inr 3050, 1), (Sum.inr 3073, 1), (Sum.inr 3096, 2), (Sum.inr 3099, 1)]

theorem sourceEq551 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm551 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA551 + difference 0 1) (sourceB551 + difference 1 0) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA551 + difference 0 1) (sourceB551 + difference 1 0) sourceC551) = raw9421 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9421; decide +kernel
    rw [ha]
    exact (canonical9421 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA551 + difference 0 2) (sourceB551 + difference 2 0) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA551 + difference 0 2) (sourceB551 + difference 2 0) sourceC551) = raw9422 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9422; decide +kernel
    rw [ha]
    exact (canonical9422 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA551 + difference 0 3) (sourceB551 + difference 3 0) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA551 + difference 0 3) (sourceB551 + difference 3 0) sourceC551) = raw9423 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9423; decide +kernel
    rw [ha]
    exact (canonical9423 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA551 + difference 0 4) (sourceB551 + difference 4 0) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA551 + difference 0 4) (sourceB551 + difference 4 0) sourceC551) = raw9424 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9424; decide +kernel
    rw [ha]
    exact (canonical9424 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA551 + difference 0 5) (sourceB551 + difference 5 0) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA551 + difference 0 5) (sourceB551 + difference 5 0) sourceC551) = raw9425 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9425; decide +kernel
    rw [ha]
    exact (canonical9425 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA551 + difference 1 0) (sourceB551 + difference 0 1) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1654) := by
    have ha : (tripleCharges (sourceA551 + difference 1 0) (sourceB551 + difference 0 1) sourceC551) = raw9426 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9426; decide +kernel
    rw [ha]
    exact (canonical9426 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA551 + difference 1 2) (sourceB551 + difference 2 1) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA551 + difference 1 2) (sourceB551 + difference 2 1) sourceC551) = raw9427 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9427; decide +kernel
    rw [ha]
    exact (canonical9427 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA551 + difference 1 3) (sourceB551 + difference 3 1) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA551 + difference 1 3) (sourceB551 + difference 3 1) sourceC551) = raw9428 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9428; decide +kernel
    rw [ha]
    exact (canonical9428 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA551 + difference 1 4) (sourceB551 + difference 4 1) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA551 + difference 1 4) (sourceB551 + difference 4 1) sourceC551) = raw9429 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9429; decide +kernel
    rw [ha]
    exact (canonical9429 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA551 + difference 1 5) (sourceB551 + difference 5 1) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3073) := by
    have ha : (tripleCharges (sourceA551 + difference 1 5) (sourceB551 + difference 5 1) sourceC551) = raw9430 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9430; decide +kernel
    rw [ha]
    exact (canonical9430 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA551 + difference 2 0) (sourceB551 + difference 0 2) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1656) := by
    have ha : (tripleCharges (sourceA551 + difference 2 0) (sourceB551 + difference 0 2) sourceC551) = raw9431 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9431; decide +kernel
    rw [ha]
    exact (canonical9431 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA551 + difference 2 1) (sourceB551 + difference 1 2) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2717) := by
    have ha : (tripleCharges (sourceA551 + difference 2 1) (sourceB551 + difference 1 2) sourceC551) = raw9432 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9432; decide +kernel
    rw [ha]
    exact (canonical9432 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA551 + difference 2 3) (sourceB551 + difference 3 2) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA551 + difference 2 3) (sourceB551 + difference 3 2) sourceC551) = raw9433 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9433; decide +kernel
    rw [ha]
    exact (canonical9433 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA551 + difference 2 4) (sourceB551 + difference 4 2) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA551 + difference 2 4) (sourceB551 + difference 4 2) sourceC551) = raw9434 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9434; decide +kernel
    rw [ha]
    exact (canonical9434 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA551 + difference 2 5) (sourceB551 + difference 5 2) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3096) := by
    have ha : (tripleCharges (sourceA551 + difference 2 5) (sourceB551 + difference 5 2) sourceC551) = raw9435 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9435; decide +kernel
    rw [ha]
    exact (canonical9435 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA551 + difference 3 0) (sourceB551 + difference 0 3) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1656) := by
    have ha : (tripleCharges (sourceA551 + difference 3 0) (sourceB551 + difference 0 3) sourceC551) = raw9436 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9436; decide +kernel
    rw [ha]
    exact (canonical9436 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA551 + difference 3 1) (sourceB551 + difference 1 3) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2717) := by
    have ha : (tripleCharges (sourceA551 + difference 3 1) (sourceB551 + difference 1 3) sourceC551) = raw9437 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9437; decide +kernel
    rw [ha]
    exact (canonical9437 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA551 + difference 3 2) (sourceB551 + difference 2 3) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA551 + difference 3 2) (sourceB551 + difference 2 3) sourceC551) = raw9438 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9438; decide +kernel
    rw [ha]
    exact (canonical9438 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA551 + difference 3 4) (sourceB551 + difference 4 3) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA551 + difference 3 4) (sourceB551 + difference 4 3) sourceC551) = raw9439 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9439; decide +kernel
    rw [ha]
    exact (canonical9439 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA551 + difference 3 5) (sourceB551 + difference 5 3) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3096) := by
    have ha : (tripleCharges (sourceA551 + difference 3 5) (sourceB551 + difference 5 3) sourceC551) = raw9440 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9440; decide +kernel
    rw [ha]
    exact (canonical9440 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA551 + difference 4 0) (sourceB551 + difference 0 4) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1655) := by
    have ha : (tripleCharges (sourceA551 + difference 4 0) (sourceB551 + difference 0 4) sourceC551) = raw9441 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9441; decide +kernel
    rw [ha]
    exact (canonical9441 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA551 + difference 4 1) (sourceB551 + difference 1 4) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2668) := by
    have ha : (tripleCharges (sourceA551 + difference 4 1) (sourceB551 + difference 1 4) sourceC551) = raw9442 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9442; decide +kernel
    rw [ha]
    exact (canonical9442 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA551 + difference 4 2) (sourceB551 + difference 2 4) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA551 + difference 4 2) (sourceB551 + difference 2 4) sourceC551) = raw9443 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9443; decide +kernel
    rw [ha]
    exact (canonical9443 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA551 + difference 4 3) (sourceB551 + difference 3 4) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA551 + difference 4 3) (sourceB551 + difference 3 4) sourceC551) = raw9444 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9444; decide +kernel
    rw [ha]
    exact (canonical9444 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA551 + difference 4 5) (sourceB551 + difference 5 4) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3050) := by
    have ha : (tripleCharges (sourceA551 + difference 4 5) (sourceB551 + difference 5 4) sourceC551) = raw9445 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9445; decide +kernel
    rw [ha]
    exact (canonical9445 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA551 + difference 5 0) (sourceB551 + difference 0 5) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA551 + difference 5 0) (sourceB551 + difference 0 5) sourceC551) = raw9446 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9446; decide +kernel
    rw [ha]
    exact (canonical9446 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA551 + difference 5 1) (sourceB551 + difference 1 5) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA551 + difference 5 1) (sourceB551 + difference 1 5) sourceC551) = raw9447 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9447; decide +kernel
    rw [ha]
    exact (canonical9447 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA551 + difference 5 2) (sourceB551 + difference 2 5) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA551 + difference 5 2) (sourceB551 + difference 2 5) sourceC551) = raw9448 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9448; decide +kernel
    rw [ha]
    exact (canonical9448 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA551 + difference 5 3) (sourceB551 + difference 3 5) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA551 + difference 5 3) (sourceB551 + difference 3 5) sourceC551) = raw9449 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9449; decide +kernel
    rw [ha]
    exact (canonical9449 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA551 + difference 5 4) (sourceB551 + difference 4 5) sourceC551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA551 + difference 5 4) (sourceB551 + difference 4 5) sourceC551) = raw9450 := by
      apply Matrix.ext; unfold tripleCharges sourceA551 sourceB551 sourceC551 difference raw9450; decide +kernel
    rw [ha]
    exact (canonical9450 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA551 sourceB551 sourceC551
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm551, Integer.Sparse.eval]
  linarith only [hs]

def sourceA552 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB552 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC552 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceForm552 : Integer.Sparse Master := [(Sum.inr 3075, 1), (Sum.inr 3525, 1), (Sum.inr 3534, 2), (Sum.inr 3581, 1), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

theorem sourceEq552 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm552 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA552 + difference 0 0) (sourceB552 + difference 0 0) sourceC552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA552 + difference 0 0) (sourceB552 + difference 0 0) sourceC552) = raw9451 := by
      apply Matrix.ext; unfold tripleCharges sourceA552 sourceB552 sourceC552 difference raw9451; decide +kernel
    rw [ha]
    exact (canonical9451 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA552 + difference 0 1) (sourceB552 + difference 1 0) sourceC552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA552 + difference 0 1) (sourceB552 + difference 1 0) sourceC552) = raw9452 := by
      apply Matrix.ext; unfold tripleCharges sourceA552 sourceB552 sourceC552 difference raw9452; decide +kernel
    rw [ha]
    exact (canonical9452 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA552 + difference 0 2) (sourceB552 + difference 2 0) sourceC552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA552 + difference 0 2) (sourceB552 + difference 2 0) sourceC552) = raw9453 := by
      apply Matrix.ext; unfold tripleCharges sourceA552 sourceB552 sourceC552 difference raw9453; decide +kernel
    rw [ha]
    exact (canonical9453 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA552 + difference 0 3) (sourceB552 + difference 3 0) sourceC552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA552 + difference 0 3) (sourceB552 + difference 3 0) sourceC552) = raw9454 := by
      apply Matrix.ext; unfold tripleCharges sourceA552 sourceB552 sourceC552 difference raw9454; decide +kernel
    rw [ha]
    exact (canonical9454 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA552 + difference 0 4) (sourceB552 + difference 4 0) sourceC552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3623) := by
    have ha : (tripleCharges (sourceA552 + difference 0 4) (sourceB552 + difference 4 0) sourceC552) = raw9455 := by
      apply Matrix.ext; unfold tripleCharges sourceA552 sourceB552 sourceC552 difference raw9455; decide +kernel
    rw [ha]
    exact (canonical9455 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA552 + difference 0 5) (sourceB552 + difference 5 0) sourceC552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA552 + difference 0 5) (sourceB552 + difference 5 0) sourceC552) = raw9456 := by
      apply Matrix.ext; unfold tripleCharges sourceA552 sourceB552 sourceC552 difference raw9456; decide +kernel
    rw [ha]
    exact (canonical9456 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA552 + sourceB552) sourceC552) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA552 + sourceB552) sourceC552) = raw9457 := by
      apply Matrix.ext; unfold doubleCharges sourceA552 sourceB552 sourceC552 raw9457; decide +kernel
    rw [ha]
    exact (canonical9457 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA552 sourceB552 sourceC552
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm552, Integer.Sparse.eval]
  linarith only [hs]

def sourceA553 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB553 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC553 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceForm553 : Integer.Sparse Master := [(Sum.inr 1382, 1), (Sum.inr 1385, 1), (Sum.inr 1390, 1), (Sum.inr 1404, 2), (Sum.inr 3075, 1), (Sum.inr 4083, -1)]

theorem sourceEq553 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm553 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA553 + difference 0 0) (sourceB553 + difference 0 0) sourceC553) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA553 + difference 0 0) (sourceB553 + difference 0 0) sourceC553) = raw9451 := by
      apply Matrix.ext; unfold tripleCharges sourceA553 sourceB553 sourceC553 difference raw9451; decide +kernel
    rw [ha]
    exact (canonical9451 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA553 + difference 1 0) (sourceB553 + difference 0 1) sourceC553) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1382) := by
    have ha : (tripleCharges (sourceA553 + difference 1 0) (sourceB553 + difference 0 1) sourceC553) = raw9458 := by
      apply Matrix.ext; unfold tripleCharges sourceA553 sourceB553 sourceC553 difference raw9458; decide +kernel
    rw [ha]
    exact (canonical9458 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA553 + difference 2 0) (sourceB553 + difference 0 2) sourceC553) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1404) := by
    have ha : (tripleCharges (sourceA553 + difference 2 0) (sourceB553 + difference 0 2) sourceC553) = raw9459 := by
      apply Matrix.ext; unfold tripleCharges sourceA553 sourceB553 sourceC553 difference raw9459; decide +kernel
    rw [ha]
    exact (canonical9459 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA553 + difference 3 0) (sourceB553 + difference 0 3) sourceC553) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1404) := by
    have ha : (tripleCharges (sourceA553 + difference 3 0) (sourceB553 + difference 0 3) sourceC553) = raw9460 := by
      apply Matrix.ext; unfold tripleCharges sourceA553 sourceB553 sourceC553 difference raw9460; decide +kernel
    rw [ha]
    exact (canonical9460 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA553 + difference 4 0) (sourceB553 + difference 0 4) sourceC553) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1390) := by
    have ha : (tripleCharges (sourceA553 + difference 4 0) (sourceB553 + difference 0 4) sourceC553) = raw9461 := by
      apply Matrix.ext; unfold tripleCharges sourceA553 sourceB553 sourceC553 difference raw9461; decide +kernel
    rw [ha]
    exact (canonical9461 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA553 + difference 5 0) (sourceB553 + difference 0 5) sourceC553) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1385) := by
    have ha : (tripleCharges (sourceA553 + difference 5 0) (sourceB553 + difference 0 5) sourceC553) = raw9462 := by
      apply Matrix.ext; unfold tripleCharges sourceA553 sourceB553 sourceC553 difference raw9462; decide +kernel
    rw [ha]
    exact (canonical9462 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA553 + sourceB553) sourceC553) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA553 + sourceB553) sourceC553) = raw9457 := by
      apply Matrix.ext; unfold doubleCharges sourceA553 sourceB553 sourceC553 raw9457; decide +kernel
    rw [ha]
    exact (canonical9457 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA553 sourceB553 sourceC553
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm553, Integer.Sparse.eval]
  linarith only [hs]

def sourceA554 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB554 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC554 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceForm554 : Integer.Sparse Master := [(Sum.inr 1382, 1), (Sum.inr 2923, 2), (Sum.inr 3073, 1), (Sum.inr 3075, 2), (Sum.inr 4083, -1)]

theorem sourceEq554 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm554 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA554 + difference 1 0) (sourceB554 + difference 0 1) sourceC554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1382) := by
    have ha : (tripleCharges (sourceA554 + difference 1 0) (sourceB554 + difference 0 1) sourceC554) = raw9458 := by
      apply Matrix.ext; unfold tripleCharges sourceA554 sourceB554 sourceC554 difference raw9458; decide +kernel
    rw [ha]
    exact (canonical9458 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA554 + difference 1 1) (sourceB554 + difference 1 1) sourceC554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA554 + difference 1 1) (sourceB554 + difference 1 1) sourceC554) = raw9451 := by
      apply Matrix.ext; unfold tripleCharges sourceA554 sourceB554 sourceC554 difference raw9451; decide +kernel
    rw [ha]
    exact (canonical9451 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA554 + difference 1 2) (sourceB554 + difference 2 1) sourceC554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA554 + difference 1 2) (sourceB554 + difference 2 1) sourceC554) = raw9463 := by
      apply Matrix.ext; unfold tripleCharges sourceA554 sourceB554 sourceC554 difference raw9463; decide +kernel
    rw [ha]
    exact (canonical9463 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA554 + difference 1 3) (sourceB554 + difference 3 1) sourceC554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA554 + difference 1 3) (sourceB554 + difference 3 1) sourceC554) = raw9464 := by
      apply Matrix.ext; unfold tripleCharges sourceA554 sourceB554 sourceC554 difference raw9464; decide +kernel
    rw [ha]
    exact (canonical9464 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA554 + difference 1 4) (sourceB554 + difference 4 1) sourceC554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA554 + difference 1 4) (sourceB554 + difference 4 1) sourceC554) = raw9465 := by
      apply Matrix.ext; unfold tripleCharges sourceA554 sourceB554 sourceC554 difference raw9465; decide +kernel
    rw [ha]
    exact (canonical9465 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA554 + difference 1 5) (sourceB554 + difference 5 1) sourceC554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3073) := by
    have ha : (tripleCharges (sourceA554 + difference 1 5) (sourceB554 + difference 5 1) sourceC554) = raw9466 := by
      apply Matrix.ext; unfold tripleCharges sourceA554 sourceB554 sourceC554 difference raw9466; decide +kernel
    rw [ha]
    exact (canonical9466 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA554 + sourceB554) sourceC554) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA554 + sourceB554) sourceC554) = raw9457 := by
      apply Matrix.ext; unfold doubleCharges sourceA554 sourceB554 sourceC554 raw9457; decide +kernel
    rw [ha]
    exact (canonical9457 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA554 sourceB554 sourceC554
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm554, Integer.Sparse.eval]
  linarith only [hs]

def sourceA555 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB555 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC555 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceForm555 : Integer.Sparse Master := [(Sum.inr 2009, 1), (Sum.inr 2980, 1), (Sum.inr 2983, 2), (Sum.inr 3075, 1), (Sum.inr 3525, 1), (Sum.inr 4083, -1)]

theorem sourceEq555 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm555 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA555 + difference 0 1) (sourceB555 + difference 1 0) sourceC555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA555 + difference 0 1) (sourceB555 + difference 1 0) sourceC555) = raw9452 := by
      apply Matrix.ext; unfold tripleCharges sourceA555 sourceB555 sourceC555 difference raw9452; decide +kernel
    rw [ha]
    exact (canonical9452 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA555 + difference 1 1) (sourceB555 + difference 1 1) sourceC555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA555 + difference 1 1) (sourceB555 + difference 1 1) sourceC555) = raw9451 := by
      apply Matrix.ext; unfold tripleCharges sourceA555 sourceB555 sourceC555 difference raw9451; decide +kernel
    rw [ha]
    exact (canonical9451 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA555 + difference 2 1) (sourceB555 + difference 1 2) sourceC555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2983) := by
    have ha : (tripleCharges (sourceA555 + difference 2 1) (sourceB555 + difference 1 2) sourceC555) = raw9467 := by
      apply Matrix.ext; unfold tripleCharges sourceA555 sourceB555 sourceC555 difference raw9467; decide +kernel
    rw [ha]
    exact (canonical9467 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA555 + difference 3 1) (sourceB555 + difference 1 3) sourceC555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2983) := by
    have ha : (tripleCharges (sourceA555 + difference 3 1) (sourceB555 + difference 1 3) sourceC555) = raw9468 := by
      apply Matrix.ext; unfold tripleCharges sourceA555 sourceB555 sourceC555 difference raw9468; decide +kernel
    rw [ha]
    exact (canonical9468 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA555 + difference 4 1) (sourceB555 + difference 1 4) sourceC555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2980) := by
    have ha : (tripleCharges (sourceA555 + difference 4 1) (sourceB555 + difference 1 4) sourceC555) = raw9469 := by
      apply Matrix.ext; unfold tripleCharges sourceA555 sourceB555 sourceC555 difference raw9469; decide +kernel
    rw [ha]
    exact (canonical9469 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA555 + difference 5 1) (sourceB555 + difference 1 5) sourceC555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA555 + difference 5 1) (sourceB555 + difference 1 5) sourceC555) = raw9470 := by
      apply Matrix.ext; unfold tripleCharges sourceA555 sourceB555 sourceC555 difference raw9470; decide +kernel
    rw [ha]
    exact (canonical9470 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA555 + sourceB555) sourceC555) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA555 + sourceB555) sourceC555) = raw9457 := by
      apply Matrix.ext; unfold doubleCharges sourceA555 sourceB555 sourceC555 raw9457; decide +kernel
    rw [ha]
    exact (canonical9457 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA555 sourceB555 sourceC555
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm555, Integer.Sparse.eval]
  linarith only [hs]

def sourceA556 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB556 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC556 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceForm556 : Integer.Sparse Master := [(Sum.inr 2025, 1), (Sum.inr 2923, 1), (Sum.inr 2930, 1), (Sum.inr 2952, 1), (Sum.inr 3075, 1), (Sum.inr 3534, 1), (Sum.inr 4083, -1)]

theorem sourceEq556 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm556 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA556 + difference 0 2) (sourceB556 + difference 2 0) sourceC556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA556 + difference 0 2) (sourceB556 + difference 2 0) sourceC556) = raw9453 := by
      apply Matrix.ext; unfold tripleCharges sourceA556 sourceB556 sourceC556 difference raw9453; decide +kernel
    rw [ha]
    exact (canonical9453 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA556 + difference 1 2) (sourceB556 + difference 2 1) sourceC556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA556 + difference 1 2) (sourceB556 + difference 2 1) sourceC556) = raw9463 := by
      apply Matrix.ext; unfold tripleCharges sourceA556 sourceB556 sourceC556 difference raw9463; decide +kernel
    rw [ha]
    exact (canonical9463 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA556 + difference 2 2) (sourceB556 + difference 2 2) sourceC556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA556 + difference 2 2) (sourceB556 + difference 2 2) sourceC556) = raw9451 := by
      apply Matrix.ext; unfold tripleCharges sourceA556 sourceB556 sourceC556 difference raw9451; decide +kernel
    rw [ha]
    exact (canonical9451 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA556 + difference 3 2) (sourceB556 + difference 2 3) sourceC556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA556 + difference 3 2) (sourceB556 + difference 2 3) sourceC556) = raw9471 := by
      apply Matrix.ext; unfold tripleCharges sourceA556 sourceB556 sourceC556 difference raw9471; decide +kernel
    rw [ha]
    exact (canonical9471 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA556 + difference 4 2) (sourceB556 + difference 2 4) sourceC556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA556 + difference 4 2) (sourceB556 + difference 2 4) sourceC556) = raw9472 := by
      apply Matrix.ext; unfold tripleCharges sourceA556 sourceB556 sourceC556 difference raw9472; decide +kernel
    rw [ha]
    exact (canonical9472 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA556 + difference 5 2) (sourceB556 + difference 2 5) sourceC556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA556 + difference 5 2) (sourceB556 + difference 2 5) sourceC556) = raw9473 := by
      apply Matrix.ext; unfold tripleCharges sourceA556 sourceB556 sourceC556 difference raw9473; decide +kernel
    rw [ha]
    exact (canonical9473 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA556 + sourceB556) sourceC556) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA556 + sourceB556) sourceC556) = raw9457 := by
      apply Matrix.ext; unfold doubleCharges sourceA556 sourceB556 sourceC556 raw9457; decide +kernel
    rw [ha]
    exact (canonical9457 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA556 sourceB556 sourceC556
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm556, Integer.Sparse.eval]
  linarith only [hs]

def sourceA557 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB557 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC557 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceForm557 : Integer.Sparse Master := [(Sum.inr 1390, 1), (Sum.inr 2930, 2), (Sum.inr 2980, 1), (Sum.inr 3075, 1), (Sum.inr 3079, 1), (Sum.inr 4083, -1)]

theorem sourceEq557 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm557 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA557 + difference 4 0) (sourceB557 + difference 0 4) sourceC557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1390) := by
    have ha : (tripleCharges (sourceA557 + difference 4 0) (sourceB557 + difference 0 4) sourceC557) = raw9461 := by
      apply Matrix.ext; unfold tripleCharges sourceA557 sourceB557 sourceC557 difference raw9461; decide +kernel
    rw [ha]
    exact (canonical9461 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA557 + difference 4 1) (sourceB557 + difference 1 4) sourceC557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2980) := by
    have ha : (tripleCharges (sourceA557 + difference 4 1) (sourceB557 + difference 1 4) sourceC557) = raw9469 := by
      apply Matrix.ext; unfold tripleCharges sourceA557 sourceB557 sourceC557 difference raw9469; decide +kernel
    rw [ha]
    exact (canonical9469 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA557 + difference 4 2) (sourceB557 + difference 2 4) sourceC557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA557 + difference 4 2) (sourceB557 + difference 2 4) sourceC557) = raw9472 := by
      apply Matrix.ext; unfold tripleCharges sourceA557 sourceB557 sourceC557 difference raw9472; decide +kernel
    rw [ha]
    exact (canonical9472 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA557 + difference 4 3) (sourceB557 + difference 3 4) sourceC557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA557 + difference 4 3) (sourceB557 + difference 3 4) sourceC557) = raw9474 := by
      apply Matrix.ext; unfold tripleCharges sourceA557 sourceB557 sourceC557 difference raw9474; decide +kernel
    rw [ha]
    exact (canonical9474 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA557 + difference 4 4) (sourceB557 + difference 4 4) sourceC557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA557 + difference 4 4) (sourceB557 + difference 4 4) sourceC557) = raw9451 := by
      apply Matrix.ext; unfold tripleCharges sourceA557 sourceB557 sourceC557 difference raw9451; decide +kernel
    rw [ha]
    exact (canonical9451 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA557 + difference 4 5) (sourceB557 + difference 5 4) sourceC557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3079) := by
    have ha : (tripleCharges (sourceA557 + difference 4 5) (sourceB557 + difference 5 4) sourceC557) = raw9475 := by
      apply Matrix.ext; unfold tripleCharges sourceA557 sourceB557 sourceC557 difference raw9475; decide +kernel
    rw [ha]
    exact (canonical9475 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA557 + sourceB557) sourceC557) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA557 + sourceB557) sourceC557) = raw9457 := by
      apply Matrix.ext; unfold doubleCharges sourceA557 sourceB557 sourceC557 raw9457; decide +kernel
    rw [ha]
    exact (canonical9457 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA557 sourceB557 sourceC557
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm557, Integer.Sparse.eval]
  linarith only [hs]

def sourceA558 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB558 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC558 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm558 : Integer.Sparse Master := [(Sum.inr 4598, 1), (Sum.inr 4600, 1), (Sum.inr 4604, 2), (Sum.inr 4613, 1), (Sum.inr 4878, 1), (Sum.inr 4879, 1), (Sum.inr 4880, 2), (Sum.inr 4889, 1), (Sum.inr 5097, 1), (Sum.inr 5099, 1), (Sum.inr 5103, 2), (Sum.inr 5133, 1), (Sum.inr 5136, 2), (Sum.inr 5159, 1), (Sum.inr 5251, 1), (Sum.inr 5270, 2), (Sum.inr 5272, 2), (Sum.inr 5276, 2), (Sum.inr 5284, 1), (Sum.inr 5294, 2), (Sum.inr 5295, 2)]

theorem sourceEq558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm558 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA558 + difference 0 1) (sourceB558 + difference 1 0) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5133) := by
    have ha : (tripleCharges (sourceA558 + difference 0 1) (sourceB558 + difference 1 0) sourceC558) = raw7526 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw7526; decide +kernel
    rw [ha]
    exact (canonical7526 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA558 + difference 0 2) (sourceB558 + difference 2 0) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA558 + difference 0 2) (sourceB558 + difference 2 0) sourceC558) = raw8063 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw8063; decide +kernel
    rw [ha]
    exact (canonical8063 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA558 + difference 0 3) (sourceB558 + difference 3 0) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA558 + difference 0 3) (sourceB558 + difference 3 0) sourceC558) = raw9476 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw9476; decide +kernel
    rw [ha]
    exact (canonical9476 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA558 + difference 0 4) (sourceB558 + difference 4 0) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA558 + difference 0 4) (sourceB558 + difference 4 0) sourceC558) = raw9235 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw9235; decide +kernel
    rw [ha]
    exact (canonical9235 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA558 + difference 0 5) (sourceB558 + difference 5 0) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA558 + difference 0 5) (sourceB558 + difference 5 0) sourceC558) = raw9477 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw9477; decide +kernel
    rw [ha]
    exact (canonical9477 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA558 + difference 1 0) (sourceB558 + difference 0 1) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4878) := by
    have ha : (tripleCharges (sourceA558 + difference 1 0) (sourceB558 + difference 0 1) sourceC558) = raw5682 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw5682; decide +kernel
    rw [ha]
    exact (canonical5682 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA558 + difference 1 2) (sourceB558 + difference 2 1) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA558 + difference 1 2) (sourceB558 + difference 2 1) sourceC558) = raw8065 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw8065; decide +kernel
    rw [ha]
    exact (canonical8065 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA558 + difference 1 3) (sourceB558 + difference 3 1) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA558 + difference 1 3) (sourceB558 + difference 3 1) sourceC558) = raw9478 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw9478; decide +kernel
    rw [ha]
    exact (canonical9478 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA558 + difference 1 4) (sourceB558 + difference 4 1) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5097) := by
    have ha : (tripleCharges (sourceA558 + difference 1 4) (sourceB558 + difference 4 1) sourceC558) = raw5662 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw5662; decide +kernel
    rw [ha]
    exact (canonical5662 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA558 + difference 1 5) (sourceB558 + difference 5 1) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4598) := by
    have ha : (tripleCharges (sourceA558 + difference 1 5) (sourceB558 + difference 5 1) sourceC558) = raw9479 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw9479; decide +kernel
    rw [ha]
    exact (canonical9479 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA558 + difference 2 0) (sourceB558 + difference 0 2) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA558 + difference 2 0) (sourceB558 + difference 0 2) sourceC558) = raw9480 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw9480; decide +kernel
    rw [ha]
    exact (canonical9480 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA558 + difference 2 1) (sourceB558 + difference 1 2) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5136) := by
    have ha : (tripleCharges (sourceA558 + difference 2 1) (sourceB558 + difference 1 2) sourceC558) = raw7532 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw7532; decide +kernel
    rw [ha]
    exact (canonical7532 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA558 + difference 2 3) (sourceB558 + difference 3 2) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA558 + difference 2 3) (sourceB558 + difference 3 2) sourceC558) = raw9481 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw9481; decide +kernel
    rw [ha]
    exact (canonical9481 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA558 + difference 2 4) (sourceB558 + difference 4 2) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA558 + difference 2 4) (sourceB558 + difference 4 2) sourceC558) = raw9238 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw9238; decide +kernel
    rw [ha]
    exact (canonical9238 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA558 + difference 2 5) (sourceB558 + difference 5 2) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4604) := by
    have ha : (tripleCharges (sourceA558 + difference 2 5) (sourceB558 + difference 5 2) sourceC558) = raw9482 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw9482; decide +kernel
    rw [ha]
    exact (canonical9482 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA558 + difference 3 0) (sourceB558 + difference 0 3) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA558 + difference 3 0) (sourceB558 + difference 0 3) sourceC558) = raw9483 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw9483; decide +kernel
    rw [ha]
    exact (canonical9483 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA558 + difference 3 1) (sourceB558 + difference 1 3) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5136) := by
    have ha : (tripleCharges (sourceA558 + difference 3 1) (sourceB558 + difference 1 3) sourceC558) = raw7058 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw7058; decide +kernel
    rw [ha]
    exact (canonical7058 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA558 + difference 3 2) (sourceB558 + difference 2 3) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA558 + difference 3 2) (sourceB558 + difference 2 3) sourceC558) = raw7055 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw7055; decide +kernel
    rw [ha]
    exact (canonical7055 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA558 + difference 3 4) (sourceB558 + difference 4 3) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA558 + difference 3 4) (sourceB558 + difference 4 3) sourceC558) = raw8790 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw8790; decide +kernel
    rw [ha]
    exact (canonical8790 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA558 + difference 3 5) (sourceB558 + difference 5 3) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4604) := by
    have ha : (tripleCharges (sourceA558 + difference 3 5) (sourceB558 + difference 5 3) sourceC558) = raw9484 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw9484; decide +kernel
    rw [ha]
    exact (canonical9484 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA558 + difference 4 0) (sourceB558 + difference 0 4) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA558 + difference 4 0) (sourceB558 + difference 0 4) sourceC558) = raw8279 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw8279; decide +kernel
    rw [ha]
    exact (canonical8279 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA558 + difference 4 1) (sourceB558 + difference 1 4) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5159) := by
    have ha : (tripleCharges (sourceA558 + difference 4 1) (sourceB558 + difference 1 4) sourceC558) = raw6380 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw6380; decide +kernel
    rw [ha]
    exact (canonical6380 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA558 + difference 4 2) (sourceB558 + difference 2 4) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA558 + difference 4 2) (sourceB558 + difference 2 4) sourceC558) = raw6376 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw6376; decide +kernel
    rw [ha]
    exact (canonical6376 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA558 + difference 4 3) (sourceB558 + difference 3 4) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA558 + difference 4 3) (sourceB558 + difference 3 4) sourceC558) = raw7655 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw7655; decide +kernel
    rw [ha]
    exact (canonical7655 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA558 + difference 4 5) (sourceB558 + difference 5 4) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4613) := by
    have ha : (tripleCharges (sourceA558 + difference 4 5) (sourceB558 + difference 5 4) sourceC558) = raw8280 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw8280; decide +kernel
    rw [ha]
    exact (canonical8280 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA558 + difference 5 0) (sourceB558 + difference 0 5) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA558 + difference 5 0) (sourceB558 + difference 0 5) sourceC558) = raw5679 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw5679; decide +kernel
    rw [ha]
    exact (canonical5679 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA558 + difference 5 1) (sourceB558 + difference 1 5) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA558 + difference 5 1) (sourceB558 + difference 1 5) sourceC558) = raw6379 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw6379; decide +kernel
    rw [ha]
    exact (canonical6379 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA558 + difference 5 2) (sourceB558 + difference 2 5) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA558 + difference 5 2) (sourceB558 + difference 2 5) sourceC558) = raw6375 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw6375; decide +kernel
    rw [ha]
    exact (canonical6375 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA558 + difference 5 3) (sourceB558 + difference 3 5) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA558 + difference 5 3) (sourceB558 + difference 3 5) sourceC558) = raw7527 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw7527; decide +kernel
    rw [ha]
    exact (canonical7527 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA558 + difference 5 4) (sourceB558 + difference 4 5) sourceC558) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA558 + difference 5 4) (sourceB558 + difference 4 5) sourceC558) = raw5658 := by
      apply Matrix.ext; unfold tripleCharges sourceA558 sourceB558 sourceC558 difference raw5658; decide +kernel
    rw [ha]
    exact (canonical5658 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA558 sourceB558 sourceC558
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm558, Integer.Sparse.eval]
  linarith only [hs]

def sourceA559 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB559 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC559 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm559 : Integer.Sparse Master := [(Sum.inr 1256, 1), (Sum.inr 1257, 2), (Sum.inr 1270, 1), (Sum.inr 1286, 1), (Sum.inr 2234, 1), (Sum.inr 2245, 1), (Sum.inr 2246, 1), (Sum.inr 2254, 2), (Sum.inr 2710, 1), (Sum.inr 2711, 1), (Sum.inr 2715, 2), (Sum.inr 2746, 1), (Sum.inr 2753, 1), (Sum.inr 2754, 2), (Sum.inr 2759, 2), (Sum.inr 2768, 2), (Sum.inr 2769, 2), (Sum.inr 2777, 2), (Sum.inr 2940, 1), (Sum.inr 3003, 1), (Sum.inr 3113, 2)]

theorem sourceEq559 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm559 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA559 + difference 0 1) (sourceB559 + difference 1 0) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2940) := by
    have ha : (tripleCharges (sourceA559 + difference 0 1) (sourceB559 + difference 1 0) sourceC559) = raw7535 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw7535; decide +kernel
    rw [ha]
    exact (canonical7535 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA559 + difference 0 2) (sourceB559 + difference 2 0) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3113) := by
    have ha : (tripleCharges (sourceA559 + difference 0 2) (sourceB559 + difference 2 0) sourceC559) = raw8067 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw8067; decide +kernel
    rw [ha]
    exact (canonical8067 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA559 + difference 0 3) (sourceB559 + difference 3 0) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3113) := by
    have ha : (tripleCharges (sourceA559 + difference 0 3) (sourceB559 + difference 3 0) sourceC559) = raw9485 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw9485; decide +kernel
    rw [ha]
    exact (canonical9485 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA559 + difference 0 4) (sourceB559 + difference 4 0) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3003) := by
    have ha : (tripleCharges (sourceA559 + difference 0 4) (sourceB559 + difference 4 0) sourceC559) = raw9240 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw9240; decide +kernel
    rw [ha]
    exact (canonical9240 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA559 + difference 0 5) (sourceB559 + difference 5 0) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA559 + difference 0 5) (sourceB559 + difference 5 0) sourceC559) = raw9486 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw9486; decide +kernel
    rw [ha]
    exact (canonical9486 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA559 + difference 1 0) (sourceB559 + difference 0 1) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA559 + difference 1 0) (sourceB559 + difference 0 1) sourceC559) = raw5712 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw5712; decide +kernel
    rw [ha]
    exact (canonical5712 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA559 + difference 1 2) (sourceB559 + difference 2 1) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA559 + difference 1 2) (sourceB559 + difference 2 1) sourceC559) = raw8069 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw8069; decide +kernel
    rw [ha]
    exact (canonical8069 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA559 + difference 1 3) (sourceB559 + difference 3 1) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA559 + difference 1 3) (sourceB559 + difference 3 1) sourceC559) = raw9487 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw9487; decide +kernel
    rw [ha]
    exact (canonical9487 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA559 + difference 1 4) (sourceB559 + difference 4 1) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2746) := by
    have ha : (tripleCharges (sourceA559 + difference 1 4) (sourceB559 + difference 4 1) sourceC559) = raw5692 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw5692; decide +kernel
    rw [ha]
    exact (canonical5692 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA559 + difference 1 5) (sourceB559 + difference 5 1) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1256) := by
    have ha : (tripleCharges (sourceA559 + difference 1 5) (sourceB559 + difference 5 1) sourceC559) = raw9488 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw9488; decide +kernel
    rw [ha]
    exact (canonical9488 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA559 + difference 2 0) (sourceB559 + difference 0 2) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA559 + difference 2 0) (sourceB559 + difference 0 2) sourceC559) = raw9489 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw9489; decide +kernel
    rw [ha]
    exact (canonical9489 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA559 + difference 2 1) (sourceB559 + difference 1 2) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2715) := by
    have ha : (tripleCharges (sourceA559 + difference 2 1) (sourceB559 + difference 1 2) sourceC559) = raw7541 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw7541; decide +kernel
    rw [ha]
    exact (canonical7541 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA559 + difference 2 3) (sourceB559 + difference 3 2) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA559 + difference 2 3) (sourceB559 + difference 3 2) sourceC559) = raw9490 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw9490; decide +kernel
    rw [ha]
    exact (canonical9490 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA559 + difference 2 4) (sourceB559 + difference 4 2) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA559 + difference 2 4) (sourceB559 + difference 4 2) sourceC559) = raw9243 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw9243; decide +kernel
    rw [ha]
    exact (canonical9243 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA559 + difference 2 5) (sourceB559 + difference 5 2) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1257) := by
    have ha : (tripleCharges (sourceA559 + difference 2 5) (sourceB559 + difference 5 2) sourceC559) = raw9491 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw9491; decide +kernel
    rw [ha]
    exact (canonical9491 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA559 + difference 3 0) (sourceB559 + difference 0 3) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA559 + difference 3 0) (sourceB559 + difference 0 3) sourceC559) = raw9492 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw9492; decide +kernel
    rw [ha]
    exact (canonical9492 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA559 + difference 3 1) (sourceB559 + difference 1 3) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2715) := by
    have ha : (tripleCharges (sourceA559 + difference 3 1) (sourceB559 + difference 1 3) sourceC559) = raw7072 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw7072; decide +kernel
    rw [ha]
    exact (canonical7072 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA559 + difference 3 2) (sourceB559 + difference 2 3) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA559 + difference 3 2) (sourceB559 + difference 2 3) sourceC559) = raw7069 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw7069; decide +kernel
    rw [ha]
    exact (canonical7069 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA559 + difference 3 4) (sourceB559 + difference 4 3) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA559 + difference 3 4) (sourceB559 + difference 4 3) sourceC559) = raw9244 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw9244; decide +kernel
    rw [ha]
    exact (canonical9244 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA559 + difference 3 5) (sourceB559 + difference 5 3) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1257) := by
    have ha : (tripleCharges (sourceA559 + difference 3 5) (sourceB559 + difference 5 3) sourceC559) = raw9493 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw9493; decide +kernel
    rw [ha]
    exact (canonical9493 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA559 + difference 4 0) (sourceB559 + difference 0 4) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA559 + difference 4 0) (sourceB559 + difference 0 4) sourceC559) = raw8292 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw8292; decide +kernel
    rw [ha]
    exact (canonical8292 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA559 + difference 4 1) (sourceB559 + difference 1 4) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2711) := by
    have ha : (tripleCharges (sourceA559 + difference 4 1) (sourceB559 + difference 1 4) sourceC559) = raw6402 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw6402; decide +kernel
    rw [ha]
    exact (canonical6402 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA559 + difference 4 2) (sourceB559 + difference 2 4) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA559 + difference 4 2) (sourceB559 + difference 2 4) sourceC559) = raw6398 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw6398; decide +kernel
    rw [ha]
    exact (canonical6398 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA559 + difference 4 3) (sourceB559 + difference 3 4) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA559 + difference 4 3) (sourceB559 + difference 3 4) sourceC559) = raw7671 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw7671; decide +kernel
    rw [ha]
    exact (canonical7671 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA559 + difference 4 5) (sourceB559 + difference 5 4) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1286) := by
    have ha : (tripleCharges (sourceA559 + difference 4 5) (sourceB559 + difference 5 4) sourceC559) = raw8293 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw8293; decide +kernel
    rw [ha]
    exact (canonical8293 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA559 + difference 5 0) (sourceB559 + difference 0 5) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA559 + difference 5 0) (sourceB559 + difference 0 5) sourceC559) = raw5709 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw5709; decide +kernel
    rw [ha]
    exact (canonical5709 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA559 + difference 5 1) (sourceB559 + difference 1 5) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA559 + difference 5 1) (sourceB559 + difference 1 5) sourceC559) = raw6401 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw6401; decide +kernel
    rw [ha]
    exact (canonical6401 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA559 + difference 5 2) (sourceB559 + difference 2 5) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA559 + difference 5 2) (sourceB559 + difference 2 5) sourceC559) = raw6397 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw6397; decide +kernel
    rw [ha]
    exact (canonical6397 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA559 + difference 5 3) (sourceB559 + difference 3 5) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA559 + difference 5 3) (sourceB559 + difference 3 5) sourceC559) = raw7536 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw7536; decide +kernel
    rw [ha]
    exact (canonical7536 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA559 + difference 5 4) (sourceB559 + difference 4 5) sourceC559) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA559 + difference 5 4) (sourceB559 + difference 4 5) sourceC559) = raw5688 := by
      apply Matrix.ext; unfold tripleCharges sourceA559 sourceB559 sourceC559 difference raw5688; decide +kernel
    rw [ha]
    exact (canonical5688 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA559 sourceB559 sourceC559
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm559, Integer.Sparse.eval]
  linarith only [hs]

def sourceA560 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB560 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC560 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm560 : Integer.Sparse Master := [(Sum.inr 2693, 1), (Sum.inr 2702, 1), (Sum.inr 2704, 1), (Sum.inr 2740, 2), (Sum.inr 3015, 2), (Sum.inr 3022, 2), (Sum.inr 3024, 2), (Sum.inr 3052, 2), (Sum.inr 3057, 1), (Sum.inr 3058, 1), (Sum.inr 3063, 1), (Sum.inr 3064, 1), (Sum.inr 3072, 1), (Sum.inr 3075, 2), (Sum.inr 3077, 1), (Sum.inr 3098, 2), (Sum.inr 3101, 2), (Sum.inr 3155, 1), (Sum.inr 3156, 2), (Sum.inr 3158, 1), (Sum.inr 3223, 1)]

theorem sourceEq560 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm560 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA560 + difference 0 1) (sourceB560 + difference 1 0) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA560 + difference 0 1) (sourceB560 + difference 1 0) sourceC560) = raw7544 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw7544; decide +kernel
    rw [ha]
    exact (canonical7544 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA560 + difference 0 2) (sourceB560 + difference 2 0) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA560 + difference 0 2) (sourceB560 + difference 2 0) sourceC560) = raw8301 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw8301; decide +kernel
    rw [ha]
    exact (canonical8301 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA560 + difference 0 3) (sourceB560 + difference 3 0) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA560 + difference 0 3) (sourceB560 + difference 3 0) sourceC560) = raw9494 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw9494; decide +kernel
    rw [ha]
    exact (canonical9494 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA560 + difference 0 4) (sourceB560 + difference 4 0) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA560 + difference 0 4) (sourceB560 + difference 4 0) sourceC560) = raw9246 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw9246; decide +kernel
    rw [ha]
    exact (canonical9246 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA560 + difference 0 5) (sourceB560 + difference 5 0) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA560 + difference 0 5) (sourceB560 + difference 5 0) sourceC560) = raw9495 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw9495; decide +kernel
    rw [ha]
    exact (canonical9495 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA560 + difference 1 0) (sourceB560 + difference 0 1) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3155) := by
    have ha : (tripleCharges (sourceA560 + difference 1 0) (sourceB560 + difference 0 1) sourceC560) = raw5742 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw5742; decide +kernel
    rw [ha]
    exact (canonical5742 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA560 + difference 1 2) (sourceB560 + difference 2 1) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA560 + difference 1 2) (sourceB560 + difference 2 1) sourceC560) = raw8305 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw8305; decide +kernel
    rw [ha]
    exact (canonical8305 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA560 + difference 1 3) (sourceB560 + difference 3 1) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA560 + difference 1 3) (sourceB560 + difference 3 1) sourceC560) = raw9496 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw9496; decide +kernel
    rw [ha]
    exact (canonical9496 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA560 + difference 1 4) (sourceB560 + difference 4 1) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3058) := by
    have ha : (tripleCharges (sourceA560 + difference 1 4) (sourceB560 + difference 4 1) sourceC560) = raw5722 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw5722; decide +kernel
    rw [ha]
    exact (canonical5722 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA560 + difference 1 5) (sourceB560 + difference 5 1) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3057) := by
    have ha : (tripleCharges (sourceA560 + difference 1 5) (sourceB560 + difference 5 1) sourceC560) = raw9497 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw9497; decide +kernel
    rw [ha]
    exact (canonical9497 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA560 + difference 2 0) (sourceB560 + difference 0 2) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA560 + difference 2 0) (sourceB560 + difference 0 2) sourceC560) = raw9498 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw9498; decide +kernel
    rw [ha]
    exact (canonical9498 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA560 + difference 2 1) (sourceB560 + difference 1 2) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3015) := by
    have ha : (tripleCharges (sourceA560 + difference 2 1) (sourceB560 + difference 1 2) sourceC560) = raw7550 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw7550; decide +kernel
    rw [ha]
    exact (canonical7550 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA560 + difference 2 3) (sourceB560 + difference 3 2) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA560 + difference 2 3) (sourceB560 + difference 3 2) sourceC560) = raw9499 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw9499; decide +kernel
    rw [ha]
    exact (canonical9499 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA560 + difference 2 4) (sourceB560 + difference 4 2) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA560 + difference 2 4) (sourceB560 + difference 4 2) sourceC560) = raw9249 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw9249; decide +kernel
    rw [ha]
    exact (canonical9249 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA560 + difference 2 5) (sourceB560 + difference 5 2) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3022) := by
    have ha : (tripleCharges (sourceA560 + difference 2 5) (sourceB560 + difference 5 2) sourceC560) = raw9500 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw9500; decide +kernel
    rw [ha]
    exact (canonical9500 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA560 + difference 3 0) (sourceB560 + difference 0 3) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA560 + difference 3 0) (sourceB560 + difference 0 3) sourceC560) = raw9501 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw9501; decide +kernel
    rw [ha]
    exact (canonical9501 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA560 + difference 3 1) (sourceB560 + difference 1 3) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3015) := by
    have ha : (tripleCharges (sourceA560 + difference 3 1) (sourceB560 + difference 1 3) sourceC560) = raw7086 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw7086; decide +kernel
    rw [ha]
    exact (canonical7086 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA560 + difference 3 2) (sourceB560 + difference 2 3) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA560 + difference 3 2) (sourceB560 + difference 2 3) sourceC560) = raw7083 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw7083; decide +kernel
    rw [ha]
    exact (canonical7083 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA560 + difference 3 4) (sourceB560 + difference 4 3) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA560 + difference 3 4) (sourceB560 + difference 4 3) sourceC560) = raw8798 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw8798; decide +kernel
    rw [ha]
    exact (canonical8798 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA560 + difference 3 5) (sourceB560 + difference 5 3) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3022) := by
    have ha : (tripleCharges (sourceA560 + difference 3 5) (sourceB560 + difference 5 3) sourceC560) = raw9502 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw9502; decide +kernel
    rw [ha]
    exact (canonical9502 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA560 + difference 4 0) (sourceB560 + difference 0 4) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA560 + difference 4 0) (sourceB560 + difference 0 4) sourceC560) = raw8307 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw8307; decide +kernel
    rw [ha]
    exact (canonical8307 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA560 + difference 4 1) (sourceB560 + difference 1 4) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3063) := by
    have ha : (tripleCharges (sourceA560 + difference 4 1) (sourceB560 + difference 1 4) sourceC560) = raw6424 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw6424; decide +kernel
    rw [ha]
    exact (canonical6424 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA560 + difference 4 2) (sourceB560 + difference 2 4) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA560 + difference 4 2) (sourceB560 + difference 2 4) sourceC560) = raw6420 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw6420; decide +kernel
    rw [ha]
    exact (canonical6420 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA560 + difference 4 3) (sourceB560 + difference 3 4) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA560 + difference 4 3) (sourceB560 + difference 3 4) sourceC560) = raw7687 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw7687; decide +kernel
    rw [ha]
    exact (canonical7687 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA560 + difference 4 5) (sourceB560 + difference 5 4) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3072) := by
    have ha : (tripleCharges (sourceA560 + difference 4 5) (sourceB560 + difference 5 4) sourceC560) = raw8308 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw8308; decide +kernel
    rw [ha]
    exact (canonical8308 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA560 + difference 5 0) (sourceB560 + difference 0 5) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA560 + difference 5 0) (sourceB560 + difference 0 5) sourceC560) = raw5739 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw5739; decide +kernel
    rw [ha]
    exact (canonical5739 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA560 + difference 5 1) (sourceB560 + difference 1 5) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA560 + difference 5 1) (sourceB560 + difference 1 5) sourceC560) = raw6423 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw6423; decide +kernel
    rw [ha]
    exact (canonical6423 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA560 + difference 5 2) (sourceB560 + difference 2 5) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA560 + difference 5 2) (sourceB560 + difference 2 5) sourceC560) = raw6419 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw6419; decide +kernel
    rw [ha]
    exact (canonical6419 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA560 + difference 5 3) (sourceB560 + difference 3 5) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA560 + difference 5 3) (sourceB560 + difference 3 5) sourceC560) = raw7545 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw7545; decide +kernel
    rw [ha]
    exact (canonical7545 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA560 + difference 5 4) (sourceB560 + difference 4 5) sourceC560) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA560 + difference 5 4) (sourceB560 + difference 4 5) sourceC560) = raw5718 := by
      apply Matrix.ext; unfold tripleCharges sourceA560 sourceB560 sourceC560 difference raw5718; decide +kernel
    rw [ha]
    exact (canonical5718 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA560 sourceB560 sourceC560
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm560, Integer.Sparse.eval]
  linarith only [hs]

def sourceA561 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB561 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC561 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm561 : Integer.Sparse Master := [(Sum.inr 1234, 1), (Sum.inr 2509, 1), (Sum.inr 2552, 1), (Sum.inr 2738, 1), (Sum.inr 2740, 2), (Sum.inr 4084, -1)]

theorem sourceEq561 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm561 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA561 + difference 0 0) (sourceB561 + difference 0 0) sourceC561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA561 + difference 0 0) (sourceB561 + difference 0 0) sourceC561) = raw7556 := by
      apply Matrix.ext; unfold tripleCharges sourceA561 sourceB561 sourceC561 difference raw7556; decide +kernel
    rw [ha]
    exact (canonical7556 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA561 + difference 0 1) (sourceB561 + difference 1 0) sourceC561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2552) := by
    have ha : (tripleCharges (sourceA561 + difference 0 1) (sourceB561 + difference 1 0) sourceC561) = raw7553 := by
      apply Matrix.ext; unfold tripleCharges sourceA561 sourceB561 sourceC561 difference raw7553; decide +kernel
    rw [ha]
    exact (canonical7553 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA561 + difference 0 2) (sourceB561 + difference 2 0) sourceC561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA561 + difference 0 2) (sourceB561 + difference 2 0) sourceC561) = raw8316 := by
      apply Matrix.ext; unfold tripleCharges sourceA561 sourceB561 sourceC561 difference raw8316; decide +kernel
    rw [ha]
    exact (canonical8316 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA561 + difference 0 3) (sourceB561 + difference 3 0) sourceC561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA561 + difference 0 3) (sourceB561 + difference 3 0) sourceC561) = raw9503 := by
      apply Matrix.ext; unfold tripleCharges sourceA561 sourceB561 sourceC561 difference raw9503; decide +kernel
    rw [ha]
    exact (canonical9503 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA561 + difference 0 4) (sourceB561 + difference 4 0) sourceC561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2509) := by
    have ha : (tripleCharges (sourceA561 + difference 0 4) (sourceB561 + difference 4 0) sourceC561) = raw9251 := by
      apply Matrix.ext; unfold tripleCharges sourceA561 sourceB561 sourceC561 difference raw9251; decide +kernel
    rw [ha]
    exact (canonical9251 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA561 + difference 0 5) (sourceB561 + difference 5 0) sourceC561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1234) := by
    have ha : (tripleCharges (sourceA561 + difference 0 5) (sourceB561 + difference 5 0) sourceC561) = raw9504 := by
      apply Matrix.ext; unfold tripleCharges sourceA561 sourceB561 sourceC561 difference raw9504; decide +kernel
    rw [ha]
    exact (canonical9504 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA561 + sourceB561) sourceC561) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA561 + sourceB561) sourceC561) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA561 sourceB561 sourceC561 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA561 sourceB561 sourceC561
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm561, Integer.Sparse.eval]
  linarith only [hs]

def sourceA562 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB562 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC562 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm562 : Integer.Sparse Master := [(Sum.inr 2131, 1), (Sum.inr 2132, 1), (Sum.inr 2133, 2), (Sum.inr 2277, 1), (Sum.inr 2738, 1), (Sum.inr 4084, -1)]

theorem sourceEq562 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm562 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA562 + difference 0 0) (sourceB562 + difference 0 0) sourceC562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA562 + difference 0 0) (sourceB562 + difference 0 0) sourceC562) = raw7556 := by
      apply Matrix.ext; unfold tripleCharges sourceA562 sourceB562 sourceC562 difference raw7556; decide +kernel
    rw [ha]
    exact (canonical7556 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA562 + difference 1 0) (sourceB562 + difference 0 1) sourceC562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2131) := by
    have ha : (tripleCharges (sourceA562 + difference 1 0) (sourceB562 + difference 0 1) sourceC562) = raw5763 := by
      apply Matrix.ext; unfold tripleCharges sourceA562 sourceB562 sourceC562 difference raw5763; decide +kernel
    rw [ha]
    exact (canonical5763 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA562 + difference 2 0) (sourceB562 + difference 0 2) sourceC562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA562 + difference 2 0) (sourceB562 + difference 0 2) sourceC562) = raw9505 := by
      apply Matrix.ext; unfold tripleCharges sourceA562 sourceB562 sourceC562 difference raw9505; decide +kernel
    rw [ha]
    exact (canonical9505 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA562 + difference 3 0) (sourceB562 + difference 0 3) sourceC562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA562 + difference 3 0) (sourceB562 + difference 0 3) sourceC562) = raw9506 := by
      apply Matrix.ext; unfold tripleCharges sourceA562 sourceB562 sourceC562 difference raw9506; decide +kernel
    rw [ha]
    exact (canonical9506 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA562 + difference 4 0) (sourceB562 + difference 0 4) sourceC562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2132) := by
    have ha : (tripleCharges (sourceA562 + difference 4 0) (sourceB562 + difference 0 4) sourceC562) = raw8319 := by
      apply Matrix.ext; unfold tripleCharges sourceA562 sourceB562 sourceC562 difference raw8319; decide +kernel
    rw [ha]
    exact (canonical8319 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA562 + difference 5 0) (sourceB562 + difference 0 5) sourceC562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA562 + difference 5 0) (sourceB562 + difference 0 5) sourceC562) = raw5760 := by
      apply Matrix.ext; unfold tripleCharges sourceA562 sourceB562 sourceC562 difference raw5760; decide +kernel
    rw [ha]
    exact (canonical5760 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA562 + sourceB562) sourceC562) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA562 + sourceB562) sourceC562) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA562 sourceB562 sourceC562 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA562 sourceB562 sourceC562
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm562, Integer.Sparse.eval]
  linarith only [hs]

def sourceA563 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB563 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC563 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm563 : Integer.Sparse Master := [(Sum.inr 1232, 1), (Sum.inr 2131, 1), (Sum.inr 2507, 1), (Sum.inr 2738, 3), (Sum.inr 4084, -1)]

theorem sourceEq563 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm563 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA563 + difference 1 0) (sourceB563 + difference 0 1) sourceC563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2131) := by
    have ha : (tripleCharges (sourceA563 + difference 1 0) (sourceB563 + difference 0 1) sourceC563) = raw5763 := by
      apply Matrix.ext; unfold tripleCharges sourceA563 sourceB563 sourceC563 difference raw5763; decide +kernel
    rw [ha]
    exact (canonical5763 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA563 + difference 1 1) (sourceB563 + difference 1 1) sourceC563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA563 + difference 1 1) (sourceB563 + difference 1 1) sourceC563) = raw7556 := by
      apply Matrix.ext; unfold tripleCharges sourceA563 sourceB563 sourceC563 difference raw7556; decide +kernel
    rw [ha]
    exact (canonical7556 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA563 + difference 1 2) (sourceB563 + difference 2 1) sourceC563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA563 + difference 1 2) (sourceB563 + difference 2 1) sourceC563) = raw8324 := by
      apply Matrix.ext; unfold tripleCharges sourceA563 sourceB563 sourceC563 difference raw8324; decide +kernel
    rw [ha]
    exact (canonical8324 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA563 + difference 1 3) (sourceB563 + difference 3 1) sourceC563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA563 + difference 1 3) (sourceB563 + difference 3 1) sourceC563) = raw9507 := by
      apply Matrix.ext; unfold tripleCharges sourceA563 sourceB563 sourceC563 difference raw9507; decide +kernel
    rw [ha]
    exact (canonical9507 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA563 + difference 1 4) (sourceB563 + difference 4 1) sourceC563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2507) := by
    have ha : (tripleCharges (sourceA563 + difference 1 4) (sourceB563 + difference 4 1) sourceC563) = raw5753 := by
      apply Matrix.ext; unfold tripleCharges sourceA563 sourceB563 sourceC563 difference raw5753; decide +kernel
    rw [ha]
    exact (canonical5753 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA563 + difference 1 5) (sourceB563 + difference 5 1) sourceC563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1232) := by
    have ha : (tripleCharges (sourceA563 + difference 1 5) (sourceB563 + difference 5 1) sourceC563) = raw9508 := by
      apply Matrix.ext; unfold tripleCharges sourceA563 sourceB563 sourceC563 difference raw9508; decide +kernel
    rw [ha]
    exact (canonical9508 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA563 + sourceB563) sourceC563) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA563 + sourceB563) sourceC563) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA563 sourceB563 sourceC563 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA563 sourceB563 sourceC563
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm563, Integer.Sparse.eval]
  linarith only [hs]

def sourceA564 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB564 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC564 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm564 : Integer.Sparse Master := [(Sum.inr 4607, 2), (Sum.inr 4609, 1), (Sum.inr 4611, 1), (Sum.inr 4619, 1), (Sum.inr 5144, 2), (Sum.inr 5147, 2), (Sum.inr 5151, 2), (Sum.inr 5163, 2), (Sum.inr 5198, 2), (Sum.inr 5201, 1), (Sum.inr 5206, 1), (Sum.inr 5258, 2), (Sum.inr 5261, 1), (Sum.inr 5274, 1), (Sum.inr 5289, 2), (Sum.inr 5295, 1), (Sum.inr 5304, 1), (Sum.inr 5432, 2), (Sum.inr 5441, 1), (Sum.inr 5449, 1), (Sum.inr 5451, 1)]

theorem sourceEq564 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm564 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA564 + difference 0 1) (sourceB564 + difference 1 0) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5449) := by
    have ha : (tripleCharges (sourceA564 + difference 0 1) (sourceB564 + difference 1 0) sourceC564) = raw9509 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9509; decide +kernel
    rw [ha]
    exact (canonical9509 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA564 + difference 0 2) (sourceB564 + difference 2 0) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA564 + difference 0 2) (sourceB564 + difference 2 0) sourceC564) = raw9510 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9510; decide +kernel
    rw [ha]
    exact (canonical9510 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA564 + difference 0 3) (sourceB564 + difference 3 0) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA564 + difference 0 3) (sourceB564 + difference 3 0) sourceC564) = raw9511 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9511; decide +kernel
    rw [ha]
    exact (canonical9511 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA564 + difference 0 4) (sourceB564 + difference 4 0) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA564 + difference 0 4) (sourceB564 + difference 4 0) sourceC564) = raw4813 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw4813; decide +kernel
    rw [ha]
    exact (canonical4813 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA564 + difference 0 5) (sourceB564 + difference 5 0) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA564 + difference 0 5) (sourceB564 + difference 5 0) sourceC564) = raw9512 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9512; decide +kernel
    rw [ha]
    exact (canonical9512 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA564 + difference 1 0) (sourceB564 + difference 0 1) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA564 + difference 1 0) (sourceB564 + difference 0 1) sourceC564) = raw9513 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9513; decide +kernel
    rw [ha]
    exact (canonical9513 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA564 + difference 1 2) (sourceB564 + difference 2 1) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA564 + difference 1 2) (sourceB564 + difference 2 1) sourceC564) = raw9514 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9514; decide +kernel
    rw [ha]
    exact (canonical9514 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA564 + difference 1 3) (sourceB564 + difference 3 1) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA564 + difference 1 3) (sourceB564 + difference 3 1) sourceC564) = raw9515 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9515; decide +kernel
    rw [ha]
    exact (canonical9515 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA564 + difference 1 4) (sourceB564 + difference 4 1) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA564 + difference 1 4) (sourceB564 + difference 4 1) sourceC564) = raw4818 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw4818; decide +kernel
    rw [ha]
    exact (canonical4818 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA564 + difference 1 5) (sourceB564 + difference 5 1) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA564 + difference 1 5) (sourceB564 + difference 5 1) sourceC564) = raw9516 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9516; decide +kernel
    rw [ha]
    exact (canonical9516 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA564 + difference 2 0) (sourceB564 + difference 0 2) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA564 + difference 2 0) (sourceB564 + difference 0 2) sourceC564) = raw9517 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9517; decide +kernel
    rw [ha]
    exact (canonical9517 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA564 + difference 2 1) (sourceB564 + difference 1 2) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA564 + difference 2 1) (sourceB564 + difference 1 2) sourceC564) = raw9518 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9518; decide +kernel
    rw [ha]
    exact (canonical9518 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA564 + difference 2 3) (sourceB564 + difference 3 2) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA564 + difference 2 3) (sourceB564 + difference 3 2) sourceC564) = raw9519 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9519; decide +kernel
    rw [ha]
    exact (canonical9519 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA564 + difference 2 4) (sourceB564 + difference 4 2) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA564 + difference 2 4) (sourceB564 + difference 4 2) sourceC564) = raw4823 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw4823; decide +kernel
    rw [ha]
    exact (canonical4823 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA564 + difference 2 5) (sourceB564 + difference 5 2) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA564 + difference 2 5) (sourceB564 + difference 5 2) sourceC564) = raw9520 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9520; decide +kernel
    rw [ha]
    exact (canonical9520 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA564 + difference 3 0) (sourceB564 + difference 0 3) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA564 + difference 3 0) (sourceB564 + difference 0 3) sourceC564) = raw9521 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9521; decide +kernel
    rw [ha]
    exact (canonical9521 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA564 + difference 3 1) (sourceB564 + difference 1 3) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA564 + difference 3 1) (sourceB564 + difference 1 3) sourceC564) = raw9522 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9522; decide +kernel
    rw [ha]
    exact (canonical9522 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA564 + difference 3 2) (sourceB564 + difference 2 3) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA564 + difference 3 2) (sourceB564 + difference 2 3) sourceC564) = raw9523 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9523; decide +kernel
    rw [ha]
    exact (canonical9523 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA564 + difference 3 4) (sourceB564 + difference 4 3) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA564 + difference 3 4) (sourceB564 + difference 4 3) sourceC564) = raw4828 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw4828; decide +kernel
    rw [ha]
    exact (canonical4828 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA564 + difference 3 5) (sourceB564 + difference 5 3) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA564 + difference 3 5) (sourceB564 + difference 5 3) sourceC564) = raw9524 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9524; decide +kernel
    rw [ha]
    exact (canonical9524 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA564 + difference 4 0) (sourceB564 + difference 0 4) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA564 + difference 4 0) (sourceB564 + difference 0 4) sourceC564) = raw9525 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9525; decide +kernel
    rw [ha]
    exact (canonical9525 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA564 + difference 4 1) (sourceB564 + difference 1 4) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA564 + difference 4 1) (sourceB564 + difference 1 4) sourceC564) = raw9526 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9526; decide +kernel
    rw [ha]
    exact (canonical9526 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA564 + difference 4 2) (sourceB564 + difference 2 4) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA564 + difference 4 2) (sourceB564 + difference 2 4) sourceC564) = raw9527 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9527; decide +kernel
    rw [ha]
    exact (canonical9527 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA564 + difference 4 3) (sourceB564 + difference 3 4) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA564 + difference 4 3) (sourceB564 + difference 3 4) sourceC564) = raw9528 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9528; decide +kernel
    rw [ha]
    exact (canonical9528 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA564 + difference 4 5) (sourceB564 + difference 5 4) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA564 + difference 4 5) (sourceB564 + difference 5 4) sourceC564) = raw9529 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9529; decide +kernel
    rw [ha]
    exact (canonical9529 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA564 + difference 5 0) (sourceB564 + difference 0 5) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA564 + difference 5 0) (sourceB564 + difference 0 5) sourceC564) = raw4829 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw4829; decide +kernel
    rw [ha]
    exact (canonical4829 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA564 + difference 5 1) (sourceB564 + difference 1 5) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5201) := by
    have ha : (tripleCharges (sourceA564 + difference 5 1) (sourceB564 + difference 1 5) sourceC564) = raw4830 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw4830; decide +kernel
    rw [ha]
    exact (canonical4830 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA564 + difference 5 2) (sourceB564 + difference 2 5) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA564 + difference 5 2) (sourceB564 + difference 2 5) sourceC564) = raw4831 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw4831; decide +kernel
    rw [ha]
    exact (canonical4831 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA564 + difference 5 3) (sourceB564 + difference 3 5) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA564 + difference 5 3) (sourceB564 + difference 3 5) sourceC564) = raw4832 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw4832; decide +kernel
    rw [ha]
    exact (canonical4832 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA564 + difference 5 4) (sourceB564 + difference 4 5) sourceC564) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA564 + difference 5 4) (sourceB564 + difference 4 5) sourceC564) = raw9530 := by
      apply Matrix.ext; unfold tripleCharges sourceA564 sourceB564 sourceC564 difference raw9530; decide +kernel
    rw [ha]
    exact (canonical9530 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA564 sourceB564 sourceC564
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm564, Integer.Sparse.eval]
  linarith only [hs]

def sourceA565 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB565 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC565 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm565 : Integer.Sparse Master := [(Sum.inr 1241, 2), (Sum.inr 1243, 1), (Sum.inr 1245, 1), (Sum.inr 1302, 1), (Sum.inr 2865, 2), (Sum.inr 2885, 2), (Sum.inr 2886, 1), (Sum.inr 2888, 1), (Sum.inr 2928, 2), (Sum.inr 2930, 2), (Sum.inr 2961, 2), (Sum.inr 3089, 2), (Sum.inr 3090, 1), (Sum.inr 3097, 2), (Sum.inr 3098, 1), (Sum.inr 3112, 1), (Sum.inr 3119, 1), (Sum.inr 3987, 1), (Sum.inr 4027, 2), (Sum.inr 4030, 1), (Sum.inr 4037, 1)]

theorem sourceEq565 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm565 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA565 + difference 0 1) (sourceB565 + difference 1 0) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4030) := by
    have ha : (tripleCharges (sourceA565 + difference 0 1) (sourceB565 + difference 1 0) sourceC565) = raw9531 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9531; decide +kernel
    rw [ha]
    exact (canonical9531 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA565 + difference 0 2) (sourceB565 + difference 2 0) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4027) := by
    have ha : (tripleCharges (sourceA565 + difference 0 2) (sourceB565 + difference 2 0) sourceC565) = raw9532 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9532; decide +kernel
    rw [ha]
    exact (canonical9532 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA565 + difference 0 3) (sourceB565 + difference 3 0) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4027) := by
    have ha : (tripleCharges (sourceA565 + difference 0 3) (sourceB565 + difference 3 0) sourceC565) = raw9533 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9533; decide +kernel
    rw [ha]
    exact (canonical9533 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA565 + difference 0 4) (sourceB565 + difference 4 0) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4037) := by
    have ha : (tripleCharges (sourceA565 + difference 0 4) (sourceB565 + difference 4 0) sourceC565) = raw4843 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw4843; decide +kernel
    rw [ha]
    exact (canonical4843 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA565 + difference 0 5) (sourceB565 + difference 5 0) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA565 + difference 0 5) (sourceB565 + difference 5 0) sourceC565) = raw9534 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9534; decide +kernel
    rw [ha]
    exact (canonical9534 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA565 + difference 1 0) (sourceB565 + difference 0 1) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1302) := by
    have ha : (tripleCharges (sourceA565 + difference 1 0) (sourceB565 + difference 0 1) sourceC565) = raw9535 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9535; decide +kernel
    rw [ha]
    exact (canonical9535 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA565 + difference 1 2) (sourceB565 + difference 2 1) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2961) := by
    have ha : (tripleCharges (sourceA565 + difference 1 2) (sourceB565 + difference 2 1) sourceC565) = raw9536 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9536; decide +kernel
    rw [ha]
    exact (canonical9536 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA565 + difference 1 3) (sourceB565 + difference 3 1) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2961) := by
    have ha : (tripleCharges (sourceA565 + difference 1 3) (sourceB565 + difference 3 1) sourceC565) = raw9537 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9537; decide +kernel
    rw [ha]
    exact (canonical9537 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA565 + difference 1 4) (sourceB565 + difference 4 1) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA565 + difference 1 4) (sourceB565 + difference 4 1) sourceC565) = raw4848 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw4848; decide +kernel
    rw [ha]
    exact (canonical4848 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA565 + difference 1 5) (sourceB565 + difference 5 1) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA565 + difference 1 5) (sourceB565 + difference 5 1) sourceC565) = raw9538 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9538; decide +kernel
    rw [ha]
    exact (canonical9538 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA565 + difference 2 0) (sourceB565 + difference 0 2) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA565 + difference 2 0) (sourceB565 + difference 0 2) sourceC565) = raw9539 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9539; decide +kernel
    rw [ha]
    exact (canonical9539 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA565 + difference 2 1) (sourceB565 + difference 1 2) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2885) := by
    have ha : (tripleCharges (sourceA565 + difference 2 1) (sourceB565 + difference 1 2) sourceC565) = raw9540 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9540; decide +kernel
    rw [ha]
    exact (canonical9540 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA565 + difference 2 3) (sourceB565 + difference 3 2) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2928) := by
    have ha : (tripleCharges (sourceA565 + difference 2 3) (sourceB565 + difference 3 2) sourceC565) = raw9541 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9541; decide +kernel
    rw [ha]
    exact (canonical9541 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA565 + difference 2 4) (sourceB565 + difference 4 2) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA565 + difference 2 4) (sourceB565 + difference 4 2) sourceC565) = raw4853 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw4853; decide +kernel
    rw [ha]
    exact (canonical4853 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA565 + difference 2 5) (sourceB565 + difference 5 2) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA565 + difference 2 5) (sourceB565 + difference 5 2) sourceC565) = raw9542 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9542; decide +kernel
    rw [ha]
    exact (canonical9542 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA565 + difference 3 0) (sourceB565 + difference 0 3) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA565 + difference 3 0) (sourceB565 + difference 0 3) sourceC565) = raw9543 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9543; decide +kernel
    rw [ha]
    exact (canonical9543 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA565 + difference 3 1) (sourceB565 + difference 1 3) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2885) := by
    have ha : (tripleCharges (sourceA565 + difference 3 1) (sourceB565 + difference 1 3) sourceC565) = raw9544 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9544; decide +kernel
    rw [ha]
    exact (canonical9544 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA565 + difference 3 2) (sourceB565 + difference 2 3) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2928) := by
    have ha : (tripleCharges (sourceA565 + difference 3 2) (sourceB565 + difference 2 3) sourceC565) = raw9545 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9545; decide +kernel
    rw [ha]
    exact (canonical9545 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA565 + difference 3 4) (sourceB565 + difference 4 3) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA565 + difference 3 4) (sourceB565 + difference 4 3) sourceC565) = raw4858 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw4858; decide +kernel
    rw [ha]
    exact (canonical4858 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA565 + difference 3 5) (sourceB565 + difference 5 3) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA565 + difference 3 5) (sourceB565 + difference 5 3) sourceC565) = raw9546 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9546; decide +kernel
    rw [ha]
    exact (canonical9546 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA565 + difference 4 0) (sourceB565 + difference 0 4) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA565 + difference 4 0) (sourceB565 + difference 0 4) sourceC565) = raw9547 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9547; decide +kernel
    rw [ha]
    exact (canonical9547 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA565 + difference 4 1) (sourceB565 + difference 1 4) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2888) := by
    have ha : (tripleCharges (sourceA565 + difference 4 1) (sourceB565 + difference 1 4) sourceC565) = raw9548 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9548; decide +kernel
    rw [ha]
    exact (canonical9548 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA565 + difference 4 2) (sourceB565 + difference 2 4) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA565 + difference 4 2) (sourceB565 + difference 2 4) sourceC565) = raw9549 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9549; decide +kernel
    rw [ha]
    exact (canonical9549 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA565 + difference 4 3) (sourceB565 + difference 3 4) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA565 + difference 4 3) (sourceB565 + difference 3 4) sourceC565) = raw9550 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9550; decide +kernel
    rw [ha]
    exact (canonical9550 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA565 + difference 4 5) (sourceB565 + difference 5 4) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA565 + difference 4 5) (sourceB565 + difference 5 4) sourceC565) = raw9551 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9551; decide +kernel
    rw [ha]
    exact (canonical9551 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA565 + difference 5 0) (sourceB565 + difference 0 5) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA565 + difference 5 0) (sourceB565 + difference 0 5) sourceC565) = raw4859 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw4859; decide +kernel
    rw [ha]
    exact (canonical4859 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA565 + difference 5 1) (sourceB565 + difference 1 5) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2886) := by
    have ha : (tripleCharges (sourceA565 + difference 5 1) (sourceB565 + difference 1 5) sourceC565) = raw4860 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw4860; decide +kernel
    rw [ha]
    exact (canonical4860 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA565 + difference 5 2) (sourceB565 + difference 2 5) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA565 + difference 5 2) (sourceB565 + difference 2 5) sourceC565) = raw4861 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw4861; decide +kernel
    rw [ha]
    exact (canonical4861 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA565 + difference 5 3) (sourceB565 + difference 3 5) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA565 + difference 5 3) (sourceB565 + difference 3 5) sourceC565) = raw4862 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw4862; decide +kernel
    rw [ha]
    exact (canonical4862 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA565 + difference 5 4) (sourceB565 + difference 4 5) sourceC565) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA565 + difference 5 4) (sourceB565 + difference 4 5) sourceC565) = raw9552 := by
      apply Matrix.ext; unfold tripleCharges sourceA565 sourceB565 sourceC565 difference raw9552; decide +kernel
    rw [ha]
    exact (canonical9552 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA565 sourceB565 sourceC565
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm565, Integer.Sparse.eval]
  linarith only [hs]

def sourceA566 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB566 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC566 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm566 : Integer.Sparse Master := [(Sum.inr 2681, 2), (Sum.inr 2683, 1), (Sum.inr 2687, 1), (Sum.inr 2781, 1), (Sum.inr 3296, 2), (Sum.inr 3302, 1), (Sum.inr 3305, 1), (Sum.inr 3530, 2), (Sum.inr 3533, 2), (Sum.inr 3545, 1), (Sum.inr 3547, 1), (Sum.inr 3557, 2), (Sum.inr 3564, 2), (Sum.inr 3570, 2), (Sum.inr 3572, 2), (Sum.inr 3579, 1), (Sum.inr 3583, 1), (Sum.inr 3850, 2), (Sum.inr 3860, 1), (Sum.inr 3886, 1), (Sum.inr 3888, 1)]

theorem sourceEq566 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm566 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA566 + difference 0 1) (sourceB566 + difference 1 0) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA566 + difference 0 1) (sourceB566 + difference 1 0) sourceC566) = raw9553 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9553; decide +kernel
    rw [ha]
    exact (canonical9553 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA566 + difference 0 2) (sourceB566 + difference 2 0) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA566 + difference 0 2) (sourceB566 + difference 2 0) sourceC566) = raw9554 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9554; decide +kernel
    rw [ha]
    exact (canonical9554 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA566 + difference 0 3) (sourceB566 + difference 3 0) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA566 + difference 0 3) (sourceB566 + difference 3 0) sourceC566) = raw9555 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9555; decide +kernel
    rw [ha]
    exact (canonical9555 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA566 + difference 0 4) (sourceB566 + difference 4 0) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3860) := by
    have ha : (tripleCharges (sourceA566 + difference 0 4) (sourceB566 + difference 4 0) sourceC566) = raw4873 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4873; decide +kernel
    rw [ha]
    exact (canonical4873 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA566 + difference 0 5) (sourceB566 + difference 5 0) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA566 + difference 0 5) (sourceB566 + difference 5 0) sourceC566) = raw9556 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9556; decide +kernel
    rw [ha]
    exact (canonical9556 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA566 + difference 1 0) (sourceB566 + difference 0 1) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA566 + difference 1 0) (sourceB566 + difference 0 1) sourceC566) = raw9557 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9557; decide +kernel
    rw [ha]
    exact (canonical9557 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA566 + difference 1 2) (sourceB566 + difference 2 1) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA566 + difference 1 2) (sourceB566 + difference 2 1) sourceC566) = raw9558 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9558; decide +kernel
    rw [ha]
    exact (canonical9558 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA566 + difference 1 3) (sourceB566 + difference 3 1) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA566 + difference 1 3) (sourceB566 + difference 3 1) sourceC566) = raw9559 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9559; decide +kernel
    rw [ha]
    exact (canonical9559 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA566 + difference 1 4) (sourceB566 + difference 4 1) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA566 + difference 1 4) (sourceB566 + difference 4 1) sourceC566) = raw4878 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4878; decide +kernel
    rw [ha]
    exact (canonical4878 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA566 + difference 1 5) (sourceB566 + difference 5 1) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA566 + difference 1 5) (sourceB566 + difference 5 1) sourceC566) = raw9560 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9560; decide +kernel
    rw [ha]
    exact (canonical9560 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA566 + difference 2 0) (sourceB566 + difference 0 2) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA566 + difference 2 0) (sourceB566 + difference 0 2) sourceC566) = raw9561 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9561; decide +kernel
    rw [ha]
    exact (canonical9561 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA566 + difference 2 1) (sourceB566 + difference 1 2) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA566 + difference 2 1) (sourceB566 + difference 1 2) sourceC566) = raw9562 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9562; decide +kernel
    rw [ha]
    exact (canonical9562 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA566 + difference 2 3) (sourceB566 + difference 3 2) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA566 + difference 2 3) (sourceB566 + difference 3 2) sourceC566) = raw9563 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9563; decide +kernel
    rw [ha]
    exact (canonical9563 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA566 + difference 2 4) (sourceB566 + difference 4 2) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA566 + difference 2 4) (sourceB566 + difference 4 2) sourceC566) = raw4883 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4883; decide +kernel
    rw [ha]
    exact (canonical4883 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA566 + difference 2 5) (sourceB566 + difference 5 2) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA566 + difference 2 5) (sourceB566 + difference 5 2) sourceC566) = raw9564 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9564; decide +kernel
    rw [ha]
    exact (canonical9564 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA566 + difference 3 0) (sourceB566 + difference 0 3) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA566 + difference 3 0) (sourceB566 + difference 0 3) sourceC566) = raw9565 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9565; decide +kernel
    rw [ha]
    exact (canonical9565 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA566 + difference 3 1) (sourceB566 + difference 1 3) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA566 + difference 3 1) (sourceB566 + difference 1 3) sourceC566) = raw9566 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9566; decide +kernel
    rw [ha]
    exact (canonical9566 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA566 + difference 3 2) (sourceB566 + difference 2 3) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA566 + difference 3 2) (sourceB566 + difference 2 3) sourceC566) = raw9567 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9567; decide +kernel
    rw [ha]
    exact (canonical9567 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA566 + difference 3 4) (sourceB566 + difference 4 3) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA566 + difference 3 4) (sourceB566 + difference 4 3) sourceC566) = raw4888 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4888; decide +kernel
    rw [ha]
    exact (canonical4888 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA566 + difference 3 5) (sourceB566 + difference 5 3) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA566 + difference 3 5) (sourceB566 + difference 5 3) sourceC566) = raw9568 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9568; decide +kernel
    rw [ha]
    exact (canonical9568 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA566 + difference 4 0) (sourceB566 + difference 0 4) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA566 + difference 4 0) (sourceB566 + difference 0 4) sourceC566) = raw9569 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9569; decide +kernel
    rw [ha]
    exact (canonical9569 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA566 + difference 4 1) (sourceB566 + difference 1 4) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA566 + difference 4 1) (sourceB566 + difference 1 4) sourceC566) = raw9570 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9570; decide +kernel
    rw [ha]
    exact (canonical9570 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA566 + difference 4 2) (sourceB566 + difference 2 4) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA566 + difference 4 2) (sourceB566 + difference 2 4) sourceC566) = raw9571 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9571; decide +kernel
    rw [ha]
    exact (canonical9571 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA566 + difference 4 3) (sourceB566 + difference 3 4) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA566 + difference 4 3) (sourceB566 + difference 3 4) sourceC566) = raw9572 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9572; decide +kernel
    rw [ha]
    exact (canonical9572 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA566 + difference 4 5) (sourceB566 + difference 5 4) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA566 + difference 4 5) (sourceB566 + difference 5 4) sourceC566) = raw9573 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9573; decide +kernel
    rw [ha]
    exact (canonical9573 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA566 + difference 5 0) (sourceB566 + difference 0 5) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA566 + difference 5 0) (sourceB566 + difference 0 5) sourceC566) = raw4889 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4889; decide +kernel
    rw [ha]
    exact (canonical4889 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA566 + difference 5 1) (sourceB566 + difference 1 5) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3579) := by
    have ha : (tripleCharges (sourceA566 + difference 5 1) (sourceB566 + difference 1 5) sourceC566) = raw4890 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4890; decide +kernel
    rw [ha]
    exact (canonical4890 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA566 + difference 5 2) (sourceB566 + difference 2 5) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA566 + difference 5 2) (sourceB566 + difference 2 5) sourceC566) = raw4891 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4891; decide +kernel
    rw [ha]
    exact (canonical4891 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA566 + difference 5 3) (sourceB566 + difference 3 5) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA566 + difference 5 3) (sourceB566 + difference 3 5) sourceC566) = raw4892 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4892; decide +kernel
    rw [ha]
    exact (canonical4892 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA566 + difference 5 4) (sourceB566 + difference 4 5) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA566 + difference 5 4) (sourceB566 + difference 4 5) sourceC566) = raw9574 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9574; decide +kernel
    rw [ha]
    exact (canonical9574 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA566 sourceB566 sourceC566
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm566, Integer.Sparse.eval]
  linarith only [hs]

def sourceA567 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB567 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC567 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm567 : Integer.Sparse Master := [(Sum.inr 2765, 1), (Sum.inr 3850, 2), (Sum.inr 3886, 1), (Sum.inr 3905, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

theorem sourceEq567 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm567 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA567 + difference 0 0) (sourceB567 + difference 0 0) sourceC567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA567 + difference 0 0) (sourceB567 + difference 0 0) sourceC567) = raw9575 := by
      apply Matrix.ext; unfold tripleCharges sourceA567 sourceB567 sourceC567 difference raw9575; decide +kernel
    rw [ha]
    exact (canonical9575 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA567 + difference 0 1) (sourceB567 + difference 1 0) sourceC567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA567 + difference 0 1) (sourceB567 + difference 1 0) sourceC567) = raw9576 := by
      apply Matrix.ext; unfold tripleCharges sourceA567 sourceB567 sourceC567 difference raw9576; decide +kernel
    rw [ha]
    exact (canonical9576 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA567 + difference 0 2) (sourceB567 + difference 2 0) sourceC567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA567 + difference 0 2) (sourceB567 + difference 2 0) sourceC567) = raw9577 := by
      apply Matrix.ext; unfold tripleCharges sourceA567 sourceB567 sourceC567 difference raw9577; decide +kernel
    rw [ha]
    exact (canonical9577 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA567 + difference 0 3) (sourceB567 + difference 3 0) sourceC567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA567 + difference 0 3) (sourceB567 + difference 3 0) sourceC567) = raw9578 := by
      apply Matrix.ext; unfold tripleCharges sourceA567 sourceB567 sourceC567 difference raw9578; decide +kernel
    rw [ha]
    exact (canonical9578 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA567 + difference 0 4) (sourceB567 + difference 4 0) sourceC567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3905) := by
    have ha : (tripleCharges (sourceA567 + difference 0 4) (sourceB567 + difference 4 0) sourceC567) = raw4904 := by
      apply Matrix.ext; unfold tripleCharges sourceA567 sourceB567 sourceC567 difference raw4904; decide +kernel
    rw [ha]
    exact (canonical4904 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA567 + difference 0 5) (sourceB567 + difference 5 0) sourceC567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA567 + difference 0 5) (sourceB567 + difference 5 0) sourceC567) = raw9579 := by
      apply Matrix.ext; unfold tripleCharges sourceA567 sourceB567 sourceC567 difference raw9579; decide +kernel
    rw [ha]
    exact (canonical9579 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA567 + sourceB567) sourceC567) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA567 + sourceB567) sourceC567) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA567 sourceB567 sourceC567 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA567 sourceB567 sourceC567
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm567, Integer.Sparse.eval]
  linarith only [hs]

def sourceA568 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB568 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC568 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm568 : Integer.Sparse Master := [(Sum.inr 1261, 2), (Sum.inr 1264, 1), (Sum.inr 1273, 1), (Sum.inr 1294, 1), (Sum.inr 2765, 1), (Sum.inr 4092, -1)]

theorem sourceEq568 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm568 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA568 + difference 0 0) (sourceB568 + difference 0 0) sourceC568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA568 + difference 0 0) (sourceB568 + difference 0 0) sourceC568) = raw9575 := by
      apply Matrix.ext; unfold tripleCharges sourceA568 sourceB568 sourceC568 difference raw9575; decide +kernel
    rw [ha]
    exact (canonical9575 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA568 + difference 1 0) (sourceB568 + difference 0 1) sourceC568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA568 + difference 1 0) (sourceB568 + difference 0 1) sourceC568) = raw9580 := by
      apply Matrix.ext; unfold tripleCharges sourceA568 sourceB568 sourceC568 difference raw9580; decide +kernel
    rw [ha]
    exact (canonical9580 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA568 + difference 2 0) (sourceB568 + difference 0 2) sourceC568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA568 + difference 2 0) (sourceB568 + difference 0 2) sourceC568) = raw9581 := by
      apply Matrix.ext; unfold tripleCharges sourceA568 sourceB568 sourceC568 difference raw9581; decide +kernel
    rw [ha]
    exact (canonical9581 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA568 + difference 3 0) (sourceB568 + difference 0 3) sourceC568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA568 + difference 3 0) (sourceB568 + difference 0 3) sourceC568) = raw9582 := by
      apply Matrix.ext; unfold tripleCharges sourceA568 sourceB568 sourceC568 difference raw9582; decide +kernel
    rw [ha]
    exact (canonical9582 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA568 + difference 4 0) (sourceB568 + difference 0 4) sourceC568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA568 + difference 4 0) (sourceB568 + difference 0 4) sourceC568) = raw9583 := by
      apply Matrix.ext; unfold tripleCharges sourceA568 sourceB568 sourceC568 difference raw9583; decide +kernel
    rw [ha]
    exact (canonical9583 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA568 + difference 5 0) (sourceB568 + difference 0 5) sourceC568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1264) := by
    have ha : (tripleCharges (sourceA568 + difference 5 0) (sourceB568 + difference 0 5) sourceC568) = raw4909 := by
      apply Matrix.ext; unfold tripleCharges sourceA568 sourceB568 sourceC568 difference raw4909; decide +kernel
    rw [ha]
    exact (canonical4909 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA568 + sourceB568) sourceC568) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA568 + sourceB568) sourceC568) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA568 sourceB568 sourceC568 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA568 sourceB568 sourceC568
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm568, Integer.Sparse.eval]
  linarith only [hs]

def sourceA569 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB569 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC569 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm569 : Integer.Sparse Master := [(Sum.inr 1294, 1), (Sum.inr 2590, 2), (Sum.inr 2742, 1), (Sum.inr 2765, 1), (Sum.inr 2782, 1), (Sum.inr 4092, -1)]

theorem sourceEq569 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm569 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA569 + difference 1 0) (sourceB569 + difference 0 1) sourceC569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA569 + difference 1 0) (sourceB569 + difference 0 1) sourceC569) = raw9580 := by
      apply Matrix.ext; unfold tripleCharges sourceA569 sourceB569 sourceC569 difference raw9580; decide +kernel
    rw [ha]
    exact (canonical9580 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA569 + difference 1 1) (sourceB569 + difference 1 1) sourceC569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA569 + difference 1 1) (sourceB569 + difference 1 1) sourceC569) = raw9575 := by
      apply Matrix.ext; unfold tripleCharges sourceA569 sourceB569 sourceC569 difference raw9575; decide +kernel
    rw [ha]
    exact (canonical9575 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA569 + difference 1 2) (sourceB569 + difference 2 1) sourceC569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA569 + difference 1 2) (sourceB569 + difference 2 1) sourceC569) = raw9584 := by
      apply Matrix.ext; unfold tripleCharges sourceA569 sourceB569 sourceC569 difference raw9584; decide +kernel
    rw [ha]
    exact (canonical9584 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA569 + difference 1 3) (sourceB569 + difference 3 1) sourceC569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA569 + difference 1 3) (sourceB569 + difference 3 1) sourceC569) = raw9585 := by
      apply Matrix.ext; unfold tripleCharges sourceA569 sourceB569 sourceC569 difference raw9585; decide +kernel
    rw [ha]
    exact (canonical9585 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA569 + difference 1 4) (sourceB569 + difference 4 1) sourceC569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA569 + difference 1 4) (sourceB569 + difference 4 1) sourceC569) = raw4914 := by
      apply Matrix.ext; unfold tripleCharges sourceA569 sourceB569 sourceC569 difference raw4914; decide +kernel
    rw [ha]
    exact (canonical4914 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA569 + difference 1 5) (sourceB569 + difference 5 1) sourceC569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA569 + difference 1 5) (sourceB569 + difference 5 1) sourceC569) = raw9586 := by
      apply Matrix.ext; unfold tripleCharges sourceA569 sourceB569 sourceC569 difference raw9586; decide +kernel
    rw [ha]
    exact (canonical9586 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA569 + sourceB569) sourceC569) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA569 + sourceB569) sourceC569) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA569 sourceB569 sourceC569 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA569 sourceB569 sourceC569
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm569, Integer.Sparse.eval]
  linarith only [hs]

def sourceA570 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB570 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC570 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm570 : Integer.Sparse Master := [(Sum.inr 2632, 2), (Sum.inr 2635, 1), (Sum.inr 2643, 1), (Sum.inr 2765, 1), (Sum.inr 3886, 1), (Sum.inr 4092, -1)]

theorem sourceEq570 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm570 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA570 + difference 0 1) (sourceB570 + difference 1 0) sourceC570) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA570 + difference 0 1) (sourceB570 + difference 1 0) sourceC570) = raw9576 := by
      apply Matrix.ext; unfold tripleCharges sourceA570 sourceB570 sourceC570 difference raw9576; decide +kernel
    rw [ha]
    exact (canonical9576 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA570 + difference 1 1) (sourceB570 + difference 1 1) sourceC570) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA570 + difference 1 1) (sourceB570 + difference 1 1) sourceC570) = raw9575 := by
      apply Matrix.ext; unfold tripleCharges sourceA570 sourceB570 sourceC570 difference raw9575; decide +kernel
    rw [ha]
    exact (canonical9575 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA570 + difference 2 1) (sourceB570 + difference 1 2) sourceC570) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2632) := by
    have ha : (tripleCharges (sourceA570 + difference 2 1) (sourceB570 + difference 1 2) sourceC570) = raw9587 := by
      apply Matrix.ext; unfold tripleCharges sourceA570 sourceB570 sourceC570 difference raw9587; decide +kernel
    rw [ha]
    exact (canonical9587 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA570 + difference 3 1) (sourceB570 + difference 1 3) sourceC570) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2632) := by
    have ha : (tripleCharges (sourceA570 + difference 3 1) (sourceB570 + difference 1 3) sourceC570) = raw9588 := by
      apply Matrix.ext; unfold tripleCharges sourceA570 sourceB570 sourceC570 difference raw9588; decide +kernel
    rw [ha]
    exact (canonical9588 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA570 + difference 4 1) (sourceB570 + difference 1 4) sourceC570) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2643) := by
    have ha : (tripleCharges (sourceA570 + difference 4 1) (sourceB570 + difference 1 4) sourceC570) = raw9589 := by
      apply Matrix.ext; unfold tripleCharges sourceA570 sourceB570 sourceC570 difference raw9589; decide +kernel
    rw [ha]
    exact (canonical9589 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA570 + difference 5 1) (sourceB570 + difference 1 5) sourceC570) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2635) := by
    have ha : (tripleCharges (sourceA570 + difference 5 1) (sourceB570 + difference 1 5) sourceC570) = raw4917 := by
      apply Matrix.ext; unfold tripleCharges sourceA570 sourceB570 sourceC570 difference raw4917; decide +kernel
    rw [ha]
    exact (canonical4917 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA570 + sourceB570) sourceC570) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA570 + sourceB570) sourceC570) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA570 sourceB570 sourceC570 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA570 sourceB570 sourceC570
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm570, Integer.Sparse.eval]
  linarith only [hs]

def sourceA571 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB571 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC571 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm571 : Integer.Sparse Master := [(Sum.inr 1261, 1), (Sum.inr 2566, 1), (Sum.inr 2632, 1), (Sum.inr 2722, 1), (Sum.inr 2763, 1), (Sum.inr 2765, 1), (Sum.inr 4092, -1)]

theorem sourceEq571 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm571 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA571 + difference 2 0) (sourceB571 + difference 0 2) sourceC571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA571 + difference 2 0) (sourceB571 + difference 0 2) sourceC571) = raw9581 := by
      apply Matrix.ext; unfold tripleCharges sourceA571 sourceB571 sourceC571 difference raw9581; decide +kernel
    rw [ha]
    exact (canonical9581 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA571 + difference 2 1) (sourceB571 + difference 1 2) sourceC571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2632) := by
    have ha : (tripleCharges (sourceA571 + difference 2 1) (sourceB571 + difference 1 2) sourceC571) = raw9587 := by
      apply Matrix.ext; unfold tripleCharges sourceA571 sourceB571 sourceC571 difference raw9587; decide +kernel
    rw [ha]
    exact (canonical9587 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA571 + difference 2 2) (sourceB571 + difference 2 2) sourceC571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA571 + difference 2 2) (sourceB571 + difference 2 2) sourceC571) = raw9575 := by
      apply Matrix.ext; unfold tripleCharges sourceA571 sourceB571 sourceC571 difference raw9575; decide +kernel
    rw [ha]
    exact (canonical9575 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA571 + difference 2 3) (sourceB571 + difference 3 2) sourceC571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2566) := by
    have ha : (tripleCharges (sourceA571 + difference 2 3) (sourceB571 + difference 3 2) sourceC571) = raw9590 := by
      apply Matrix.ext; unfold tripleCharges sourceA571 sourceB571 sourceC571 difference raw9590; decide +kernel
    rw [ha]
    exact (canonical9590 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA571 + difference 2 4) (sourceB571 + difference 4 2) sourceC571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA571 + difference 2 4) (sourceB571 + difference 4 2) sourceC571) = raw4921 := by
      apply Matrix.ext; unfold tripleCharges sourceA571 sourceB571 sourceC571 difference raw4921; decide +kernel
    rw [ha]
    exact (canonical4921 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA571 + difference 2 5) (sourceB571 + difference 5 2) sourceC571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA571 + difference 2 5) (sourceB571 + difference 5 2) sourceC571) = raw9591 := by
      apply Matrix.ext; unfold tripleCharges sourceA571 sourceB571 sourceC571 difference raw9591; decide +kernel
    rw [ha]
    exact (canonical9591 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA571 + sourceB571) sourceC571) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA571 + sourceB571) sourceC571) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA571 sourceB571 sourceC571 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA571 sourceB571 sourceC571
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm571, Integer.Sparse.eval]
  linarith only [hs]

def sourceA572 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB572 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC572 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceForm572 : Integer.Sparse Master := [(Sum.inr 4452, 2), (Sum.inr 4454, 1), (Sum.inr 4466, 1), (Sum.inr 4491, 1), (Sum.inr 4827, 2), (Sum.inr 4845, 1), (Sum.inr 4868, 1), (Sum.inr 5070, 2), (Sum.inr 5080, 2), (Sum.inr 5095, 2), (Sum.inr 5163, 2), (Sum.inr 5176, 1), (Sum.inr 5228, 2), (Sum.inr 5238, 1), (Sum.inr 5290, 2), (Sum.inr 5294, 1), (Sum.inr 5304, 1), (Sum.inr 5438, 2), (Sum.inr 5443, 1), (Sum.inr 5451, 1), (Sum.inr 5492, 1)]

theorem sourceEq572 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm572 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA572 + difference 0 1) (sourceB572 + difference 1 0) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA572 + difference 0 1) (sourceB572 + difference 1 0) sourceC572) = raw9592 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9592; decide +kernel
    rw [ha]
    exact (canonical9592 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA572 + difference 0 2) (sourceB572 + difference 2 0) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA572 + difference 0 2) (sourceB572 + difference 2 0) sourceC572) = raw9593 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9593; decide +kernel
    rw [ha]
    exact (canonical9593 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA572 + difference 0 3) (sourceB572 + difference 3 0) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA572 + difference 0 3) (sourceB572 + difference 3 0) sourceC572) = raw9594 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9594; decide +kernel
    rw [ha]
    exact (canonical9594 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA572 + difference 0 4) (sourceB572 + difference 4 0) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA572 + difference 0 4) (sourceB572 + difference 4 0) sourceC572) = raw9595 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9595; decide +kernel
    rw [ha]
    exact (canonical9595 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA572 + difference 0 5) (sourceB572 + difference 5 0) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA572 + difference 0 5) (sourceB572 + difference 5 0) sourceC572) = raw9596 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9596; decide +kernel
    rw [ha]
    exact (canonical9596 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA572 + difference 1 0) (sourceB572 + difference 0 1) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA572 + difference 1 0) (sourceB572 + difference 0 1) sourceC572) = raw9597 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9597; decide +kernel
    rw [ha]
    exact (canonical9597 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA572 + difference 1 2) (sourceB572 + difference 2 1) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA572 + difference 1 2) (sourceB572 + difference 2 1) sourceC572) = raw9598 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9598; decide +kernel
    rw [ha]
    exact (canonical9598 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA572 + difference 1 3) (sourceB572 + difference 3 1) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA572 + difference 1 3) (sourceB572 + difference 3 1) sourceC572) = raw9599 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9599; decide +kernel
    rw [ha]
    exact (canonical9599 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA572 + difference 1 4) (sourceB572 + difference 4 1) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA572 + difference 1 4) (sourceB572 + difference 4 1) sourceC572) = raw9600 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9600; decide +kernel
    rw [ha]
    exact (canonical9600 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA572 + difference 1 5) (sourceB572 + difference 5 1) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA572 + difference 1 5) (sourceB572 + difference 5 1) sourceC572) = raw9601 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9601; decide +kernel
    rw [ha]
    exact (canonical9601 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA572 + difference 2 0) (sourceB572 + difference 0 2) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA572 + difference 2 0) (sourceB572 + difference 0 2) sourceC572) = raw9602 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9602; decide +kernel
    rw [ha]
    exact (canonical9602 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA572 + difference 2 1) (sourceB572 + difference 1 2) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA572 + difference 2 1) (sourceB572 + difference 1 2) sourceC572) = raw9603 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9603; decide +kernel
    rw [ha]
    exact (canonical9603 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA572 + difference 2 3) (sourceB572 + difference 3 2) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA572 + difference 2 3) (sourceB572 + difference 3 2) sourceC572) = raw9604 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9604; decide +kernel
    rw [ha]
    exact (canonical9604 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA572 + difference 2 4) (sourceB572 + difference 4 2) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA572 + difference 2 4) (sourceB572 + difference 4 2) sourceC572) = raw9605 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9605; decide +kernel
    rw [ha]
    exact (canonical9605 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA572 + difference 2 5) (sourceB572 + difference 5 2) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA572 + difference 2 5) (sourceB572 + difference 5 2) sourceC572) = raw9606 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9606; decide +kernel
    rw [ha]
    exact (canonical9606 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA572 + difference 3 0) (sourceB572 + difference 0 3) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA572 + difference 3 0) (sourceB572 + difference 0 3) sourceC572) = raw9607 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9607; decide +kernel
    rw [ha]
    exact (canonical9607 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA572 + difference 3 1) (sourceB572 + difference 1 3) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA572 + difference 3 1) (sourceB572 + difference 1 3) sourceC572) = raw9608 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9608; decide +kernel
    rw [ha]
    exact (canonical9608 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA572 + difference 3 2) (sourceB572 + difference 2 3) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA572 + difference 3 2) (sourceB572 + difference 2 3) sourceC572) = raw9609 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9609; decide +kernel
    rw [ha]
    exact (canonical9609 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA572 + difference 3 4) (sourceB572 + difference 4 3) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA572 + difference 3 4) (sourceB572 + difference 4 3) sourceC572) = raw9610 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9610; decide +kernel
    rw [ha]
    exact (canonical9610 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA572 + difference 3 5) (sourceB572 + difference 5 3) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA572 + difference 3 5) (sourceB572 + difference 5 3) sourceC572) = raw9611 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9611; decide +kernel
    rw [ha]
    exact (canonical9611 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA572 + difference 4 0) (sourceB572 + difference 0 4) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA572 + difference 4 0) (sourceB572 + difference 0 4) sourceC572) = raw9612 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9612; decide +kernel
    rw [ha]
    exact (canonical9612 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA572 + difference 4 1) (sourceB572 + difference 1 4) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA572 + difference 4 1) (sourceB572 + difference 1 4) sourceC572) = raw9613 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9613; decide +kernel
    rw [ha]
    exact (canonical9613 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA572 + difference 4 2) (sourceB572 + difference 2 4) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA572 + difference 4 2) (sourceB572 + difference 2 4) sourceC572) = raw9614 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9614; decide +kernel
    rw [ha]
    exact (canonical9614 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA572 + difference 4 3) (sourceB572 + difference 3 4) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA572 + difference 4 3) (sourceB572 + difference 3 4) sourceC572) = raw9615 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9615; decide +kernel
    rw [ha]
    exact (canonical9615 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA572 + difference 4 5) (sourceB572 + difference 5 4) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA572 + difference 4 5) (sourceB572 + difference 5 4) sourceC572) = raw9616 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9616; decide +kernel
    rw [ha]
    exact (canonical9616 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA572 + difference 5 0) (sourceB572 + difference 0 5) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4454) := by
    have ha : (tripleCharges (sourceA572 + difference 5 0) (sourceB572 + difference 0 5) sourceC572) = raw9617 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9617; decide +kernel
    rw [ha]
    exact (canonical9617 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA572 + difference 5 1) (sourceB572 + difference 1 5) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA572 + difference 5 1) (sourceB572 + difference 1 5) sourceC572) = raw9618 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9618; decide +kernel
    rw [ha]
    exact (canonical9618 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA572 + difference 5 2) (sourceB572 + difference 2 5) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA572 + difference 5 2) (sourceB572 + difference 2 5) sourceC572) = raw9619 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9619; decide +kernel
    rw [ha]
    exact (canonical9619 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA572 + difference 5 3) (sourceB572 + difference 3 5) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA572 + difference 5 3) (sourceB572 + difference 3 5) sourceC572) = raw9620 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9620; decide +kernel
    rw [ha]
    exact (canonical9620 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA572 + difference 5 4) (sourceB572 + difference 4 5) sourceC572) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA572 + difference 5 4) (sourceB572 + difference 4 5) sourceC572) = raw9621 := by
      apply Matrix.ext; unfold tripleCharges sourceA572 sourceB572 sourceC572 difference raw9621; decide +kernel
    rw [ha]
    exact (canonical9621 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA572 sourceB572 sourceC572
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm572, Integer.Sparse.eval]
  linarith only [hs]

def sourceA573 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB573 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC573 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceForm573 : Integer.Sparse Master := [(Sum.inr 1035, 2), (Sum.inr 1037, 1), (Sum.inr 1049, 1), (Sum.inr 1075, 1), (Sum.inr 2079, 2), (Sum.inr 2109, 1), (Sum.inr 2218, 1), (Sum.inr 2477, 2), (Sum.inr 2488, 2), (Sum.inr 2505, 2), (Sum.inr 2590, 2), (Sum.inr 2604, 1), (Sum.inr 2672, 2), (Sum.inr 2686, 1), (Sum.inr 2764, 2), (Sum.inr 2768, 1), (Sum.inr 2782, 1), (Sum.inr 3876, 2), (Sum.inr 3888, 1), (Sum.inr 3907, 1), (Sum.inr 4017, 1)]

theorem sourceEq573 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm573 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA573 + difference 0 1) (sourceB573 + difference 1 0) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA573 + difference 0 1) (sourceB573 + difference 1 0) sourceC573) = raw9622 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9622; decide +kernel
    rw [ha]
    exact (canonical9622 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA573 + difference 0 2) (sourceB573 + difference 2 0) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA573 + difference 0 2) (sourceB573 + difference 2 0) sourceC573) = raw9623 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9623; decide +kernel
    rw [ha]
    exact (canonical9623 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA573 + difference 0 3) (sourceB573 + difference 3 0) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA573 + difference 0 3) (sourceB573 + difference 3 0) sourceC573) = raw9624 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9624; decide +kernel
    rw [ha]
    exact (canonical9624 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA573 + difference 0 4) (sourceB573 + difference 4 0) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA573 + difference 0 4) (sourceB573 + difference 4 0) sourceC573) = raw9625 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9625; decide +kernel
    rw [ha]
    exact (canonical9625 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA573 + difference 0 5) (sourceB573 + difference 5 0) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4017) := by
    have ha : (tripleCharges (sourceA573 + difference 0 5) (sourceB573 + difference 5 0) sourceC573) = raw9626 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9626; decide +kernel
    rw [ha]
    exact (canonical9626 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA573 + difference 1 0) (sourceB573 + difference 0 1) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1075) := by
    have ha : (tripleCharges (sourceA573 + difference 1 0) (sourceB573 + difference 0 1) sourceC573) = raw9627 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9627; decide +kernel
    rw [ha]
    exact (canonical9627 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA573 + difference 1 2) (sourceB573 + difference 2 1) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2505) := by
    have ha : (tripleCharges (sourceA573 + difference 1 2) (sourceB573 + difference 2 1) sourceC573) = raw9628 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9628; decide +kernel
    rw [ha]
    exact (canonical9628 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA573 + difference 1 3) (sourceB573 + difference 3 1) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2505) := by
    have ha : (tripleCharges (sourceA573 + difference 1 3) (sourceB573 + difference 3 1) sourceC573) = raw9629 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9629; decide +kernel
    rw [ha]
    exact (canonical9629 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA573 + difference 1 4) (sourceB573 + difference 4 1) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA573 + difference 1 4) (sourceB573 + difference 4 1) sourceC573) = raw9630 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9630; decide +kernel
    rw [ha]
    exact (canonical9630 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA573 + difference 1 5) (sourceB573 + difference 5 1) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA573 + difference 1 5) (sourceB573 + difference 5 1) sourceC573) = raw9631 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9631; decide +kernel
    rw [ha]
    exact (canonical9631 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA573 + difference 2 0) (sourceB573 + difference 0 2) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA573 + difference 2 0) (sourceB573 + difference 0 2) sourceC573) = raw9632 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9632; decide +kernel
    rw [ha]
    exact (canonical9632 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA573 + difference 2 1) (sourceB573 + difference 1 2) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA573 + difference 2 1) (sourceB573 + difference 1 2) sourceC573) = raw9633 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9633; decide +kernel
    rw [ha]
    exact (canonical9633 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA573 + difference 2 3) (sourceB573 + difference 3 2) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA573 + difference 2 3) (sourceB573 + difference 3 2) sourceC573) = raw9634 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9634; decide +kernel
    rw [ha]
    exact (canonical9634 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA573 + difference 2 4) (sourceB573 + difference 4 2) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA573 + difference 2 4) (sourceB573 + difference 4 2) sourceC573) = raw9635 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9635; decide +kernel
    rw [ha]
    exact (canonical9635 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA573 + difference 2 5) (sourceB573 + difference 5 2) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA573 + difference 2 5) (sourceB573 + difference 5 2) sourceC573) = raw9636 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9636; decide +kernel
    rw [ha]
    exact (canonical9636 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA573 + difference 3 0) (sourceB573 + difference 0 3) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA573 + difference 3 0) (sourceB573 + difference 0 3) sourceC573) = raw9637 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9637; decide +kernel
    rw [ha]
    exact (canonical9637 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA573 + difference 3 1) (sourceB573 + difference 1 3) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA573 + difference 3 1) (sourceB573 + difference 1 3) sourceC573) = raw9638 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9638; decide +kernel
    rw [ha]
    exact (canonical9638 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA573 + difference 3 2) (sourceB573 + difference 2 3) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA573 + difference 3 2) (sourceB573 + difference 2 3) sourceC573) = raw9639 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9639; decide +kernel
    rw [ha]
    exact (canonical9639 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA573 + difference 3 4) (sourceB573 + difference 4 3) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA573 + difference 3 4) (sourceB573 + difference 4 3) sourceC573) = raw9640 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9640; decide +kernel
    rw [ha]
    exact (canonical9640 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA573 + difference 3 5) (sourceB573 + difference 5 3) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA573 + difference 3 5) (sourceB573 + difference 5 3) sourceC573) = raw9641 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9641; decide +kernel
    rw [ha]
    exact (canonical9641 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA573 + difference 4 0) (sourceB573 + difference 0 4) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA573 + difference 4 0) (sourceB573 + difference 0 4) sourceC573) = raw9642 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9642; decide +kernel
    rw [ha]
    exact (canonical9642 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA573 + difference 4 1) (sourceB573 + difference 1 4) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2604) := by
    have ha : (tripleCharges (sourceA573 + difference 4 1) (sourceB573 + difference 1 4) sourceC573) = raw9643 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9643; decide +kernel
    rw [ha]
    exact (canonical9643 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA573 + difference 4 2) (sourceB573 + difference 2 4) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA573 + difference 4 2) (sourceB573 + difference 2 4) sourceC573) = raw9644 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9644; decide +kernel
    rw [ha]
    exact (canonical9644 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA573 + difference 4 3) (sourceB573 + difference 3 4) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA573 + difference 4 3) (sourceB573 + difference 3 4) sourceC573) = raw9645 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9645; decide +kernel
    rw [ha]
    exact (canonical9645 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA573 + difference 4 5) (sourceB573 + difference 5 4) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA573 + difference 4 5) (sourceB573 + difference 5 4) sourceC573) = raw9646 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9646; decide +kernel
    rw [ha]
    exact (canonical9646 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA573 + difference 5 0) (sourceB573 + difference 0 5) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1037) := by
    have ha : (tripleCharges (sourceA573 + difference 5 0) (sourceB573 + difference 0 5) sourceC573) = raw9647 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9647; decide +kernel
    rw [ha]
    exact (canonical9647 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA573 + difference 5 1) (sourceB573 + difference 1 5) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA573 + difference 5 1) (sourceB573 + difference 1 5) sourceC573) = raw9648 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9648; decide +kernel
    rw [ha]
    exact (canonical9648 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA573 + difference 5 2) (sourceB573 + difference 2 5) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA573 + difference 5 2) (sourceB573 + difference 2 5) sourceC573) = raw9649 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9649; decide +kernel
    rw [ha]
    exact (canonical9649 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA573 + difference 5 3) (sourceB573 + difference 3 5) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA573 + difference 5 3) (sourceB573 + difference 3 5) sourceC573) = raw9650 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9650; decide +kernel
    rw [ha]
    exact (canonical9650 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA573 + difference 5 4) (sourceB573 + difference 4 5) sourceC573) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA573 + difference 5 4) (sourceB573 + difference 4 5) sourceC573) = raw9651 := by
      apply Matrix.ext; unfold tripleCharges sourceA573 sourceB573 sourceC573 difference raw9651; decide +kernel
    rw [ha]
    exact (canonical9651 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA573 sourceB573 sourceC573
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm573, Integer.Sparse.eval]
  linarith only [hs]

def sourceA574 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB574 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC574 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm574 : Integer.Sparse Master := [(Sum.inr 4865, 2), (Sum.inr 4868, 1), (Sum.inr 4874, 1), (Sum.inr 4894, 1), (Sum.inr 5161, 2), (Sum.inr 5175, 1), (Sum.inr 5249, 2), (Sum.inr 5258, 2), (Sum.inr 5260, 2), (Sum.inr 5264, 2), (Sum.inr 5275, 1), (Sum.inr 5276, 1), (Sum.inr 5279, 2), (Sum.inr 5282, 2), (Sum.inr 5291, 2), (Sum.inr 5293, 1), (Sum.inr 5297, 1), (Sum.inr 5300, 1), (Sum.inr 5305, 1), (Sum.inr 5308, 1), (Sum.inr 5310, 1)]

theorem sourceEq574 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm574 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA574 + difference 0 1) (sourceB574 + difference 1 0) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA574 + difference 0 1) (sourceB574 + difference 1 0) sourceC574) = raw9652 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9652; decide +kernel
    rw [ha]
    exact (canonical9652 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA574 + difference 0 2) (sourceB574 + difference 2 0) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA574 + difference 0 2) (sourceB574 + difference 2 0) sourceC574) = raw9653 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9653; decide +kernel
    rw [ha]
    exact (canonical9653 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA574 + difference 0 3) (sourceB574 + difference 3 0) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA574 + difference 0 3) (sourceB574 + difference 3 0) sourceC574) = raw9654 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9654; decide +kernel
    rw [ha]
    exact (canonical9654 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA574 + difference 0 4) (sourceB574 + difference 4 0) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA574 + difference 0 4) (sourceB574 + difference 4 0) sourceC574) = raw9655 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9655; decide +kernel
    rw [ha]
    exact (canonical9655 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA574 + difference 0 5) (sourceB574 + difference 5 0) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA574 + difference 0 5) (sourceB574 + difference 5 0) sourceC574) = raw9656 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9656; decide +kernel
    rw [ha]
    exact (canonical9656 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA574 + difference 1 0) (sourceB574 + difference 0 1) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA574 + difference 1 0) (sourceB574 + difference 0 1) sourceC574) = raw9657 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9657; decide +kernel
    rw [ha]
    exact (canonical9657 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA574 + difference 1 2) (sourceB574 + difference 2 1) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA574 + difference 1 2) (sourceB574 + difference 2 1) sourceC574) = raw9658 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9658; decide +kernel
    rw [ha]
    exact (canonical9658 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA574 + difference 1 3) (sourceB574 + difference 3 1) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA574 + difference 1 3) (sourceB574 + difference 3 1) sourceC574) = raw9659 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9659; decide +kernel
    rw [ha]
    exact (canonical9659 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA574 + difference 1 4) (sourceB574 + difference 4 1) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5297) := by
    have ha : (tripleCharges (sourceA574 + difference 1 4) (sourceB574 + difference 4 1) sourceC574) = raw9660 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9660; decide +kernel
    rw [ha]
    exact (canonical9660 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA574 + difference 1 5) (sourceB574 + difference 5 1) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA574 + difference 1 5) (sourceB574 + difference 5 1) sourceC574) = raw9661 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9661; decide +kernel
    rw [ha]
    exact (canonical9661 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA574 + difference 2 0) (sourceB574 + difference 0 2) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA574 + difference 2 0) (sourceB574 + difference 0 2) sourceC574) = raw9662 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9662; decide +kernel
    rw [ha]
    exact (canonical9662 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA574 + difference 2 1) (sourceB574 + difference 1 2) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA574 + difference 2 1) (sourceB574 + difference 1 2) sourceC574) = raw9048 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9048; decide +kernel
    rw [ha]
    exact (canonical9048 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA574 + difference 2 3) (sourceB574 + difference 3 2) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA574 + difference 2 3) (sourceB574 + difference 3 2) sourceC574) = raw9663 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9663; decide +kernel
    rw [ha]
    exact (canonical9663 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA574 + difference 2 4) (sourceB574 + difference 4 2) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5279) := by
    have ha : (tripleCharges (sourceA574 + difference 2 4) (sourceB574 + difference 4 2) sourceC574) = raw9664 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9664; decide +kernel
    rw [ha]
    exact (canonical9664 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA574 + difference 2 5) (sourceB574 + difference 5 2) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA574 + difference 2 5) (sourceB574 + difference 5 2) sourceC574) = raw9041 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9041; decide +kernel
    rw [ha]
    exact (canonical9041 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA574 + difference 3 0) (sourceB574 + difference 0 3) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA574 + difference 3 0) (sourceB574 + difference 0 3) sourceC574) = raw9665 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9665; decide +kernel
    rw [ha]
    exact (canonical9665 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA574 + difference 3 1) (sourceB574 + difference 1 3) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA574 + difference 3 1) (sourceB574 + difference 1 3) sourceC574) = raw7930 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw7930; decide +kernel
    rw [ha]
    exact (canonical7930 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA574 + difference 3 2) (sourceB574 + difference 2 3) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA574 + difference 3 2) (sourceB574 + difference 2 3) sourceC574) = raw9666 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9666; decide +kernel
    rw [ha]
    exact (canonical9666 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA574 + difference 3 4) (sourceB574 + difference 4 3) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5279) := by
    have ha : (tripleCharges (sourceA574 + difference 3 4) (sourceB574 + difference 4 3) sourceC574) = raw9667 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9667; decide +kernel
    rw [ha]
    exact (canonical9667 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA574 + difference 3 5) (sourceB574 + difference 5 3) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA574 + difference 3 5) (sourceB574 + difference 5 3) sourceC574) = raw7924 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw7924; decide +kernel
    rw [ha]
    exact (canonical7924 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA574 + difference 4 0) (sourceB574 + difference 0 4) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA574 + difference 4 0) (sourceB574 + difference 0 4) sourceC574) = raw9668 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9668; decide +kernel
    rw [ha]
    exact (canonical9668 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA574 + difference 4 1) (sourceB574 + difference 1 4) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA574 + difference 4 1) (sourceB574 + difference 1 4) sourceC574) = raw7929 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw7929; decide +kernel
    rw [ha]
    exact (canonical7929 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA574 + difference 4 2) (sourceB574 + difference 2 4) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA574 + difference 4 2) (sourceB574 + difference 2 4) sourceC574) = raw9669 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9669; decide +kernel
    rw [ha]
    exact (canonical9669 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA574 + difference 4 3) (sourceB574 + difference 3 4) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA574 + difference 4 3) (sourceB574 + difference 3 4) sourceC574) = raw9670 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9670; decide +kernel
    rw [ha]
    exact (canonical9670 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA574 + difference 4 5) (sourceB574 + difference 5 4) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA574 + difference 4 5) (sourceB574 + difference 5 4) sourceC574) = raw7923 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw7923; decide +kernel
    rw [ha]
    exact (canonical7923 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA574 + difference 5 0) (sourceB574 + difference 0 5) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA574 + difference 5 0) (sourceB574 + difference 0 5) sourceC574) = raw9671 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9671; decide +kernel
    rw [ha]
    exact (canonical9671 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA574 + difference 5 1) (sourceB574 + difference 1 5) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA574 + difference 5 1) (sourceB574 + difference 1 5) sourceC574) = raw9672 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9672; decide +kernel
    rw [ha]
    exact (canonical9672 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA574 + difference 5 2) (sourceB574 + difference 2 5) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA574 + difference 5 2) (sourceB574 + difference 2 5) sourceC574) = raw9673 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9673; decide +kernel
    rw [ha]
    exact (canonical9673 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA574 + difference 5 3) (sourceB574 + difference 3 5) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA574 + difference 5 3) (sourceB574 + difference 3 5) sourceC574) = raw9674 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9674; decide +kernel
    rw [ha]
    exact (canonical9674 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA574 + difference 5 4) (sourceB574 + difference 4 5) sourceC574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA574 + difference 5 4) (sourceB574 + difference 4 5) sourceC574) = raw9675 := by
      apply Matrix.ext; unfold tripleCharges sourceA574 sourceB574 sourceC574 difference raw9675; decide +kernel
    rw [ha]
    exact (canonical9675 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA574 sourceB574 sourceC574
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm574, Integer.Sparse.eval]
  linarith only [hs]

def sourceA575 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB575 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC575 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm575 : Integer.Sparse Master := [(Sum.inr 2242, 2), (Sum.inr 2261, 1), (Sum.inr 2264, 1), (Sum.inr 2276, 1), (Sum.inr 2708, 2), (Sum.inr 2719, 2), (Sum.inr 2722, 2), (Sum.inr 2729, 2), (Sum.inr 2748, 2), (Sum.inr 2751, 2), (Sum.inr 2761, 1), (Sum.inr 2765, 2), (Sum.inr 2767, 1), (Sum.inr 2771, 1), (Sum.inr 2774, 1), (Sum.inr 2777, 1), (Sum.inr 2783, 1), (Sum.inr 2786, 1), (Sum.inr 3086, 2), (Sum.inr 3110, 1), (Sum.inr 3121, 1)]

theorem sourceEq575 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm575 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA575 + difference 0 1) (sourceB575 + difference 1 0) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA575 + difference 0 1) (sourceB575 + difference 1 0) sourceC575) = raw9676 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9676; decide +kernel
    rw [ha]
    exact (canonical9676 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA575 + difference 0 2) (sourceB575 + difference 2 0) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA575 + difference 0 2) (sourceB575 + difference 2 0) sourceC575) = raw9677 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9677; decide +kernel
    rw [ha]
    exact (canonical9677 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA575 + difference 0 3) (sourceB575 + difference 3 0) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA575 + difference 0 3) (sourceB575 + difference 3 0) sourceC575) = raw9678 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9678; decide +kernel
    rw [ha]
    exact (canonical9678 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA575 + difference 0 4) (sourceB575 + difference 4 0) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA575 + difference 0 4) (sourceB575 + difference 4 0) sourceC575) = raw9679 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9679; decide +kernel
    rw [ha]
    exact (canonical9679 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA575 + difference 0 5) (sourceB575 + difference 5 0) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA575 + difference 0 5) (sourceB575 + difference 5 0) sourceC575) = raw9680 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9680; decide +kernel
    rw [ha]
    exact (canonical9680 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA575 + difference 1 0) (sourceB575 + difference 0 1) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA575 + difference 1 0) (sourceB575 + difference 0 1) sourceC575) = raw9681 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9681; decide +kernel
    rw [ha]
    exact (canonical9681 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA575 + difference 1 2) (sourceB575 + difference 2 1) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA575 + difference 1 2) (sourceB575 + difference 2 1) sourceC575) = raw9682 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9682; decide +kernel
    rw [ha]
    exact (canonical9682 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA575 + difference 1 3) (sourceB575 + difference 3 1) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA575 + difference 1 3) (sourceB575 + difference 3 1) sourceC575) = raw9683 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9683; decide +kernel
    rw [ha]
    exact (canonical9683 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA575 + difference 1 4) (sourceB575 + difference 4 1) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2771) := by
    have ha : (tripleCharges (sourceA575 + difference 1 4) (sourceB575 + difference 4 1) sourceC575) = raw9684 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9684; decide +kernel
    rw [ha]
    exact (canonical9684 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA575 + difference 1 5) (sourceB575 + difference 5 1) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA575 + difference 1 5) (sourceB575 + difference 5 1) sourceC575) = raw9685 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9685; decide +kernel
    rw [ha]
    exact (canonical9685 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA575 + difference 2 0) (sourceB575 + difference 0 2) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA575 + difference 2 0) (sourceB575 + difference 0 2) sourceC575) = raw9686 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9686; decide +kernel
    rw [ha]
    exact (canonical9686 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA575 + difference 2 1) (sourceB575 + difference 1 2) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA575 + difference 2 1) (sourceB575 + difference 1 2) sourceC575) = raw9060 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9060; decide +kernel
    rw [ha]
    exact (canonical9060 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA575 + difference 2 3) (sourceB575 + difference 3 2) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA575 + difference 2 3) (sourceB575 + difference 3 2) sourceC575) = raw9687 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9687; decide +kernel
    rw [ha]
    exact (canonical9687 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA575 + difference 2 4) (sourceB575 + difference 4 2) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2748) := by
    have ha : (tripleCharges (sourceA575 + difference 2 4) (sourceB575 + difference 4 2) sourceC575) = raw9688 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9688; decide +kernel
    rw [ha]
    exact (canonical9688 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA575 + difference 2 5) (sourceB575 + difference 5 2) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA575 + difference 2 5) (sourceB575 + difference 5 2) sourceC575) = raw9053 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9053; decide +kernel
    rw [ha]
    exact (canonical9053 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA575 + difference 3 0) (sourceB575 + difference 0 3) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA575 + difference 3 0) (sourceB575 + difference 0 3) sourceC575) = raw9689 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9689; decide +kernel
    rw [ha]
    exact (canonical9689 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA575 + difference 3 1) (sourceB575 + difference 1 3) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA575 + difference 3 1) (sourceB575 + difference 1 3) sourceC575) = raw7943 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw7943; decide +kernel
    rw [ha]
    exact (canonical7943 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA575 + difference 3 2) (sourceB575 + difference 2 3) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA575 + difference 3 2) (sourceB575 + difference 2 3) sourceC575) = raw9690 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9690; decide +kernel
    rw [ha]
    exact (canonical9690 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA575 + difference 3 4) (sourceB575 + difference 4 3) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2748) := by
    have ha : (tripleCharges (sourceA575 + difference 3 4) (sourceB575 + difference 4 3) sourceC575) = raw9691 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9691; decide +kernel
    rw [ha]
    exact (canonical9691 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA575 + difference 3 5) (sourceB575 + difference 5 3) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA575 + difference 3 5) (sourceB575 + difference 5 3) sourceC575) = raw7937 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw7937; decide +kernel
    rw [ha]
    exact (canonical7937 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA575 + difference 4 0) (sourceB575 + difference 0 4) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA575 + difference 4 0) (sourceB575 + difference 0 4) sourceC575) = raw9692 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9692; decide +kernel
    rw [ha]
    exact (canonical9692 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA575 + difference 4 1) (sourceB575 + difference 1 4) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2786) := by
    have ha : (tripleCharges (sourceA575 + difference 4 1) (sourceB575 + difference 1 4) sourceC575) = raw7942 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw7942; decide +kernel
    rw [ha]
    exact (canonical7942 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA575 + difference 4 2) (sourceB575 + difference 2 4) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA575 + difference 4 2) (sourceB575 + difference 2 4) sourceC575) = raw9693 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9693; decide +kernel
    rw [ha]
    exact (canonical9693 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA575 + difference 4 3) (sourceB575 + difference 3 4) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA575 + difference 4 3) (sourceB575 + difference 3 4) sourceC575) = raw9694 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9694; decide +kernel
    rw [ha]
    exact (canonical9694 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA575 + difference 4 5) (sourceB575 + difference 5 4) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA575 + difference 4 5) (sourceB575 + difference 5 4) sourceC575) = raw7936 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw7936; decide +kernel
    rw [ha]
    exact (canonical7936 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA575 + difference 5 0) (sourceB575 + difference 0 5) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA575 + difference 5 0) (sourceB575 + difference 0 5) sourceC575) = raw9695 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9695; decide +kernel
    rw [ha]
    exact (canonical9695 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA575 + difference 5 1) (sourceB575 + difference 1 5) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA575 + difference 5 1) (sourceB575 + difference 1 5) sourceC575) = raw9696 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9696; decide +kernel
    rw [ha]
    exact (canonical9696 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA575 + difference 5 2) (sourceB575 + difference 2 5) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA575 + difference 5 2) (sourceB575 + difference 2 5) sourceC575) = raw9697 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9697; decide +kernel
    rw [ha]
    exact (canonical9697 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA575 + difference 5 3) (sourceB575 + difference 3 5) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA575 + difference 5 3) (sourceB575 + difference 3 5) sourceC575) = raw9698 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9698; decide +kernel
    rw [ha]
    exact (canonical9698 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA575 + difference 5 4) (sourceB575 + difference 4 5) sourceC575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA575 + difference 5 4) (sourceB575 + difference 4 5) sourceC575) = raw9699 := by
      apply Matrix.ext; unfold tripleCharges sourceA575 sourceB575 sourceC575 difference raw9699; decide +kernel
    rw [ha]
    exact (canonical9699 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA575 sourceB575 sourceC575
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm575, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
