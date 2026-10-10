import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical106
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical116
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical117
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical122
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical131
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical133
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical134
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical135
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical136
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical137
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical139
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical140
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical141

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1056 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1056 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1056 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceForm1056 : Integer.Sparse Master := [(Sum.inr 2077, 1), (Sum.inr 2079, 1), (Sum.inr 2082, 1), (Sum.inr 2107, 1), (Sum.inr 2216, 1), (Sum.inr 2477, 1), (Sum.inr 2488, 1), (Sum.inr 2505, 1), (Sum.inr 2765, 1), (Sum.inr 3687, 1), (Sum.inr 3693, 1), (Sum.inr 3702, 1), (Sum.inr 3721, 1), (Sum.inr 3737, 1), (Sum.inr 3751, 1), (Sum.inr 3771, 1), (Sum.inr 3787, 1), (Sum.inr 3796, 1), (Sum.inr 3850, 1), (Sum.inr 3875, 1), (Sum.inr 3876, 1), (Sum.inr 3887, 1), (Sum.inr 3888, 1), (Sum.inr 3906, 1), (Sum.inr 3907, 1), (Sum.inr 3979, 1), (Sum.inr 3982, 1), (Sum.inr 3983, 1), (Sum.inr 4013, 1), (Sum.inr 4017, 1)]

theorem sourceEq1056 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1056 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1056 + difference 0 1) (sourceB1056 + difference 1 0) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA1056 + difference 0 1) (sourceB1056 + difference 1 0) sourceC1056) = raw17344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17344; decide +kernel
    rw [ha]
    exact (canonical17344 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1056 + difference 0 2) (sourceB1056 + difference 2 0) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA1056 + difference 0 2) (sourceB1056 + difference 2 0) sourceC1056) = raw17345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17345; decide +kernel
    rw [ha]
    exact (canonical17345 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1056 + difference 0 3) (sourceB1056 + difference 3 0) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA1056 + difference 0 3) (sourceB1056 + difference 3 0) sourceC1056) = raw17346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17346; decide +kernel
    rw [ha]
    exact (canonical17346 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1056 + difference 0 4) (sourceB1056 + difference 4 0) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3906) := by
    have ha : (tripleCharges (sourceA1056 + difference 0 4) (sourceB1056 + difference 4 0) sourceC1056) = raw17347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17347; decide +kernel
    rw [ha]
    exact (canonical17347 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1056 + difference 0 5) (sourceB1056 + difference 5 0) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA1056 + difference 0 5) (sourceB1056 + difference 5 0) sourceC1056) = raw17348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17348; decide +kernel
    rw [ha]
    exact (canonical17348 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1056 + difference 1 0) (sourceB1056 + difference 0 1) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA1056 + difference 1 0) (sourceB1056 + difference 0 1) sourceC1056) = raw17349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17349; decide +kernel
    rw [ha]
    exact (canonical17349 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1056 + difference 1 2) (sourceB1056 + difference 2 1) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA1056 + difference 1 2) (sourceB1056 + difference 2 1) sourceC1056) = raw17350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17350; decide +kernel
    rw [ha]
    exact (canonical17350 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1056 + difference 1 3) (sourceB1056 + difference 3 1) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1056 + difference 1 3) (sourceB1056 + difference 3 1) sourceC1056) = raw17351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17351; decide +kernel
    rw [ha]
    exact (canonical17351 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1056 + difference 1 4) (sourceB1056 + difference 4 1) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA1056 + difference 1 4) (sourceB1056 + difference 4 1) sourceC1056) = raw17352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17352; decide +kernel
    rw [ha]
    exact (canonical17352 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1056 + difference 1 5) (sourceB1056 + difference 5 1) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4017) := by
    have ha : (tripleCharges (sourceA1056 + difference 1 5) (sourceB1056 + difference 5 1) sourceC1056) = raw17353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17353; decide +kernel
    rw [ha]
    exact (canonical17353 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1056 + difference 2 0) (sourceB1056 + difference 0 2) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2505) := by
    have ha : (tripleCharges (sourceA1056 + difference 2 0) (sourceB1056 + difference 0 2) sourceC1056) = raw17354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17354; decide +kernel
    rw [ha]
    exact (canonical17354 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1056 + difference 2 1) (sourceB1056 + difference 1 2) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3702) := by
    have ha : (tripleCharges (sourceA1056 + difference 2 1) (sourceB1056 + difference 1 2) sourceC1056) = raw17355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17355; decide +kernel
    rw [ha]
    exact (canonical17355 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1056 + difference 2 3) (sourceB1056 + difference 3 2) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3751) := by
    have ha : (tripleCharges (sourceA1056 + difference 2 3) (sourceB1056 + difference 3 2) sourceC1056) = raw17356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17356; decide +kernel
    rw [ha]
    exact (canonical17356 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1056 + difference 2 4) (sourceB1056 + difference 4 2) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3771) := by
    have ha : (tripleCharges (sourceA1056 + difference 2 4) (sourceB1056 + difference 4 2) sourceC1056) = raw17357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17357; decide +kernel
    rw [ha]
    exact (canonical17357 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1056 + difference 2 5) (sourceB1056 + difference 5 2) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA1056 + difference 2 5) (sourceB1056 + difference 5 2) sourceC1056) = raw17358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17358; decide +kernel
    rw [ha]
    exact (canonical17358 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1056 + difference 3 0) (sourceB1056 + difference 0 3) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA1056 + difference 3 0) (sourceB1056 + difference 0 3) sourceC1056) = raw17359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17359; decide +kernel
    rw [ha]
    exact (canonical17359 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1056 + difference 3 1) (sourceB1056 + difference 1 3) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3687) := by
    have ha : (tripleCharges (sourceA1056 + difference 3 1) (sourceB1056 + difference 1 3) sourceC1056) = raw17360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17360; decide +kernel
    rw [ha]
    exact (canonical17360 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1056 + difference 3 2) (sourceB1056 + difference 2 3) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3787) := by
    have ha : (tripleCharges (sourceA1056 + difference 3 2) (sourceB1056 + difference 2 3) sourceC1056) = raw17361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17361; decide +kernel
    rw [ha]
    exact (canonical17361 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1056 + difference 3 4) (sourceB1056 + difference 4 3) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA1056 + difference 3 4) (sourceB1056 + difference 4 3) sourceC1056) = raw17362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17362; decide +kernel
    rw [ha]
    exact (canonical17362 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1056 + difference 3 5) (sourceB1056 + difference 5 3) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA1056 + difference 3 5) (sourceB1056 + difference 5 3) sourceC1056) = raw17363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17363; decide +kernel
    rw [ha]
    exact (canonical17363 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1056 + difference 4 0) (sourceB1056 + difference 0 4) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA1056 + difference 4 0) (sourceB1056 + difference 0 4) sourceC1056) = raw17364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17364; decide +kernel
    rw [ha]
    exact (canonical17364 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1056 + difference 4 1) (sourceB1056 + difference 1 4) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA1056 + difference 4 1) (sourceB1056 + difference 1 4) sourceC1056) = raw17365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17365; decide +kernel
    rw [ha]
    exact (canonical17365 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1056 + difference 4 2) (sourceB1056 + difference 2 4) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3737) := by
    have ha : (tripleCharges (sourceA1056 + difference 4 2) (sourceB1056 + difference 2 4) sourceC1056) = raw17366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17366; decide +kernel
    rw [ha]
    exact (canonical17366 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1056 + difference 4 3) (sourceB1056 + difference 3 4) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA1056 + difference 4 3) (sourceB1056 + difference 3 4) sourceC1056) = raw17367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17367; decide +kernel
    rw [ha]
    exact (canonical17367 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1056 + difference 4 5) (sourceB1056 + difference 5 4) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA1056 + difference 4 5) (sourceB1056 + difference 5 4) sourceC1056) = raw17368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17368; decide +kernel
    rw [ha]
    exact (canonical17368 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1056 + difference 5 0) (sourceB1056 + difference 0 5) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA1056 + difference 5 0) (sourceB1056 + difference 0 5) sourceC1056) = raw17369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17369; decide +kernel
    rw [ha]
    exact (canonical17369 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1056 + difference 5 1) (sourceB1056 + difference 1 5) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA1056 + difference 5 1) (sourceB1056 + difference 1 5) sourceC1056) = raw17370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17370; decide +kernel
    rw [ha]
    exact (canonical17370 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1056 + difference 5 2) (sourceB1056 + difference 2 5) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA1056 + difference 5 2) (sourceB1056 + difference 2 5) sourceC1056) = raw17371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17371; decide +kernel
    rw [ha]
    exact (canonical17371 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1056 + difference 5 3) (sourceB1056 + difference 3 5) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2077) := by
    have ha : (tripleCharges (sourceA1056 + difference 5 3) (sourceB1056 + difference 3 5) sourceC1056) = raw17372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17372; decide +kernel
    rw [ha]
    exact (canonical17372 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1056 + difference 5 4) (sourceB1056 + difference 4 5) sourceC1056) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1056 + difference 5 4) (sourceB1056 + difference 4 5) sourceC1056) = raw17373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1056 sourceB1056 sourceC1056 difference raw17373; decide +kernel
    rw [ha]
    exact (canonical17373 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1056 sourceB1056 sourceC1056
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1056, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1057 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceB1057 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1057 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1057 : Integer.Sparse Master := [(Sum.inr 5160, 1), (Sum.inr 5163, 1), (Sum.inr 5164, 1), (Sum.inr 5173, 1), (Sum.inr 5263, 1), (Sum.inr 5264, 1), (Sum.inr 5267, 1), (Sum.inr 5299, 1), (Sum.inr 5304, 1), (Sum.inr 5382, 1), (Sum.inr 5384, 1), (Sum.inr 5385, 1), (Sum.inr 5400, 1), (Sum.inr 5409, 1), (Sum.inr 5414, 1), (Sum.inr 5424, 1), (Sum.inr 5425, 1), (Sum.inr 5428, 2), (Sum.inr 5430, 1), (Sum.inr 5432, 1), (Sum.inr 5436, 1), (Sum.inr 5438, 1), (Sum.inr 5442, 1), (Sum.inr 5443, 1), (Sum.inr 5446, 1), (Sum.inr 5451, 1), (Sum.inr 5471, 1), (Sum.inr 5473, 1), (Sum.inr 5483, 1)]

theorem sourceEq1057 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1057 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1057 + difference 0 1) (sourceB1057 + difference 1 0) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA1057 + difference 0 1) (sourceB1057 + difference 1 0) sourceC1057) = raw17374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17374; decide +kernel
    rw [ha]
    exact (canonical17374 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1057 + difference 0 2) (sourceB1057 + difference 2 0) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1057 + difference 0 2) (sourceB1057 + difference 2 0) sourceC1057) = raw17375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17375; decide +kernel
    rw [ha]
    exact (canonical17375 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1057 + difference 0 3) (sourceB1057 + difference 3 0) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1057 + difference 0 3) (sourceB1057 + difference 3 0) sourceC1057) = raw17376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17376; decide +kernel
    rw [ha]
    exact (canonical17376 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1057 + difference 0 4) (sourceB1057 + difference 4 0) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA1057 + difference 0 4) (sourceB1057 + difference 4 0) sourceC1057) = raw17377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17377; decide +kernel
    rw [ha]
    exact (canonical17377 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1057 + difference 0 5) (sourceB1057 + difference 5 0) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1057 + difference 0 5) (sourceB1057 + difference 5 0) sourceC1057) = raw17378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17378; decide +kernel
    rw [ha]
    exact (canonical17378 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1057 + difference 1 0) (sourceB1057 + difference 0 1) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1057 + difference 1 0) (sourceB1057 + difference 0 1) sourceC1057) = raw15683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw15683; decide +kernel
    rw [ha]
    exact (canonical15683 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1057 + difference 1 2) (sourceB1057 + difference 2 1) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1057 + difference 1 2) (sourceB1057 + difference 2 1) sourceC1057) = raw17379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17379; decide +kernel
    rw [ha]
    exact (canonical17379 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1057 + difference 1 3) (sourceB1057 + difference 3 1) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1057 + difference 1 3) (sourceB1057 + difference 3 1) sourceC1057) = raw17380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17380; decide +kernel
    rw [ha]
    exact (canonical17380 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1057 + difference 1 4) (sourceB1057 + difference 4 1) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA1057 + difference 1 4) (sourceB1057 + difference 4 1) sourceC1057) = raw17381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17381; decide +kernel
    rw [ha]
    exact (canonical17381 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1057 + difference 1 5) (sourceB1057 + difference 5 1) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1057 + difference 1 5) (sourceB1057 + difference 5 1) sourceC1057) = raw15665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw15665; decide +kernel
    rw [ha]
    exact (canonical15665 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1057 + difference 2 0) (sourceB1057 + difference 0 2) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1057 + difference 2 0) (sourceB1057 + difference 0 2) sourceC1057) = raw17382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17382; decide +kernel
    rw [ha]
    exact (canonical17382 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1057 + difference 2 1) (sourceB1057 + difference 1 2) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5385) := by
    have ha : (tripleCharges (sourceA1057 + difference 2 1) (sourceB1057 + difference 1 2) sourceC1057) = raw17383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17383; decide +kernel
    rw [ha]
    exact (canonical17383 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1057 + difference 2 3) (sourceB1057 + difference 3 2) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5382) := by
    have ha : (tripleCharges (sourceA1057 + difference 2 3) (sourceB1057 + difference 3 2) sourceC1057) = raw17384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17384; decide +kernel
    rw [ha]
    exact (canonical17384 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1057 + difference 2 4) (sourceB1057 + difference 4 2) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA1057 + difference 2 4) (sourceB1057 + difference 4 2) sourceC1057) = raw17385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17385; decide +kernel
    rw [ha]
    exact (canonical17385 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1057 + difference 2 5) (sourceB1057 + difference 5 2) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1057 + difference 2 5) (sourceB1057 + difference 5 2) sourceC1057) = raw17386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17386; decide +kernel
    rw [ha]
    exact (canonical17386 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1057 + difference 3 0) (sourceB1057 + difference 0 3) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1057 + difference 3 0) (sourceB1057 + difference 0 3) sourceC1057) = raw15682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw15682; decide +kernel
    rw [ha]
    exact (canonical15682 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1057 + difference 3 1) (sourceB1057 + difference 1 3) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA1057 + difference 3 1) (sourceB1057 + difference 1 3) sourceC1057) = raw16863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw16863; decide +kernel
    rw [ha]
    exact (canonical16863 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1057 + difference 3 2) (sourceB1057 + difference 2 3) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1057 + difference 3 2) (sourceB1057 + difference 2 3) sourceC1057) = raw17127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17127; decide +kernel
    rw [ha]
    exact (canonical17127 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1057 + difference 3 4) (sourceB1057 + difference 4 3) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA1057 + difference 3 4) (sourceB1057 + difference 4 3) sourceC1057) = raw17387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17387; decide +kernel
    rw [ha]
    exact (canonical17387 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1057 + difference 3 5) (sourceB1057 + difference 5 3) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1057 + difference 3 5) (sourceB1057 + difference 5 3) sourceC1057) = raw15664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw15664; decide +kernel
    rw [ha]
    exact (canonical15664 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1057 + difference 4 0) (sourceB1057 + difference 0 4) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1057 + difference 4 0) (sourceB1057 + difference 0 4) sourceC1057) = raw17388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17388; decide +kernel
    rw [ha]
    exact (canonical17388 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1057 + difference 4 1) (sourceB1057 + difference 1 4) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1057 + difference 4 1) (sourceB1057 + difference 1 4) sourceC1057) = raw16862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw16862; decide +kernel
    rw [ha]
    exact (canonical16862 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1057 + difference 4 2) (sourceB1057 + difference 2 4) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1057 + difference 4 2) (sourceB1057 + difference 2 4) sourceC1057) = raw17126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17126; decide +kernel
    rw [ha]
    exact (canonical17126 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1057 + difference 4 3) (sourceB1057 + difference 3 4) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1057 + difference 4 3) (sourceB1057 + difference 3 4) sourceC1057) = raw17389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17389; decide +kernel
    rw [ha]
    exact (canonical17389 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1057 + difference 4 5) (sourceB1057 + difference 5 4) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1057 + difference 4 5) (sourceB1057 + difference 5 4) sourceC1057) = raw16843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw16843; decide +kernel
    rw [ha]
    exact (canonical16843 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1057 + difference 5 0) (sourceB1057 + difference 0 5) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA1057 + difference 5 0) (sourceB1057 + difference 0 5) sourceC1057) = raw17390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17390; decide +kernel
    rw [ha]
    exact (canonical17390 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1057 + difference 5 1) (sourceB1057 + difference 1 5) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA1057 + difference 5 1) (sourceB1057 + difference 1 5) sourceC1057) = raw17391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17391; decide +kernel
    rw [ha]
    exact (canonical17391 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1057 + difference 5 2) (sourceB1057 + difference 2 5) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA1057 + difference 5 2) (sourceB1057 + difference 2 5) sourceC1057) = raw17392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17392; decide +kernel
    rw [ha]
    exact (canonical17392 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1057 + difference 5 3) (sourceB1057 + difference 3 5) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA1057 + difference 5 3) (sourceB1057 + difference 3 5) sourceC1057) = raw17393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17393; decide +kernel
    rw [ha]
    exact (canonical17393 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1057 + difference 5 4) (sourceB1057 + difference 4 5) sourceC1057) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA1057 + difference 5 4) (sourceB1057 + difference 4 5) sourceC1057) = raw17394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1057 sourceB1057 sourceC1057 difference raw17394; decide +kernel
    rw [ha]
    exact (canonical17394 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1057 sourceB1057 sourceC1057
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1057, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1058 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceB1058 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1058 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1058 : Integer.Sparse Master := [(Sum.inr 2728, 1), (Sum.inr 2729, 1), (Sum.inr 2732, 1), (Sum.inr 2735, 1), (Sum.inr 2773, 1), (Sum.inr 3558, 1), (Sum.inr 3564, 1), (Sum.inr 3565, 1), (Sum.inr 3583, 1), (Sum.inr 3799, 1), (Sum.inr 3807, 1), (Sum.inr 3811, 1), (Sum.inr 3838, 1), (Sum.inr 3845, 1), (Sum.inr 3850, 1), (Sum.inr 3861, 1), (Sum.inr 3866, 1), (Sum.inr 3868, 1), (Sum.inr 3869, 1), (Sum.inr 3871, 1), (Sum.inr 3872, 1), (Sum.inr 3876, 1), (Sum.inr 3877, 1), (Sum.inr 3881, 1), (Sum.inr 3888, 1), (Sum.inr 3889, 1), (Sum.inr 3976, 1), (Sum.inr 3981, 1), (Sum.inr 3995, 1), (Sum.inr 4003, 1)]

theorem sourceEq1058 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1058 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1058 + difference 0 1) (sourceB1058 + difference 1 0) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA1058 + difference 0 1) (sourceB1058 + difference 1 0) sourceC1058) = raw17395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17395; decide +kernel
    rw [ha]
    exact (canonical17395 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1058 + difference 0 2) (sourceB1058 + difference 2 0) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA1058 + difference 0 2) (sourceB1058 + difference 2 0) sourceC1058) = raw17396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17396; decide +kernel
    rw [ha]
    exact (canonical17396 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1058 + difference 0 3) (sourceB1058 + difference 3 0) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA1058 + difference 0 3) (sourceB1058 + difference 3 0) sourceC1058) = raw17397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17397; decide +kernel
    rw [ha]
    exact (canonical17397 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1058 + difference 0 4) (sourceB1058 + difference 4 0) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA1058 + difference 0 4) (sourceB1058 + difference 4 0) sourceC1058) = raw17398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17398; decide +kernel
    rw [ha]
    exact (canonical17398 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1058 + difference 0 5) (sourceB1058 + difference 5 0) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA1058 + difference 0 5) (sourceB1058 + difference 5 0) sourceC1058) = raw17399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17399; decide +kernel
    rw [ha]
    exact (canonical17399 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1058 + difference 1 0) (sourceB1058 + difference 0 1) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA1058 + difference 1 0) (sourceB1058 + difference 0 1) sourceC1058) = raw15713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw15713; decide +kernel
    rw [ha]
    exact (canonical15713 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1058 + difference 1 2) (sourceB1058 + difference 2 1) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA1058 + difference 1 2) (sourceB1058 + difference 2 1) sourceC1058) = raw17400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17400; decide +kernel
    rw [ha]
    exact (canonical17400 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1058 + difference 1 3) (sourceB1058 + difference 3 1) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA1058 + difference 1 3) (sourceB1058 + difference 3 1) sourceC1058) = raw17401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17401; decide +kernel
    rw [ha]
    exact (canonical17401 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1058 + difference 1 4) (sourceB1058 + difference 4 1) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA1058 + difference 1 4) (sourceB1058 + difference 4 1) sourceC1058) = raw17402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17402; decide +kernel
    rw [ha]
    exact (canonical17402 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1058 + difference 1 5) (sourceB1058 + difference 5 1) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA1058 + difference 1 5) (sourceB1058 + difference 5 1) sourceC1058) = raw15687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw15687; decide +kernel
    rw [ha]
    exact (canonical15687 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1058 + difference 2 0) (sourceB1058 + difference 0 2) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA1058 + difference 2 0) (sourceB1058 + difference 0 2) sourceC1058) = raw17403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17403; decide +kernel
    rw [ha]
    exact (canonical17403 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1058 + difference 2 1) (sourceB1058 + difference 1 2) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3868) := by
    have ha : (tripleCharges (sourceA1058 + difference 2 1) (sourceB1058 + difference 1 2) sourceC1058) = raw17404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17404; decide +kernel
    rw [ha]
    exact (canonical17404 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1058 + difference 2 3) (sourceB1058 + difference 3 2) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA1058 + difference 2 3) (sourceB1058 + difference 3 2) sourceC1058) = raw17405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17405; decide +kernel
    rw [ha]
    exact (canonical17405 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1058 + difference 2 4) (sourceB1058 + difference 4 2) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA1058 + difference 2 4) (sourceB1058 + difference 4 2) sourceC1058) = raw17406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17406; decide +kernel
    rw [ha]
    exact (canonical17406 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1058 + difference 2 5) (sourceB1058 + difference 5 2) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1058 + difference 2 5) (sourceB1058 + difference 5 2) sourceC1058) = raw17407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17407; decide +kernel
    rw [ha]
    exact (canonical17407 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1058 + difference 3 0) (sourceB1058 + difference 0 3) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA1058 + difference 3 0) (sourceB1058 + difference 0 3) sourceC1058) = raw15711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw15711; decide +kernel
    rw [ha]
    exact (canonical15711 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1058 + difference 3 1) (sourceB1058 + difference 1 3) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA1058 + difference 3 1) (sourceB1058 + difference 1 3) sourceC1058) = raw16890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw16890; decide +kernel
    rw [ha]
    exact (canonical16890 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1058 + difference 3 2) (sourceB1058 + difference 2 3) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1058 + difference 3 2) (sourceB1058 + difference 2 3) sourceC1058) = raw17408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17408; decide +kernel
    rw [ha]
    exact (canonical17408 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1058 + difference 3 4) (sourceB1058 + difference 4 3) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA1058 + difference 3 4) (sourceB1058 + difference 4 3) sourceC1058) = raw17409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17409; decide +kernel
    rw [ha]
    exact (canonical17409 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1058 + difference 3 5) (sourceB1058 + difference 5 3) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3976) := by
    have ha : (tripleCharges (sourceA1058 + difference 3 5) (sourceB1058 + difference 5 3) sourceC1058) = raw15685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw15685; decide +kernel
    rw [ha]
    exact (canonical15685 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1058 + difference 4 0) (sourceB1058 + difference 0 4) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA1058 + difference 4 0) (sourceB1058 + difference 0 4) sourceC1058) = raw17410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17410; decide +kernel
    rw [ha]
    exact (canonical17410 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1058 + difference 4 1) (sourceB1058 + difference 1 4) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA1058 + difference 4 1) (sourceB1058 + difference 1 4) sourceC1058) = raw16889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw16889; decide +kernel
    rw [ha]
    exact (canonical16889 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1058 + difference 4 2) (sourceB1058 + difference 2 4) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3861) := by
    have ha : (tripleCharges (sourceA1058 + difference 4 2) (sourceB1058 + difference 2 4) sourceC1058) = raw17411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17411; decide +kernel
    rw [ha]
    exact (canonical17411 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1058 + difference 4 3) (sourceB1058 + difference 3 4) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA1058 + difference 4 3) (sourceB1058 + difference 3 4) sourceC1058) = raw17412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17412; decide +kernel
    rw [ha]
    exact (canonical17412 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1058 + difference 4 5) (sourceB1058 + difference 5 4) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1058 + difference 4 5) (sourceB1058 + difference 5 4) sourceC1058) = raw16870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw16870; decide +kernel
    rw [ha]
    exact (canonical16870 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1058 + difference 5 0) (sourceB1058 + difference 0 5) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA1058 + difference 5 0) (sourceB1058 + difference 0 5) sourceC1058) = raw17413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17413; decide +kernel
    rw [ha]
    exact (canonical17413 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1058 + difference 5 1) (sourceB1058 + difference 1 5) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA1058 + difference 5 1) (sourceB1058 + difference 1 5) sourceC1058) = raw17414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17414; decide +kernel
    rw [ha]
    exact (canonical17414 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1058 + difference 5 2) (sourceB1058 + difference 2 5) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA1058 + difference 5 2) (sourceB1058 + difference 2 5) sourceC1058) = raw17415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17415; decide +kernel
    rw [ha]
    exact (canonical17415 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1058 + difference 5 3) (sourceB1058 + difference 3 5) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA1058 + difference 5 3) (sourceB1058 + difference 3 5) sourceC1058) = raw17416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17416; decide +kernel
    rw [ha]
    exact (canonical17416 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1058 + difference 5 4) (sourceB1058 + difference 4 5) sourceC1058) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA1058 + difference 5 4) (sourceB1058 + difference 4 5) sourceC1058) = raw17417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1058 sourceB1058 sourceC1058 difference raw17417; decide +kernel
    rw [ha]
    exact (canonical17417 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1058 sourceB1058 sourceC1058
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1058, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1059 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1059 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1059 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceForm1059 : Integer.Sparse Master := [(Sum.inr 5047, 1), (Sum.inr 5050, 2), (Sum.inr 5059, 2), (Sum.inr 5073, 2), (Sum.inr 5259, 2), (Sum.inr 5341, 1), (Sum.inr 5346, 2), (Sum.inr 5352, 2), (Sum.inr 5424, 2), (Sum.inr 5467, 1), (Sum.inr 5473, 2), (Sum.inr 5476, 1), (Sum.inr 5478, 2), (Sum.inr 5482, 2), (Sum.inr 5483, 2), (Sum.inr 5490, 2), (Sum.inr 5491, 1), (Sum.inr 5500, 1)]

theorem sourceEq1059 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1059 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1059 + difference 0 1) (sourceB1059 + difference 1 0) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1059 + difference 0 1) (sourceB1059 + difference 1 0) sourceC1059) = raw3397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw3397; decide +kernel
    rw [ha]
    exact (canonical3397 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1059 + difference 0 2) (sourceB1059 + difference 2 0) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1059 + difference 0 2) (sourceB1059 + difference 2 0) sourceC1059) = raw3398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw3398; decide +kernel
    rw [ha]
    exact (canonical3398 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1059 + difference 0 3) (sourceB1059 + difference 3 0) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1059 + difference 0 3) (sourceB1059 + difference 3 0) sourceC1059) = raw3399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw3399; decide +kernel
    rw [ha]
    exact (canonical3399 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1059 + difference 0 4) (sourceB1059 + difference 4 0) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1059 + difference 0 4) (sourceB1059 + difference 4 0) sourceC1059) = raw3400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw3400; decide +kernel
    rw [ha]
    exact (canonical3400 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1059 + difference 0 5) (sourceB1059 + difference 5 0) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA1059 + difference 0 5) (sourceB1059 + difference 5 0) sourceC1059) = raw2628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw2628; decide +kernel
    rw [ha]
    exact (canonical2628 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1059 + difference 1 0) (sourceB1059 + difference 0 1) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA1059 + difference 1 0) (sourceB1059 + difference 0 1) sourceC1059) = raw17418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17418; decide +kernel
    rw [ha]
    exact (canonical17418 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1059 + difference 1 2) (sourceB1059 + difference 2 1) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1059 + difference 1 2) (sourceB1059 + difference 2 1) sourceC1059) = raw17419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17419; decide +kernel
    rw [ha]
    exact (canonical17419 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1059 + difference 1 3) (sourceB1059 + difference 3 1) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1059 + difference 1 3) (sourceB1059 + difference 3 1) sourceC1059) = raw17420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17420; decide +kernel
    rw [ha]
    exact (canonical17420 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1059 + difference 1 4) (sourceB1059 + difference 4 1) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1059 + difference 1 4) (sourceB1059 + difference 4 1) sourceC1059) = raw17421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17421; decide +kernel
    rw [ha]
    exact (canonical17421 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1059 + difference 1 5) (sourceB1059 + difference 5 1) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1059 + difference 1 5) (sourceB1059 + difference 5 1) sourceC1059) = raw3376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw3376; decide +kernel
    rw [ha]
    exact (canonical3376 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1059 + difference 2 0) (sourceB1059 + difference 0 2) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA1059 + difference 2 0) (sourceB1059 + difference 0 2) sourceC1059) = raw17422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17422; decide +kernel
    rw [ha]
    exact (canonical17422 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1059 + difference 2 1) (sourceB1059 + difference 1 2) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA1059 + difference 2 1) (sourceB1059 + difference 1 2) sourceC1059) = raw17423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17423; decide +kernel
    rw [ha]
    exact (canonical17423 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1059 + difference 2 3) (sourceB1059 + difference 3 2) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5467) := by
    have ha : (tripleCharges (sourceA1059 + difference 2 3) (sourceB1059 + difference 3 2) sourceC1059) = raw17424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17424; decide +kernel
    rw [ha]
    exact (canonical17424 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1059 + difference 2 4) (sourceB1059 + difference 4 2) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1059 + difference 2 4) (sourceB1059 + difference 4 2) sourceC1059) = raw17425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17425; decide +kernel
    rw [ha]
    exact (canonical17425 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1059 + difference 2 5) (sourceB1059 + difference 5 2) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1059 + difference 2 5) (sourceB1059 + difference 5 2) sourceC1059) = raw3381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw3381; decide +kernel
    rw [ha]
    exact (canonical3381 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1059 + difference 3 0) (sourceB1059 + difference 0 3) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1059 + difference 3 0) (sourceB1059 + difference 0 3) sourceC1059) = raw17426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17426; decide +kernel
    rw [ha]
    exact (canonical17426 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1059 + difference 3 1) (sourceB1059 + difference 1 3) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1059 + difference 3 1) (sourceB1059 + difference 1 3) sourceC1059) = raw17427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17427; decide +kernel
    rw [ha]
    exact (canonical17427 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1059 + difference 3 2) (sourceB1059 + difference 2 3) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5476) := by
    have ha : (tripleCharges (sourceA1059 + difference 3 2) (sourceB1059 + difference 2 3) sourceC1059) = raw17428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17428; decide +kernel
    rw [ha]
    exact (canonical17428 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1059 + difference 3 4) (sourceB1059 + difference 4 3) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1059 + difference 3 4) (sourceB1059 + difference 4 3) sourceC1059) = raw17429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17429; decide +kernel
    rw [ha]
    exact (canonical17429 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1059 + difference 3 5) (sourceB1059 + difference 5 3) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1059 + difference 3 5) (sourceB1059 + difference 5 3) sourceC1059) = raw3386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw3386; decide +kernel
    rw [ha]
    exact (canonical3386 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1059 + difference 4 0) (sourceB1059 + difference 0 4) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA1059 + difference 4 0) (sourceB1059 + difference 0 4) sourceC1059) = raw17430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17430; decide +kernel
    rw [ha]
    exact (canonical17430 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1059 + difference 4 1) (sourceB1059 + difference 1 4) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA1059 + difference 4 1) (sourceB1059 + difference 1 4) sourceC1059) = raw17431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17431; decide +kernel
    rw [ha]
    exact (canonical17431 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1059 + difference 4 2) (sourceB1059 + difference 2 4) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1059 + difference 4 2) (sourceB1059 + difference 2 4) sourceC1059) = raw17432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17432; decide +kernel
    rw [ha]
    exact (canonical17432 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1059 + difference 4 3) (sourceB1059 + difference 3 4) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA1059 + difference 4 3) (sourceB1059 + difference 3 4) sourceC1059) = raw17433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17433; decide +kernel
    rw [ha]
    exact (canonical17433 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1059 + difference 4 5) (sourceB1059 + difference 5 4) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1059 + difference 4 5) (sourceB1059 + difference 5 4) sourceC1059) = raw3391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw3391; decide +kernel
    rw [ha]
    exact (canonical3391 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1059 + difference 5 0) (sourceB1059 + difference 0 5) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5047) := by
    have ha : (tripleCharges (sourceA1059 + difference 5 0) (sourceB1059 + difference 0 5) sourceC1059) = raw17434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17434; decide +kernel
    rw [ha]
    exact (canonical17434 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1059 + difference 5 1) (sourceB1059 + difference 1 5) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA1059 + difference 5 1) (sourceB1059 + difference 1 5) sourceC1059) = raw17435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17435; decide +kernel
    rw [ha]
    exact (canonical17435 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1059 + difference 5 2) (sourceB1059 + difference 2 5) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1059 + difference 5 2) (sourceB1059 + difference 2 5) sourceC1059) = raw17436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17436; decide +kernel
    rw [ha]
    exact (canonical17436 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1059 + difference 5 3) (sourceB1059 + difference 3 5) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA1059 + difference 5 3) (sourceB1059 + difference 3 5) sourceC1059) = raw17437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17437; decide +kernel
    rw [ha]
    exact (canonical17437 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1059 + difference 5 4) (sourceB1059 + difference 4 5) sourceC1059) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA1059 + difference 5 4) (sourceB1059 + difference 4 5) sourceC1059) = raw17438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1059 sourceB1059 sourceC1059 difference raw17438; decide +kernel
    rw [ha]
    exact (canonical17438 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1059 sourceB1059 sourceC1059
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1059, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1060 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1060 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1060 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceForm1060 : Integer.Sparse Master := [(Sum.inr 2449, 1), (Sum.inr 2452, 2), (Sum.inr 2462, 2), (Sum.inr 2480, 2), (Sum.inr 2723, 2), (Sum.inr 3678, 1), (Sum.inr 3683, 2), (Sum.inr 3690, 2), (Sum.inr 3838, 2), (Sum.inr 3942, 1), (Sum.inr 3958, 2), (Sum.inr 3965, 1), (Sum.inr 3974, 2), (Sum.inr 3980, 2), (Sum.inr 3981, 2), (Sum.inr 4013, 2), (Sum.inr 4014, 1), (Sum.inr 4053, 1)]

theorem sourceEq1060 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1060 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1060 + difference 0 1) (sourceB1060 + difference 1 0) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA1060 + difference 0 1) (sourceB1060 + difference 1 0) sourceC1060) = raw17439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17439; decide +kernel
    rw [ha]
    exact (canonical17439 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1060 + difference 0 2) (sourceB1060 + difference 2 0) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA1060 + difference 0 2) (sourceB1060 + difference 2 0) sourceC1060) = raw17440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17440; decide +kernel
    rw [ha]
    exact (canonical17440 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1060 + difference 0 3) (sourceB1060 + difference 3 0) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA1060 + difference 0 3) (sourceB1060 + difference 3 0) sourceC1060) = raw17441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17441; decide +kernel
    rw [ha]
    exact (canonical17441 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1060 + difference 0 4) (sourceB1060 + difference 4 0) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA1060 + difference 0 4) (sourceB1060 + difference 4 0) sourceC1060) = raw17442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17442; decide +kernel
    rw [ha]
    exact (canonical17442 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1060 + difference 0 5) (sourceB1060 + difference 5 0) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4053) := by
    have ha : (tripleCharges (sourceA1060 + difference 0 5) (sourceB1060 + difference 5 0) sourceC1060) = raw17443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17443; decide +kernel
    rw [ha]
    exact (canonical17443 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1060 + difference 1 0) (sourceB1060 + difference 0 1) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA1060 + difference 1 0) (sourceB1060 + difference 0 1) sourceC1060) = raw17444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17444; decide +kernel
    rw [ha]
    exact (canonical17444 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1060 + difference 1 2) (sourceB1060 + difference 2 1) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1060 + difference 1 2) (sourceB1060 + difference 2 1) sourceC1060) = raw17445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17445; decide +kernel
    rw [ha]
    exact (canonical17445 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1060 + difference 1 3) (sourceB1060 + difference 3 1) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1060 + difference 1 3) (sourceB1060 + difference 3 1) sourceC1060) = raw17446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17446; decide +kernel
    rw [ha]
    exact (canonical17446 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1060 + difference 1 4) (sourceB1060 + difference 4 1) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4014) := by
    have ha : (tripleCharges (sourceA1060 + difference 1 4) (sourceB1060 + difference 4 1) sourceC1060) = raw17447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17447; decide +kernel
    rw [ha]
    exact (canonical17447 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1060 + difference 1 5) (sourceB1060 + difference 5 1) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA1060 + difference 1 5) (sourceB1060 + difference 5 1) sourceC1060) = raw17448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17448; decide +kernel
    rw [ha]
    exact (canonical17448 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1060 + difference 2 0) (sourceB1060 + difference 0 2) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA1060 + difference 2 0) (sourceB1060 + difference 0 2) sourceC1060) = raw17449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17449; decide +kernel
    rw [ha]
    exact (canonical17449 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1060 + difference 2 1) (sourceB1060 + difference 1 2) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3683) := by
    have ha : (tripleCharges (sourceA1060 + difference 2 1) (sourceB1060 + difference 1 2) sourceC1060) = raw17450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17450; decide +kernel
    rw [ha]
    exact (canonical17450 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1060 + difference 2 3) (sourceB1060 + difference 3 2) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3942) := by
    have ha : (tripleCharges (sourceA1060 + difference 2 3) (sourceB1060 + difference 3 2) sourceC1060) = raw17451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17451; decide +kernel
    rw [ha]
    exact (canonical17451 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1060 + difference 2 4) (sourceB1060 + difference 4 2) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1060 + difference 2 4) (sourceB1060 + difference 4 2) sourceC1060) = raw17452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17452; decide +kernel
    rw [ha]
    exact (canonical17452 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1060 + difference 2 5) (sourceB1060 + difference 5 2) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA1060 + difference 2 5) (sourceB1060 + difference 5 2) sourceC1060) = raw17453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17453; decide +kernel
    rw [ha]
    exact (canonical17453 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1060 + difference 3 0) (sourceB1060 + difference 0 3) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA1060 + difference 3 0) (sourceB1060 + difference 0 3) sourceC1060) = raw17454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17454; decide +kernel
    rw [ha]
    exact (canonical17454 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1060 + difference 3 1) (sourceB1060 + difference 1 3) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA1060 + difference 3 1) (sourceB1060 + difference 1 3) sourceC1060) = raw17455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17455; decide +kernel
    rw [ha]
    exact (canonical17455 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1060 + difference 3 2) (sourceB1060 + difference 2 3) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3965) := by
    have ha : (tripleCharges (sourceA1060 + difference 3 2) (sourceB1060 + difference 2 3) sourceC1060) = raw17456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17456; decide +kernel
    rw [ha]
    exact (canonical17456 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1060 + difference 3 4) (sourceB1060 + difference 4 3) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1060 + difference 3 4) (sourceB1060 + difference 4 3) sourceC1060) = raw17457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17457; decide +kernel
    rw [ha]
    exact (canonical17457 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1060 + difference 3 5) (sourceB1060 + difference 5 3) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA1060 + difference 3 5) (sourceB1060 + difference 5 3) sourceC1060) = raw17458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17458; decide +kernel
    rw [ha]
    exact (canonical17458 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1060 + difference 4 0) (sourceB1060 + difference 0 4) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA1060 + difference 4 0) (sourceB1060 + difference 0 4) sourceC1060) = raw17459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17459; decide +kernel
    rw [ha]
    exact (canonical17459 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1060 + difference 4 1) (sourceB1060 + difference 1 4) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3678) := by
    have ha : (tripleCharges (sourceA1060 + difference 4 1) (sourceB1060 + difference 1 4) sourceC1060) = raw17460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17460; decide +kernel
    rw [ha]
    exact (canonical17460 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1060 + difference 4 2) (sourceB1060 + difference 2 4) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA1060 + difference 4 2) (sourceB1060 + difference 2 4) sourceC1060) = raw17461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17461; decide +kernel
    rw [ha]
    exact (canonical17461 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1060 + difference 4 3) (sourceB1060 + difference 3 4) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3683) := by
    have ha : (tripleCharges (sourceA1060 + difference 4 3) (sourceB1060 + difference 3 4) sourceC1060) = raw17462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17462; decide +kernel
    rw [ha]
    exact (canonical17462 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1060 + difference 4 5) (sourceB1060 + difference 5 4) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA1060 + difference 4 5) (sourceB1060 + difference 5 4) sourceC1060) = raw17463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17463; decide +kernel
    rw [ha]
    exact (canonical17463 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1060 + difference 5 0) (sourceB1060 + difference 0 5) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2449) := by
    have ha : (tripleCharges (sourceA1060 + difference 5 0) (sourceB1060 + difference 0 5) sourceC1060) = raw17464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17464; decide +kernel
    rw [ha]
    exact (canonical17464 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1060 + difference 5 1) (sourceB1060 + difference 1 5) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA1060 + difference 5 1) (sourceB1060 + difference 1 5) sourceC1060) = raw17465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17465; decide +kernel
    rw [ha]
    exact (canonical17465 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1060 + difference 5 2) (sourceB1060 + difference 2 5) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA1060 + difference 5 2) (sourceB1060 + difference 2 5) sourceC1060) = raw17466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17466; decide +kernel
    rw [ha]
    exact (canonical17466 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1060 + difference 5 3) (sourceB1060 + difference 3 5) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA1060 + difference 5 3) (sourceB1060 + difference 3 5) sourceC1060) = raw17467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17467; decide +kernel
    rw [ha]
    exact (canonical17467 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1060 + difference 5 4) (sourceB1060 + difference 4 5) sourceC1060) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA1060 + difference 5 4) (sourceB1060 + difference 4 5) sourceC1060) = raw17468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1060 sourceB1060 sourceC1060 difference raw17468; decide +kernel
    rw [ha]
    exact (canonical17468 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1060 sourceB1060 sourceC1060
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1060, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1061 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceB1061 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1061 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1061 : Integer.Sparse Master := [(Sum.inr 5394, 1), (Sum.inr 5395, 2), (Sum.inr 5397, 2), (Sum.inr 5410, 2), (Sum.inr 5420, 1), (Sum.inr 5421, 2), (Sum.inr 5423, 1), (Sum.inr 5424, 4), (Sum.inr 5425, 2), (Sum.inr 5430, 2), (Sum.inr 5434, 2), (Sum.inr 5445, 2), (Sum.inr 5468, 1), (Sum.inr 5473, 2), (Sum.inr 5477, 1), (Sum.inr 5483, 2), (Sum.inr 5487, 1)]

theorem sourceEq1061 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1061 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1061 + difference 0 1) (sourceB1061 + difference 1 0) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1061 + difference 0 1) (sourceB1061 + difference 1 0) sourceC1061) = raw17469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17469; decide +kernel
    rw [ha]
    exact (canonical17469 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1061 + difference 0 2) (sourceB1061 + difference 2 0) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1061 + difference 0 2) (sourceB1061 + difference 2 0) sourceC1061) = raw17470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17470; decide +kernel
    rw [ha]
    exact (canonical17470 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1061 + difference 0 3) (sourceB1061 + difference 3 0) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1061 + difference 0 3) (sourceB1061 + difference 3 0) sourceC1061) = raw17471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17471; decide +kernel
    rw [ha]
    exact (canonical17471 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1061 + difference 0 4) (sourceB1061 + difference 4 0) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1061 + difference 0 4) (sourceB1061 + difference 4 0) sourceC1061) = raw17472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17472; decide +kernel
    rw [ha]
    exact (canonical17472 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1061 + difference 0 5) (sourceB1061 + difference 5 0) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA1061 + difference 0 5) (sourceB1061 + difference 5 0) sourceC1061) = raw17473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17473; decide +kernel
    rw [ha]
    exact (canonical17473 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1061 + difference 1 0) (sourceB1061 + difference 0 1) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1061 + difference 1 0) (sourceB1061 + difference 0 1) sourceC1061) = raw17474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17474; decide +kernel
    rw [ha]
    exact (canonical17474 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1061 + difference 1 2) (sourceB1061 + difference 2 1) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1061 + difference 1 2) (sourceB1061 + difference 2 1) sourceC1061) = raw17475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17475; decide +kernel
    rw [ha]
    exact (canonical17475 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1061 + difference 1 3) (sourceB1061 + difference 3 1) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1061 + difference 1 3) (sourceB1061 + difference 3 1) sourceC1061) = raw17476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17476; decide +kernel
    rw [ha]
    exact (canonical17476 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1061 + difference 1 4) (sourceB1061 + difference 4 1) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1061 + difference 1 4) (sourceB1061 + difference 4 1) sourceC1061) = raw17477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17477; decide +kernel
    rw [ha]
    exact (canonical17477 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1061 + difference 1 5) (sourceB1061 + difference 5 1) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1061 + difference 1 5) (sourceB1061 + difference 5 1) sourceC1061) = raw17478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17478; decide +kernel
    rw [ha]
    exact (canonical17478 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1061 + difference 2 0) (sourceB1061 + difference 0 2) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1061 + difference 2 0) (sourceB1061 + difference 0 2) sourceC1061) = raw17479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17479; decide +kernel
    rw [ha]
    exact (canonical17479 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1061 + difference 2 1) (sourceB1061 + difference 1 2) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1061 + difference 2 1) (sourceB1061 + difference 1 2) sourceC1061) = raw17480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17480; decide +kernel
    rw [ha]
    exact (canonical17480 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1061 + difference 2 3) (sourceB1061 + difference 3 2) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5420) := by
    have ha : (tripleCharges (sourceA1061 + difference 2 3) (sourceB1061 + difference 3 2) sourceC1061) = raw17481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17481; decide +kernel
    rw [ha]
    exact (canonical17481 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1061 + difference 2 4) (sourceB1061 + difference 4 2) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1061 + difference 2 4) (sourceB1061 + difference 4 2) sourceC1061) = raw17482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17482; decide +kernel
    rw [ha]
    exact (canonical17482 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1061 + difference 2 5) (sourceB1061 + difference 5 2) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1061 + difference 2 5) (sourceB1061 + difference 5 2) sourceC1061) = raw17483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17483; decide +kernel
    rw [ha]
    exact (canonical17483 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1061 + difference 3 0) (sourceB1061 + difference 0 3) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1061 + difference 3 0) (sourceB1061 + difference 0 3) sourceC1061) = raw17484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17484; decide +kernel
    rw [ha]
    exact (canonical17484 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1061 + difference 3 1) (sourceB1061 + difference 1 3) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1061 + difference 3 1) (sourceB1061 + difference 1 3) sourceC1061) = raw16857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw16857; decide +kernel
    rw [ha]
    exact (canonical16857 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1061 + difference 3 2) (sourceB1061 + difference 2 3) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA1061 + difference 3 2) (sourceB1061 + difference 2 3) sourceC1061) = raw17125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17125; decide +kernel
    rw [ha]
    exact (canonical17125 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1061 + difference 3 4) (sourceB1061 + difference 4 3) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1061 + difference 3 4) (sourceB1061 + difference 4 3) sourceC1061) = raw16843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw16843; decide +kernel
    rw [ha]
    exact (canonical16843 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1061 + difference 3 5) (sourceB1061 + difference 5 3) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1061 + difference 3 5) (sourceB1061 + difference 5 3) sourceC1061) = raw17231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17231; decide +kernel
    rw [ha]
    exact (canonical17231 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1061 + difference 4 0) (sourceB1061 + difference 0 4) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1061 + difference 4 0) (sourceB1061 + difference 0 4) sourceC1061) = raw17485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17485; decide +kernel
    rw [ha]
    exact (canonical17485 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1061 + difference 4 1) (sourceB1061 + difference 1 4) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5468) := by
    have ha : (tripleCharges (sourceA1061 + difference 4 1) (sourceB1061 + difference 1 4) sourceC1061) = raw17486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17486; decide +kernel
    rw [ha]
    exact (canonical17486 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1061 + difference 4 2) (sourceB1061 + difference 2 4) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1061 + difference 4 2) (sourceB1061 + difference 2 4) sourceC1061) = raw17487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17487; decide +kernel
    rw [ha]
    exact (canonical17487 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1061 + difference 4 3) (sourceB1061 + difference 3 4) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1061 + difference 4 3) (sourceB1061 + difference 3 4) sourceC1061) = raw17488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17488; decide +kernel
    rw [ha]
    exact (canonical17488 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1061 + difference 4 5) (sourceB1061 + difference 5 4) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1061 + difference 4 5) (sourceB1061 + difference 5 4) sourceC1061) = raw17489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17489; decide +kernel
    rw [ha]
    exact (canonical17489 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1061 + difference 5 0) (sourceB1061 + difference 0 5) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA1061 + difference 5 0) (sourceB1061 + difference 0 5) sourceC1061) = raw17490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17490; decide +kernel
    rw [ha]
    exact (canonical17490 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1061 + difference 5 1) (sourceB1061 + difference 1 5) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1061 + difference 5 1) (sourceB1061 + difference 1 5) sourceC1061) = raw17491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17491; decide +kernel
    rw [ha]
    exact (canonical17491 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1061 + difference 5 2) (sourceB1061 + difference 2 5) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1061 + difference 5 2) (sourceB1061 + difference 2 5) sourceC1061) = raw17492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17492; decide +kernel
    rw [ha]
    exact (canonical17492 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1061 + difference 5 3) (sourceB1061 + difference 3 5) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1061 + difference 5 3) (sourceB1061 + difference 3 5) sourceC1061) = raw17493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17493; decide +kernel
    rw [ha]
    exact (canonical17493 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1061 + difference 5 4) (sourceB1061 + difference 4 5) sourceC1061) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1061 + difference 5 4) (sourceB1061 + difference 4 5) sourceC1061) = raw17389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1061 sourceB1061 sourceC1061 difference raw17389; decide +kernel
    rw [ha]
    exact (canonical17389 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1061 sourceB1061 sourceC1061
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1061, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1062 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceB1062 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1062 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1062 : Integer.Sparse Master := [(Sum.inr 3793, 1), (Sum.inr 3794, 2), (Sum.inr 3796, 2), (Sum.inr 3808, 2), (Sum.inr 3838, 2), (Sum.inr 3870, 1), (Sum.inr 3872, 2), (Sum.inr 3873, 2), (Sum.inr 3880, 2), (Sum.inr 3950, 1), (Sum.inr 3958, 2), (Sum.inr 3972, 2), (Sum.inr 3981, 2), (Sum.inr 3982, 2), (Sum.inr 3986, 1), (Sum.inr 3989, 1), (Sum.inr 3990, 2), (Sum.inr 4032, 1)]

theorem sourceEq1062 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1062 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1062 + difference 0 1) (sourceB1062 + difference 1 0) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA1062 + difference 0 1) (sourceB1062 + difference 1 0) sourceC1062) = raw17494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17494; decide +kernel
    rw [ha]
    exact (canonical17494 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1062 + difference 0 2) (sourceB1062 + difference 2 0) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA1062 + difference 0 2) (sourceB1062 + difference 2 0) sourceC1062) = raw17495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17495; decide +kernel
    rw [ha]
    exact (canonical17495 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1062 + difference 0 3) (sourceB1062 + difference 3 0) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA1062 + difference 0 3) (sourceB1062 + difference 3 0) sourceC1062) = raw17496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17496; decide +kernel
    rw [ha]
    exact (canonical17496 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1062 + difference 0 4) (sourceB1062 + difference 4 0) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA1062 + difference 0 4) (sourceB1062 + difference 4 0) sourceC1062) = raw17497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17497; decide +kernel
    rw [ha]
    exact (canonical17497 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1062 + difference 0 5) (sourceB1062 + difference 5 0) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4032) := by
    have ha : (tripleCharges (sourceA1062 + difference 0 5) (sourceB1062 + difference 5 0) sourceC1062) = raw17498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17498; decide +kernel
    rw [ha]
    exact (canonical17498 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1062 + difference 1 0) (sourceB1062 + difference 0 1) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA1062 + difference 1 0) (sourceB1062 + difference 0 1) sourceC1062) = raw17499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17499; decide +kernel
    rw [ha]
    exact (canonical17499 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1062 + difference 1 2) (sourceB1062 + difference 2 1) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1062 + difference 1 2) (sourceB1062 + difference 2 1) sourceC1062) = raw17500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17500; decide +kernel
    rw [ha]
    exact (canonical17500 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1062 + difference 1 3) (sourceB1062 + difference 3 1) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1062 + difference 1 3) (sourceB1062 + difference 3 1) sourceC1062) = raw17501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17501; decide +kernel
    rw [ha]
    exact (canonical17501 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1062 + difference 1 4) (sourceB1062 + difference 4 1) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3989) := by
    have ha : (tripleCharges (sourceA1062 + difference 1 4) (sourceB1062 + difference 4 1) sourceC1062) = raw17502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17502; decide +kernel
    rw [ha]
    exact (canonical17502 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1062 + difference 1 5) (sourceB1062 + difference 5 1) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA1062 + difference 1 5) (sourceB1062 + difference 5 1) sourceC1062) = raw17503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17503; decide +kernel
    rw [ha]
    exact (canonical17503 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1062 + difference 2 0) (sourceB1062 + difference 0 2) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA1062 + difference 2 0) (sourceB1062 + difference 0 2) sourceC1062) = raw17504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17504; decide +kernel
    rw [ha]
    exact (canonical17504 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1062 + difference 2 1) (sourceB1062 + difference 1 2) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA1062 + difference 2 1) (sourceB1062 + difference 1 2) sourceC1062) = raw17505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17505; decide +kernel
    rw [ha]
    exact (canonical17505 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1062 + difference 2 3) (sourceB1062 + difference 3 2) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3870) := by
    have ha : (tripleCharges (sourceA1062 + difference 2 3) (sourceB1062 + difference 3 2) sourceC1062) = raw17506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17506; decide +kernel
    rw [ha]
    exact (canonical17506 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1062 + difference 2 4) (sourceB1062 + difference 4 2) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1062 + difference 2 4) (sourceB1062 + difference 4 2) sourceC1062) = raw17507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17507; decide +kernel
    rw [ha]
    exact (canonical17507 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1062 + difference 2 5) (sourceB1062 + difference 5 2) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA1062 + difference 2 5) (sourceB1062 + difference 5 2) sourceC1062) = raw17508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17508; decide +kernel
    rw [ha]
    exact (canonical17508 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1062 + difference 3 0) (sourceB1062 + difference 0 3) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA1062 + difference 3 0) (sourceB1062 + difference 0 3) sourceC1062) = raw17509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17509; decide +kernel
    rw [ha]
    exact (canonical17509 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1062 + difference 3 1) (sourceB1062 + difference 1 3) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1062 + difference 3 1) (sourceB1062 + difference 1 3) sourceC1062) = raw16884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw16884; decide +kernel
    rw [ha]
    exact (canonical16884 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1062 + difference 3 2) (sourceB1062 + difference 2 3) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3986) := by
    have ha : (tripleCharges (sourceA1062 + difference 3 2) (sourceB1062 + difference 2 3) sourceC1062) = raw17510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17510; decide +kernel
    rw [ha]
    exact (canonical17510 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1062 + difference 3 4) (sourceB1062 + difference 4 3) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1062 + difference 3 4) (sourceB1062 + difference 4 3) sourceC1062) = raw16870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw16870; decide +kernel
    rw [ha]
    exact (canonical16870 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1062 + difference 3 5) (sourceB1062 + difference 5 3) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA1062 + difference 3 5) (sourceB1062 + difference 5 3) sourceC1062) = raw17511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17511; decide +kernel
    rw [ha]
    exact (canonical17511 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1062 + difference 4 0) (sourceB1062 + difference 0 4) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA1062 + difference 4 0) (sourceB1062 + difference 0 4) sourceC1062) = raw17512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17512; decide +kernel
    rw [ha]
    exact (canonical17512 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1062 + difference 4 1) (sourceB1062 + difference 1 4) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3950) := by
    have ha : (tripleCharges (sourceA1062 + difference 4 1) (sourceB1062 + difference 1 4) sourceC1062) = raw17513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17513; decide +kernel
    rw [ha]
    exact (canonical17513 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1062 + difference 4 2) (sourceB1062 + difference 2 4) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1062 + difference 4 2) (sourceB1062 + difference 2 4) sourceC1062) = raw17514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17514; decide +kernel
    rw [ha]
    exact (canonical17514 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1062 + difference 4 3) (sourceB1062 + difference 3 4) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA1062 + difference 4 3) (sourceB1062 + difference 3 4) sourceC1062) = raw17515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17515; decide +kernel
    rw [ha]
    exact (canonical17515 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1062 + difference 4 5) (sourceB1062 + difference 5 4) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA1062 + difference 4 5) (sourceB1062 + difference 5 4) sourceC1062) = raw17516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17516; decide +kernel
    rw [ha]
    exact (canonical17516 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1062 + difference 5 0) (sourceB1062 + difference 0 5) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3793) := by
    have ha : (tripleCharges (sourceA1062 + difference 5 0) (sourceB1062 + difference 0 5) sourceC1062) = raw17517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17517; decide +kernel
    rw [ha]
    exact (canonical17517 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1062 + difference 5 1) (sourceB1062 + difference 1 5) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA1062 + difference 5 1) (sourceB1062 + difference 1 5) sourceC1062) = raw17518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17518; decide +kernel
    rw [ha]
    exact (canonical17518 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1062 + difference 5 2) (sourceB1062 + difference 2 5) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA1062 + difference 5 2) (sourceB1062 + difference 2 5) sourceC1062) = raw17519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17519; decide +kernel
    rw [ha]
    exact (canonical17519 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1062 + difference 5 3) (sourceB1062 + difference 3 5) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA1062 + difference 5 3) (sourceB1062 + difference 3 5) sourceC1062) = raw17520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17520; decide +kernel
    rw [ha]
    exact (canonical17520 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1062 + difference 5 4) (sourceB1062 + difference 4 5) sourceC1062) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA1062 + difference 5 4) (sourceB1062 + difference 4 5) sourceC1062) = raw17412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1062 sourceB1062 sourceC1062 difference raw17412; decide +kernel
    rw [ha]
    exact (canonical17412 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1062 sourceB1062 sourceC1062
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1062, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1063 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1063 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC1063 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceForm1063 : Integer.Sparse Master := [(Sum.inr 5128, 1), (Sum.inr 5129, 1), (Sum.inr 5130, 1), (Sum.inr 5137, 1), (Sum.inr 5138, 1), (Sum.inr 5145, 1), (Sum.inr 5149, 1), (Sum.inr 5251, 1), (Sum.inr 5259, 1), (Sum.inr 5377, 1), (Sum.inr 5379, 1), (Sum.inr 5380, 1), (Sum.inr 5393, 1), (Sum.inr 5396, 1), (Sum.inr 5410, 1), (Sum.inr 5419, 1), (Sum.inr 5421, 1), (Sum.inr 5424, 2), (Sum.inr 5427, 1), (Sum.inr 5429, 1), (Sum.inr 5430, 1), (Sum.inr 5431, 1), (Sum.inr 5438, 1), (Sum.inr 5439, 1), (Sum.inr 5440, 1), (Sum.inr 5478, 1), (Sum.inr 5480, 1), (Sum.inr 5481, 1), (Sum.inr 5482, 1)]

theorem sourceEq1063 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1063 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1063 + difference 0 1) (sourceB1063 + difference 1 0) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1063 + difference 0 1) (sourceB1063 + difference 1 0) sourceC1063) = raw17521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17521; decide +kernel
    rw [ha]
    exact (canonical17521 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1063 + difference 0 2) (sourceB1063 + difference 2 0) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1063 + difference 0 2) (sourceB1063 + difference 2 0) sourceC1063) = raw17522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17522; decide +kernel
    rw [ha]
    exact (canonical17522 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1063 + difference 0 3) (sourceB1063 + difference 3 0) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5427) := by
    have ha : (tripleCharges (sourceA1063 + difference 0 3) (sourceB1063 + difference 3 0) sourceC1063) = raw17523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17523; decide +kernel
    rw [ha]
    exact (canonical17523 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1063 + difference 0 4) (sourceB1063 + difference 4 0) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1063 + difference 0 4) (sourceB1063 + difference 4 0) sourceC1063) = raw17524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17524; decide +kernel
    rw [ha]
    exact (canonical17524 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1063 + difference 0 5) (sourceB1063 + difference 5 0) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1063 + difference 0 5) (sourceB1063 + difference 5 0) sourceC1063) = raw17525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17525; decide +kernel
    rw [ha]
    exact (canonical17525 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1063 + difference 1 0) (sourceB1063 + difference 0 1) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA1063 + difference 1 0) (sourceB1063 + difference 0 1) sourceC1063) = raw17526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17526; decide +kernel
    rw [ha]
    exact (canonical17526 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1063 + difference 1 2) (sourceB1063 + difference 2 1) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1063 + difference 1 2) (sourceB1063 + difference 2 1) sourceC1063) = raw17527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17527; decide +kernel
    rw [ha]
    exact (canonical17527 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1063 + difference 1 3) (sourceB1063 + difference 3 1) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1063 + difference 1 3) (sourceB1063 + difference 3 1) sourceC1063) = raw17528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17528; decide +kernel
    rw [ha]
    exact (canonical17528 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1063 + difference 1 4) (sourceB1063 + difference 4 1) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1063 + difference 1 4) (sourceB1063 + difference 4 1) sourceC1063) = raw17529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17529; decide +kernel
    rw [ha]
    exact (canonical17529 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1063 + difference 1 5) (sourceB1063 + difference 5 1) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA1063 + difference 1 5) (sourceB1063 + difference 5 1) sourceC1063) = raw17530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17530; decide +kernel
    rw [ha]
    exact (canonical17530 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1063 + difference 2 0) (sourceB1063 + difference 0 2) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA1063 + difference 2 0) (sourceB1063 + difference 0 2) sourceC1063) = raw17531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17531; decide +kernel
    rw [ha]
    exact (canonical17531 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1063 + difference 2 1) (sourceB1063 + difference 1 2) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA1063 + difference 2 1) (sourceB1063 + difference 1 2) sourceC1063) = raw17532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17532; decide +kernel
    rw [ha]
    exact (canonical17532 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1063 + difference 2 3) (sourceB1063 + difference 3 2) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA1063 + difference 2 3) (sourceB1063 + difference 3 2) sourceC1063) = raw17533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17533; decide +kernel
    rw [ha]
    exact (canonical17533 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1063 + difference 2 4) (sourceB1063 + difference 4 2) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1063 + difference 2 4) (sourceB1063 + difference 4 2) sourceC1063) = raw17534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17534; decide +kernel
    rw [ha]
    exact (canonical17534 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1063 + difference 2 5) (sourceB1063 + difference 5 2) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1063 + difference 2 5) (sourceB1063 + difference 5 2) sourceC1063) = raw17535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17535; decide +kernel
    rw [ha]
    exact (canonical17535 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1063 + difference 3 0) (sourceB1063 + difference 0 3) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA1063 + difference 3 0) (sourceB1063 + difference 0 3) sourceC1063) = raw17536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17536; decide +kernel
    rw [ha]
    exact (canonical17536 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1063 + difference 3 1) (sourceB1063 + difference 1 3) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5419) := by
    have ha : (tripleCharges (sourceA1063 + difference 3 1) (sourceB1063 + difference 1 3) sourceC1063) = raw17537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17537; decide +kernel
    rw [ha]
    exact (canonical17537 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1063 + difference 3 2) (sourceB1063 + difference 2 3) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1063 + difference 3 2) (sourceB1063 + difference 2 3) sourceC1063) = raw17538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17538; decide +kernel
    rw [ha]
    exact (canonical17538 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1063 + difference 3 4) (sourceB1063 + difference 4 3) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1063 + difference 3 4) (sourceB1063 + difference 4 3) sourceC1063) = raw17539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17539; decide +kernel
    rw [ha]
    exact (canonical17539 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1063 + difference 3 5) (sourceB1063 + difference 5 3) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1063 + difference 3 5) (sourceB1063 + difference 5 3) sourceC1063) = raw17540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17540; decide +kernel
    rw [ha]
    exact (canonical17540 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1063 + difference 4 0) (sourceB1063 + difference 0 4) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA1063 + difference 4 0) (sourceB1063 + difference 0 4) sourceC1063) = raw17541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17541; decide +kernel
    rw [ha]
    exact (canonical17541 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1063 + difference 4 1) (sourceB1063 + difference 1 4) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5377) := by
    have ha : (tripleCharges (sourceA1063 + difference 4 1) (sourceB1063 + difference 1 4) sourceC1063) = raw17542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17542; decide +kernel
    rw [ha]
    exact (canonical17542 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1063 + difference 4 2) (sourceB1063 + difference 2 4) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA1063 + difference 4 2) (sourceB1063 + difference 2 4) sourceC1063) = raw17543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17543; decide +kernel
    rw [ha]
    exact (canonical17543 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1063 + difference 4 3) (sourceB1063 + difference 3 4) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA1063 + difference 4 3) (sourceB1063 + difference 3 4) sourceC1063) = raw17544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17544; decide +kernel
    rw [ha]
    exact (canonical17544 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1063 + difference 4 5) (sourceB1063 + difference 5 4) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1063 + difference 4 5) (sourceB1063 + difference 5 4) sourceC1063) = raw17545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17545; decide +kernel
    rw [ha]
    exact (canonical17545 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1063 + difference 5 0) (sourceB1063 + difference 0 5) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA1063 + difference 5 0) (sourceB1063 + difference 0 5) sourceC1063) = raw17546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17546; decide +kernel
    rw [ha]
    exact (canonical17546 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1063 + difference 5 1) (sourceB1063 + difference 1 5) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA1063 + difference 5 1) (sourceB1063 + difference 1 5) sourceC1063) = raw17547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17547; decide +kernel
    rw [ha]
    exact (canonical17547 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1063 + difference 5 2) (sourceB1063 + difference 2 5) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA1063 + difference 5 2) (sourceB1063 + difference 2 5) sourceC1063) = raw17548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17548; decide +kernel
    rw [ha]
    exact (canonical17548 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1063 + difference 5 3) (sourceB1063 + difference 3 5) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA1063 + difference 5 3) (sourceB1063 + difference 3 5) sourceC1063) = raw17549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17549; decide +kernel
    rw [ha]
    exact (canonical17549 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1063 + difference 5 4) (sourceB1063 + difference 4 5) sourceC1063) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA1063 + difference 5 4) (sourceB1063 + difference 4 5) sourceC1063) = raw17550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1063 sourceB1063 sourceC1063 difference raw17550; decide +kernel
    rw [ha]
    exact (canonical17550 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1063 sourceB1063 sourceC1063
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1063, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1064 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1064 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC1064 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceForm1064 : Integer.Sparse Master := [(Sum.inr 3516, 1), (Sum.inr 3517, 1), (Sum.inr 3519, 1), (Sum.inr 3520, 1), (Sum.inr 3521, 1), (Sum.inr 3539, 1), (Sum.inr 3544, 1), (Sum.inr 3562, 1), (Sum.inr 3605, 1), (Sum.inr 3797, 1), (Sum.inr 3798, 1), (Sum.inr 3816, 1), (Sum.inr 3832, 1), (Sum.inr 3835, 1), (Sum.inr 3836, 1), (Sum.inr 3842, 1), (Sum.inr 3843, 2), (Sum.inr 3844, 1), (Sum.inr 3848, 1), (Sum.inr 3857, 1), (Sum.inr 3858, 1), (Sum.inr 3859, 1), (Sum.inr 3873, 1), (Sum.inr 3874, 1), (Sum.inr 3875, 1), (Sum.inr 3974, 1), (Sum.inr 3978, 1), (Sum.inr 3991, 1), (Sum.inr 3992, 1)]

theorem sourceEq1064 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1064 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1064 + difference 0 1) (sourceB1064 + difference 1 0) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA1064 + difference 0 1) (sourceB1064 + difference 1 0) sourceC1064) = raw17551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17551; decide +kernel
    rw [ha]
    exact (canonical17551 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1064 + difference 0 2) (sourceB1064 + difference 2 0) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA1064 + difference 0 2) (sourceB1064 + difference 2 0) sourceC1064) = raw17552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17552; decide +kernel
    rw [ha]
    exact (canonical17552 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1064 + difference 0 3) (sourceB1064 + difference 3 0) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3844) := by
    have ha : (tripleCharges (sourceA1064 + difference 0 3) (sourceB1064 + difference 3 0) sourceC1064) = raw17553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17553; decide +kernel
    rw [ha]
    exact (canonical17553 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1064 + difference 0 4) (sourceB1064 + difference 4 0) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3859) := by
    have ha : (tripleCharges (sourceA1064 + difference 0 4) (sourceB1064 + difference 4 0) sourceC1064) = raw17554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17554; decide +kernel
    rw [ha]
    exact (canonical17554 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1064 + difference 0 5) (sourceB1064 + difference 5 0) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3992) := by
    have ha : (tripleCharges (sourceA1064 + difference 0 5) (sourceB1064 + difference 5 0) sourceC1064) = raw17555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17555; decide +kernel
    rw [ha]
    exact (canonical17555 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1064 + difference 1 0) (sourceB1064 + difference 0 1) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA1064 + difference 1 0) (sourceB1064 + difference 0 1) sourceC1064) = raw17556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17556; decide +kernel
    rw [ha]
    exact (canonical17556 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1064 + difference 1 2) (sourceB1064 + difference 2 1) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA1064 + difference 1 2) (sourceB1064 + difference 2 1) sourceC1064) = raw17557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17557; decide +kernel
    rw [ha]
    exact (canonical17557 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1064 + difference 1 3) (sourceB1064 + difference 3 1) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA1064 + difference 1 3) (sourceB1064 + difference 3 1) sourceC1064) = raw17558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17558; decide +kernel
    rw [ha]
    exact (canonical17558 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1064 + difference 1 4) (sourceB1064 + difference 4 1) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA1064 + difference 1 4) (sourceB1064 + difference 4 1) sourceC1064) = raw17559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17559; decide +kernel
    rw [ha]
    exact (canonical17559 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1064 + difference 1 5) (sourceB1064 + difference 5 1) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3991) := by
    have ha : (tripleCharges (sourceA1064 + difference 1 5) (sourceB1064 + difference 5 1) sourceC1064) = raw17560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17560; decide +kernel
    rw [ha]
    exact (canonical17560 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1064 + difference 2 0) (sourceB1064 + difference 0 2) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA1064 + difference 2 0) (sourceB1064 + difference 0 2) sourceC1064) = raw17561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17561; decide +kernel
    rw [ha]
    exact (canonical17561 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1064 + difference 2 1) (sourceB1064 + difference 1 2) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3797) := by
    have ha : (tripleCharges (sourceA1064 + difference 2 1) (sourceB1064 + difference 1 2) sourceC1064) = raw17562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17562; decide +kernel
    rw [ha]
    exact (canonical17562 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1064 + difference 2 3) (sourceB1064 + difference 3 2) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3798) := by
    have ha : (tripleCharges (sourceA1064 + difference 2 3) (sourceB1064 + difference 3 2) sourceC1064) = raw17563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17563; decide +kernel
    rw [ha]
    exact (canonical17563 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1064 + difference 2 4) (sourceB1064 + difference 4 2) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA1064 + difference 2 4) (sourceB1064 + difference 4 2) sourceC1064) = raw17564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17564; decide +kernel
    rw [ha]
    exact (canonical17564 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1064 + difference 2 5) (sourceB1064 + difference 5 2) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA1064 + difference 2 5) (sourceB1064 + difference 5 2) sourceC1064) = raw17565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17565; decide +kernel
    rw [ha]
    exact (canonical17565 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1064 + difference 3 0) (sourceB1064 + difference 0 3) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA1064 + difference 3 0) (sourceB1064 + difference 0 3) sourceC1064) = raw17566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17566; decide +kernel
    rw [ha]
    exact (canonical17566 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1064 + difference 3 1) (sourceB1064 + difference 1 3) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3842) := by
    have ha : (tripleCharges (sourceA1064 + difference 3 1) (sourceB1064 + difference 1 3) sourceC1064) = raw17567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17567; decide +kernel
    rw [ha]
    exact (canonical17567 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1064 + difference 3 2) (sourceB1064 + difference 2 3) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA1064 + difference 3 2) (sourceB1064 + difference 2 3) sourceC1064) = raw17568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17568; decide +kernel
    rw [ha]
    exact (canonical17568 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1064 + difference 3 4) (sourceB1064 + difference 4 3) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA1064 + difference 3 4) (sourceB1064 + difference 4 3) sourceC1064) = raw17569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17569; decide +kernel
    rw [ha]
    exact (canonical17569 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1064 + difference 3 5) (sourceB1064 + difference 5 3) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1064 + difference 3 5) (sourceB1064 + difference 5 3) sourceC1064) = raw17570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17570; decide +kernel
    rw [ha]
    exact (canonical17570 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1064 + difference 4 0) (sourceB1064 + difference 0 4) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA1064 + difference 4 0) (sourceB1064 + difference 0 4) sourceC1064) = raw17571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17571; decide +kernel
    rw [ha]
    exact (canonical17571 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1064 + difference 4 1) (sourceB1064 + difference 1 4) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3835) := by
    have ha : (tripleCharges (sourceA1064 + difference 4 1) (sourceB1064 + difference 1 4) sourceC1064) = raw17572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17572; decide +kernel
    rw [ha]
    exact (canonical17572 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1064 + difference 4 2) (sourceB1064 + difference 2 4) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA1064 + difference 4 2) (sourceB1064 + difference 2 4) sourceC1064) = raw17573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17573; decide +kernel
    rw [ha]
    exact (canonical17573 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1064 + difference 4 3) (sourceB1064 + difference 3 4) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3836) := by
    have ha : (tripleCharges (sourceA1064 + difference 4 3) (sourceB1064 + difference 3 4) sourceC1064) = raw17574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17574; decide +kernel
    rw [ha]
    exact (canonical17574 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1064 + difference 4 5) (sourceB1064 + difference 5 4) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA1064 + difference 4 5) (sourceB1064 + difference 5 4) sourceC1064) = raw17575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17575; decide +kernel
    rw [ha]
    exact (canonical17575 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1064 + difference 5 0) (sourceB1064 + difference 0 5) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA1064 + difference 5 0) (sourceB1064 + difference 0 5) sourceC1064) = raw17576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17576; decide +kernel
    rw [ha]
    exact (canonical17576 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1064 + difference 5 1) (sourceB1064 + difference 1 5) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA1064 + difference 5 1) (sourceB1064 + difference 1 5) sourceC1064) = raw17577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17577; decide +kernel
    rw [ha]
    exact (canonical17577 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1064 + difference 5 2) (sourceB1064 + difference 2 5) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA1064 + difference 5 2) (sourceB1064 + difference 2 5) sourceC1064) = raw17578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17578; decide +kernel
    rw [ha]
    exact (canonical17578 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1064 + difference 5 3) (sourceB1064 + difference 3 5) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3521) := by
    have ha : (tripleCharges (sourceA1064 + difference 5 3) (sourceB1064 + difference 3 5) sourceC1064) = raw17579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17579; decide +kernel
    rw [ha]
    exact (canonical17579 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1064 + difference 5 4) (sourceB1064 + difference 4 5) sourceC1064) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA1064 + difference 5 4) (sourceB1064 + difference 4 5) sourceC1064) = raw17580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1064 sourceB1064 sourceC1064 difference raw17580; decide +kernel
    rw [ha]
    exact (canonical17580 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1064 sourceB1064 sourceC1064
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1064, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1065 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1065 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1065 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceForm1065 : Integer.Sparse Master := [(Sum.inr 4779, 1), (Sum.inr 4782, 1), (Sum.inr 4787, 1), (Sum.inr 4802, 1), (Sum.inr 4831, 1), (Sum.inr 5050, 1), (Sum.inr 5056, 1), (Sum.inr 5072, 1), (Sum.inr 5258, 1), (Sum.inr 5341, 1), (Sum.inr 5344, 1), (Sum.inr 5346, 2), (Sum.inr 5351, 1), (Sum.inr 5352, 1), (Sum.inr 5365, 1), (Sum.inr 5416, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 2), (Sum.inr 5428, 1), (Sum.inr 5433, 2), (Sum.inr 5434, 1), (Sum.inr 5439, 1), (Sum.inr 5477, 1), (Sum.inr 5478, 1), (Sum.inr 5482, 1), (Sum.inr 5490, 1), (Sum.inr 5500, 1)]

theorem sourceEq1065 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1065 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1065 + difference 0 1) (sourceB1065 + difference 1 0) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA1065 + difference 0 1) (sourceB1065 + difference 1 0) sourceC1065) = raw17581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17581; decide +kernel
    rw [ha]
    exact (canonical17581 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1065 + difference 0 2) (sourceB1065 + difference 2 0) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1065 + difference 0 2) (sourceB1065 + difference 2 0) sourceC1065) = raw17582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17582; decide +kernel
    rw [ha]
    exact (canonical17582 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1065 + difference 0 3) (sourceB1065 + difference 3 0) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1065 + difference 0 3) (sourceB1065 + difference 3 0) sourceC1065) = raw17583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17583; decide +kernel
    rw [ha]
    exact (canonical17583 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1065 + difference 0 4) (sourceB1065 + difference 4 0) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1065 + difference 0 4) (sourceB1065 + difference 4 0) sourceC1065) = raw17584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17584; decide +kernel
    rw [ha]
    exact (canonical17584 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1065 + difference 0 5) (sourceB1065 + difference 5 0) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA1065 + difference 0 5) (sourceB1065 + difference 5 0) sourceC1065) = raw17585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17585; decide +kernel
    rw [ha]
    exact (canonical17585 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1065 + difference 1 0) (sourceB1065 + difference 0 1) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1065 + difference 1 0) (sourceB1065 + difference 0 1) sourceC1065) = raw12619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw12619; decide +kernel
    rw [ha]
    exact (canonical12619 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1065 + difference 1 2) (sourceB1065 + difference 2 1) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1065 + difference 1 2) (sourceB1065 + difference 2 1) sourceC1065) = raw17586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17586; decide +kernel
    rw [ha]
    exact (canonical17586 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1065 + difference 1 3) (sourceB1065 + difference 3 1) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1065 + difference 1 3) (sourceB1065 + difference 3 1) sourceC1065) = raw17587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17587; decide +kernel
    rw [ha]
    exact (canonical17587 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1065 + difference 1 4) (sourceB1065 + difference 4 1) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1065 + difference 1 4) (sourceB1065 + difference 4 1) sourceC1065) = raw17588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17588; decide +kernel
    rw [ha]
    exact (canonical17588 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1065 + difference 1 5) (sourceB1065 + difference 5 1) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1065 + difference 1 5) (sourceB1065 + difference 5 1) sourceC1065) = raw12593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw12593; decide +kernel
    rw [ha]
    exact (canonical12593 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1065 + difference 2 0) (sourceB1065 + difference 0 2) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA1065 + difference 2 0) (sourceB1065 + difference 0 2) sourceC1065) = raw17589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17589; decide +kernel
    rw [ha]
    exact (canonical17589 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1065 + difference 2 1) (sourceB1065 + difference 1 2) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA1065 + difference 2 1) (sourceB1065 + difference 1 2) sourceC1065) = raw17590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17590; decide +kernel
    rw [ha]
    exact (canonical17590 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1065 + difference 2 3) (sourceB1065 + difference 3 2) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA1065 + difference 2 3) (sourceB1065 + difference 3 2) sourceC1065) = raw17591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17591; decide +kernel
    rw [ha]
    exact (canonical17591 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1065 + difference 2 4) (sourceB1065 + difference 4 2) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA1065 + difference 2 4) (sourceB1065 + difference 4 2) sourceC1065) = raw17592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17592; decide +kernel
    rw [ha]
    exact (canonical17592 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1065 + difference 2 5) (sourceB1065 + difference 5 2) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1065 + difference 2 5) (sourceB1065 + difference 5 2) sourceC1065) = raw17593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17593; decide +kernel
    rw [ha]
    exact (canonical17593 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1065 + difference 3 0) (sourceB1065 + difference 0 3) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA1065 + difference 3 0) (sourceB1065 + difference 0 3) sourceC1065) = raw12617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw12617; decide +kernel
    rw [ha]
    exact (canonical12617 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1065 + difference 3 1) (sourceB1065 + difference 1 3) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1065 + difference 3 1) (sourceB1065 + difference 1 3) sourceC1065) = raw17594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17594; decide +kernel
    rw [ha]
    exact (canonical17594 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1065 + difference 3 2) (sourceB1065 + difference 2 3) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA1065 + difference 3 2) (sourceB1065 + difference 2 3) sourceC1065) = raw17595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17595; decide +kernel
    rw [ha]
    exact (canonical17595 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1065 + difference 3 4) (sourceB1065 + difference 4 3) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1065 + difference 3 4) (sourceB1065 + difference 4 3) sourceC1065) = raw17596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17596; decide +kernel
    rw [ha]
    exact (canonical17596 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1065 + difference 3 5) (sourceB1065 + difference 5 3) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1065 + difference 3 5) (sourceB1065 + difference 5 3) sourceC1065) = raw12591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw12591; decide +kernel
    rw [ha]
    exact (canonical12591 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1065 + difference 4 0) (sourceB1065 + difference 0 4) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA1065 + difference 4 0) (sourceB1065 + difference 0 4) sourceC1065) = raw17597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17597; decide +kernel
    rw [ha]
    exact (canonical17597 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1065 + difference 4 1) (sourceB1065 + difference 1 4) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA1065 + difference 4 1) (sourceB1065 + difference 1 4) sourceC1065) = raw17598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17598; decide +kernel
    rw [ha]
    exact (canonical17598 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1065 + difference 4 2) (sourceB1065 + difference 2 4) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1065 + difference 4 2) (sourceB1065 + difference 2 4) sourceC1065) = raw17599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17599; decide +kernel
    rw [ha]
    exact (canonical17599 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1065 + difference 4 3) (sourceB1065 + difference 3 4) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA1065 + difference 4 3) (sourceB1065 + difference 3 4) sourceC1065) = raw17600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17600; decide +kernel
    rw [ha]
    exact (canonical17600 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1065 + difference 4 5) (sourceB1065 + difference 5 4) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1065 + difference 4 5) (sourceB1065 + difference 5 4) sourceC1065) = raw17601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17601; decide +kernel
    rw [ha]
    exact (canonical17601 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1065 + difference 5 0) (sourceB1065 + difference 0 5) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA1065 + difference 5 0) (sourceB1065 + difference 0 5) sourceC1065) = raw17602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17602; decide +kernel
    rw [ha]
    exact (canonical17602 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1065 + difference 5 1) (sourceB1065 + difference 1 5) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA1065 + difference 5 1) (sourceB1065 + difference 1 5) sourceC1065) = raw17603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17603; decide +kernel
    rw [ha]
    exact (canonical17603 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1065 + difference 5 2) (sourceB1065 + difference 2 5) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA1065 + difference 5 2) (sourceB1065 + difference 2 5) sourceC1065) = raw17604 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17604; decide +kernel
    rw [ha]
    exact (canonical17604 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1065 + difference 5 3) (sourceB1065 + difference 3 5) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA1065 + difference 5 3) (sourceB1065 + difference 3 5) sourceC1065) = raw17605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17605; decide +kernel
    rw [ha]
    exact (canonical17605 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1065 + difference 5 4) (sourceB1065 + difference 4 5) sourceC1065) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA1065 + difference 5 4) (sourceB1065 + difference 4 5) sourceC1065) = raw17606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1065 sourceB1065 sourceC1065 difference raw17606; decide +kernel
    rw [ha]
    exact (canonical17606 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1065 sourceB1065 sourceC1065
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1065, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1066 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1066 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1066 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceForm1066 : Integer.Sparse Master := [(Sum.inr 1987, 1), (Sum.inr 1990, 1), (Sum.inr 2000, 1), (Sum.inr 2020, 1), (Sum.inr 2191, 1), (Sum.inr 2452, 1), (Sum.inr 2459, 1), (Sum.inr 2479, 1), (Sum.inr 2722, 1), (Sum.inr 3678, 1), (Sum.inr 3681, 1), (Sum.inr 3683, 1), (Sum.inr 3689, 1), (Sum.inr 3690, 1), (Sum.inr 3746, 1), (Sum.inr 3758, 1), (Sum.inr 3821, 1), (Sum.inr 3837, 1), (Sum.inr 3838, 1), (Sum.inr 3843, 1), (Sum.inr 3845, 1), (Sum.inr 3851, 1), (Sum.inr 3852, 1), (Sum.inr 3901, 1), (Sum.inr 3902, 1), (Sum.inr 3971, 1), (Sum.inr 3974, 1), (Sum.inr 3980, 1), (Sum.inr 4013, 1), (Sum.inr 4053, 1)]

theorem sourceEq1066 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1066 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1066 + difference 0 1) (sourceB1066 + difference 1 0) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA1066 + difference 0 1) (sourceB1066 + difference 1 0) sourceC1066) = raw17607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17607; decide +kernel
    rw [ha]
    exact (canonical17607 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1066 + difference 0 2) (sourceB1066 + difference 2 0) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA1066 + difference 0 2) (sourceB1066 + difference 2 0) sourceC1066) = raw17608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17608; decide +kernel
    rw [ha]
    exact (canonical17608 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1066 + difference 0 3) (sourceB1066 + difference 3 0) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA1066 + difference 0 3) (sourceB1066 + difference 3 0) sourceC1066) = raw17609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17609; decide +kernel
    rw [ha]
    exact (canonical17609 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1066 + difference 0 4) (sourceB1066 + difference 4 0) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3901) := by
    have ha : (tripleCharges (sourceA1066 + difference 0 4) (sourceB1066 + difference 4 0) sourceC1066) = raw17610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17610; decide +kernel
    rw [ha]
    exact (canonical17610 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1066 + difference 0 5) (sourceB1066 + difference 5 0) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4053) := by
    have ha : (tripleCharges (sourceA1066 + difference 0 5) (sourceB1066 + difference 5 0) sourceC1066) = raw17611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17611; decide +kernel
    rw [ha]
    exact (canonical17611 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1066 + difference 1 0) (sourceB1066 + difference 0 1) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA1066 + difference 1 0) (sourceB1066 + difference 0 1) sourceC1066) = raw12649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw12649; decide +kernel
    rw [ha]
    exact (canonical12649 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1066 + difference 1 2) (sourceB1066 + difference 2 1) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1066 + difference 1 2) (sourceB1066 + difference 2 1) sourceC1066) = raw17612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17612; decide +kernel
    rw [ha]
    exact (canonical17612 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1066 + difference 1 3) (sourceB1066 + difference 3 1) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA1066 + difference 1 3) (sourceB1066 + difference 3 1) sourceC1066) = raw17613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17613; decide +kernel
    rw [ha]
    exact (canonical17613 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1066 + difference 1 4) (sourceB1066 + difference 4 1) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA1066 + difference 1 4) (sourceB1066 + difference 4 1) sourceC1066) = raw17614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17614; decide +kernel
    rw [ha]
    exact (canonical17614 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1066 + difference 1 5) (sourceB1066 + difference 5 1) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA1066 + difference 1 5) (sourceB1066 + difference 5 1) sourceC1066) = raw12623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw12623; decide +kernel
    rw [ha]
    exact (canonical12623 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1066 + difference 2 0) (sourceB1066 + difference 0 2) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA1066 + difference 2 0) (sourceB1066 + difference 0 2) sourceC1066) = raw17615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17615; decide +kernel
    rw [ha]
    exact (canonical17615 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1066 + difference 2 1) (sourceB1066 + difference 1 2) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3681) := by
    have ha : (tripleCharges (sourceA1066 + difference 2 1) (sourceB1066 + difference 1 2) sourceC1066) = raw17616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17616; decide +kernel
    rw [ha]
    exact (canonical17616 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1066 + difference 2 3) (sourceB1066 + difference 3 2) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3746) := by
    have ha : (tripleCharges (sourceA1066 + difference 2 3) (sourceB1066 + difference 3 2) sourceC1066) = raw17617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17617; decide +kernel
    rw [ha]
    exact (canonical17617 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1066 + difference 2 4) (sourceB1066 + difference 4 2) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA1066 + difference 2 4) (sourceB1066 + difference 4 2) sourceC1066) = raw17618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17618; decide +kernel
    rw [ha]
    exact (canonical17618 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1066 + difference 2 5) (sourceB1066 + difference 5 2) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA1066 + difference 2 5) (sourceB1066 + difference 5 2) sourceC1066) = raw17619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17619; decide +kernel
    rw [ha]
    exact (canonical17619 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1066 + difference 3 0) (sourceB1066 + difference 0 3) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2479) := by
    have ha : (tripleCharges (sourceA1066 + difference 3 0) (sourceB1066 + difference 0 3) sourceC1066) = raw12647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw12647; decide +kernel
    rw [ha]
    exact (canonical12647 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1066 + difference 3 1) (sourceB1066 + difference 1 3) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3689) := by
    have ha : (tripleCharges (sourceA1066 + difference 3 1) (sourceB1066 + difference 1 3) sourceC1066) = raw17620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17620; decide +kernel
    rw [ha]
    exact (canonical17620 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1066 + difference 3 2) (sourceB1066 + difference 2 3) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3821) := by
    have ha : (tripleCharges (sourceA1066 + difference 3 2) (sourceB1066 + difference 2 3) sourceC1066) = raw17621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17621; decide +kernel
    rw [ha]
    exact (canonical17621 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1066 + difference 3 4) (sourceB1066 + difference 4 3) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA1066 + difference 3 4) (sourceB1066 + difference 4 3) sourceC1066) = raw17622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17622; decide +kernel
    rw [ha]
    exact (canonical17622 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1066 + difference 3 5) (sourceB1066 + difference 5 3) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA1066 + difference 3 5) (sourceB1066 + difference 5 3) sourceC1066) = raw12621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw12621; decide +kernel
    rw [ha]
    exact (canonical12621 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1066 + difference 4 0) (sourceB1066 + difference 0 4) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA1066 + difference 4 0) (sourceB1066 + difference 0 4) sourceC1066) = raw17623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17623; decide +kernel
    rw [ha]
    exact (canonical17623 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1066 + difference 4 1) (sourceB1066 + difference 1 4) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3678) := by
    have ha : (tripleCharges (sourceA1066 + difference 4 1) (sourceB1066 + difference 1 4) sourceC1066) = raw17624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17624; decide +kernel
    rw [ha]
    exact (canonical17624 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1066 + difference 4 2) (sourceB1066 + difference 2 4) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA1066 + difference 4 2) (sourceB1066 + difference 2 4) sourceC1066) = raw17625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17625; decide +kernel
    rw [ha]
    exact (canonical17625 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1066 + difference 4 3) (sourceB1066 + difference 3 4) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3683) := by
    have ha : (tripleCharges (sourceA1066 + difference 4 3) (sourceB1066 + difference 3 4) sourceC1066) = raw17626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17626; decide +kernel
    rw [ha]
    exact (canonical17626 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1066 + difference 4 5) (sourceB1066 + difference 5 4) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3971) := by
    have ha : (tripleCharges (sourceA1066 + difference 4 5) (sourceB1066 + difference 5 4) sourceC1066) = raw17627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17627; decide +kernel
    rw [ha]
    exact (canonical17627 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1066 + difference 5 0) (sourceB1066 + difference 0 5) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1987) := by
    have ha : (tripleCharges (sourceA1066 + difference 5 0) (sourceB1066 + difference 0 5) sourceC1066) = raw17628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17628; decide +kernel
    rw [ha]
    exact (canonical17628 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1066 + difference 5 1) (sourceB1066 + difference 1 5) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1990) := by
    have ha : (tripleCharges (sourceA1066 + difference 5 1) (sourceB1066 + difference 1 5) sourceC1066) = raw17629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17629; decide +kernel
    rw [ha]
    exact (canonical17629 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1066 + difference 5 2) (sourceB1066 + difference 2 5) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA1066 + difference 5 2) (sourceB1066 + difference 2 5) sourceC1066) = raw17630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17630; decide +kernel
    rw [ha]
    exact (canonical17630 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1066 + difference 5 3) (sourceB1066 + difference 3 5) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2000) := by
    have ha : (tripleCharges (sourceA1066 + difference 5 3) (sourceB1066 + difference 3 5) sourceC1066) = raw17631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17631; decide +kernel
    rw [ha]
    exact (canonical17631 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1066 + difference 5 4) (sourceB1066 + difference 4 5) sourceC1066) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1066 + difference 5 4) (sourceB1066 + difference 4 5) sourceC1066) = raw17632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1066 sourceB1066 sourceC1066 difference raw17632; decide +kernel
    rw [ha]
    exact (canonical17632 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1066 sourceB1066 sourceC1066
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1066, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1067 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB1067 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1067 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1067 : Integer.Sparse Master := [(Sum.inr 5134, 1), (Sum.inr 5135, 1), (Sum.inr 5138, 1), (Sum.inr 5160, 1), (Sum.inr 5271, 1), (Sum.inr 5378, 1), (Sum.inr 5379, 1), (Sum.inr 5381, 1), (Sum.inr 5382, 1), (Sum.inr 5394, 1), (Sum.inr 5395, 1), (Sum.inr 5397, 1), (Sum.inr 5409, 1), (Sum.inr 5410, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 1), (Sum.inr 5425, 3), (Sum.inr 5426, 1), (Sum.inr 5428, 1), (Sum.inr 5430, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 1), (Sum.inr 5438, 1), (Sum.inr 5442, 1), (Sum.inr 5445, 1), (Sum.inr 5477, 2), (Sum.inr 5483, 1)]

theorem sourceEq1067 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1067 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1067 + difference 0 1) (sourceB1067 + difference 1 0) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1067 + difference 0 1) (sourceB1067 + difference 1 0) sourceC1067) = raw17633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17633; decide +kernel
    rw [ha]
    exact (canonical17633 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1067 + difference 0 2) (sourceB1067 + difference 2 0) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1067 + difference 0 2) (sourceB1067 + difference 2 0) sourceC1067) = raw17634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17634; decide +kernel
    rw [ha]
    exact (canonical17634 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1067 + difference 0 3) (sourceB1067 + difference 3 0) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5426) := by
    have ha : (tripleCharges (sourceA1067 + difference 0 3) (sourceB1067 + difference 3 0) sourceC1067) = raw17635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17635; decide +kernel
    rw [ha]
    exact (canonical17635 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1067 + difference 0 4) (sourceB1067 + difference 4 0) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1067 + difference 0 4) (sourceB1067 + difference 4 0) sourceC1067) = raw17376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17376; decide +kernel
    rw [ha]
    exact (canonical17376 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1067 + difference 0 5) (sourceB1067 + difference 5 0) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1067 + difference 0 5) (sourceB1067 + difference 5 0) sourceC1067) = raw17472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17472; decide +kernel
    rw [ha]
    exact (canonical17472 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1067 + difference 1 0) (sourceB1067 + difference 0 1) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA1067 + difference 1 0) (sourceB1067 + difference 0 1) sourceC1067) = raw17636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17636; decide +kernel
    rw [ha]
    exact (canonical17636 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1067 + difference 1 2) (sourceB1067 + difference 2 1) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1067 + difference 1 2) (sourceB1067 + difference 2 1) sourceC1067) = raw17637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17637; decide +kernel
    rw [ha]
    exact (canonical17637 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1067 + difference 1 3) (sourceB1067 + difference 3 1) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1067 + difference 1 3) (sourceB1067 + difference 3 1) sourceC1067) = raw17638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17638; decide +kernel
    rw [ha]
    exact (canonical17638 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1067 + difference 1 4) (sourceB1067 + difference 4 1) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1067 + difference 1 4) (sourceB1067 + difference 4 1) sourceC1067) = raw17380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17380; decide +kernel
    rw [ha]
    exact (canonical17380 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1067 + difference 1 5) (sourceB1067 + difference 5 1) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1067 + difference 1 5) (sourceB1067 + difference 5 1) sourceC1067) = raw17477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17477; decide +kernel
    rw [ha]
    exact (canonical17477 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1067 + difference 2 0) (sourceB1067 + difference 0 2) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1067 + difference 2 0) (sourceB1067 + difference 0 2) sourceC1067) = raw17639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17639; decide +kernel
    rw [ha]
    exact (canonical17639 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1067 + difference 2 1) (sourceB1067 + difference 1 2) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA1067 + difference 2 1) (sourceB1067 + difference 1 2) sourceC1067) = raw17640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17640; decide +kernel
    rw [ha]
    exact (canonical17640 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1067 + difference 2 3) (sourceB1067 + difference 3 2) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA1067 + difference 2 3) (sourceB1067 + difference 3 2) sourceC1067) = raw17641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17641; decide +kernel
    rw [ha]
    exact (canonical17641 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1067 + difference 2 4) (sourceB1067 + difference 4 2) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5382) := by
    have ha : (tripleCharges (sourceA1067 + difference 2 4) (sourceB1067 + difference 4 2) sourceC1067) = raw17384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17384; decide +kernel
    rw [ha]
    exact (canonical17384 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1067 + difference 2 5) (sourceB1067 + difference 5 2) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1067 + difference 2 5) (sourceB1067 + difference 5 2) sourceC1067) = raw17482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17482; decide +kernel
    rw [ha]
    exact (canonical17482 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1067 + difference 3 0) (sourceB1067 + difference 0 3) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1067 + difference 3 0) (sourceB1067 + difference 0 3) sourceC1067) = raw17388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17388; decide +kernel
    rw [ha]
    exact (canonical17388 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1067 + difference 3 1) (sourceB1067 + difference 1 3) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1067 + difference 3 1) (sourceB1067 + difference 1 3) sourceC1067) = raw16862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw16862; decide +kernel
    rw [ha]
    exact (canonical16862 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1067 + difference 3 2) (sourceB1067 + difference 2 3) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1067 + difference 3 2) (sourceB1067 + difference 2 3) sourceC1067) = raw17126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17126; decide +kernel
    rw [ha]
    exact (canonical17126 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1067 + difference 3 4) (sourceB1067 + difference 4 3) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1067 + difference 3 4) (sourceB1067 + difference 4 3) sourceC1067) = raw17642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17642; decide +kernel
    rw [ha]
    exact (canonical17642 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1067 + difference 3 5) (sourceB1067 + difference 5 3) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1067 + difference 3 5) (sourceB1067 + difference 5 3) sourceC1067) = raw16843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw16843; decide +kernel
    rw [ha]
    exact (canonical16843 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1067 + difference 4 0) (sourceB1067 + difference 0 4) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA1067 + difference 4 0) (sourceB1067 + difference 0 4) sourceC1067) = raw17490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17490; decide +kernel
    rw [ha]
    exact (canonical17490 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1067 + difference 4 1) (sourceB1067 + difference 1 4) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1067 + difference 4 1) (sourceB1067 + difference 1 4) sourceC1067) = raw17491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17491; decide +kernel
    rw [ha]
    exact (canonical17491 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1067 + difference 4 2) (sourceB1067 + difference 2 4) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1067 + difference 4 2) (sourceB1067 + difference 2 4) sourceC1067) = raw17492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17492; decide +kernel
    rw [ha]
    exact (canonical17492 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1067 + difference 4 3) (sourceB1067 + difference 3 4) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1067 + difference 4 3) (sourceB1067 + difference 3 4) sourceC1067) = raw17493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17493; decide +kernel
    rw [ha]
    exact (canonical17493 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1067 + difference 4 5) (sourceB1067 + difference 5 4) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1067 + difference 4 5) (sourceB1067 + difference 5 4) sourceC1067) = raw17643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17643; decide +kernel
    rw [ha]
    exact (canonical17643 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1067 + difference 5 0) (sourceB1067 + difference 0 5) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA1067 + difference 5 0) (sourceB1067 + difference 0 5) sourceC1067) = raw17644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17644; decide +kernel
    rw [ha]
    exact (canonical17644 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1067 + difference 5 1) (sourceB1067 + difference 1 5) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA1067 + difference 5 1) (sourceB1067 + difference 1 5) sourceC1067) = raw17645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17645; decide +kernel
    rw [ha]
    exact (canonical17645 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1067 + difference 5 2) (sourceB1067 + difference 2 5) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA1067 + difference 5 2) (sourceB1067 + difference 2 5) sourceC1067) = raw17646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17646; decide +kernel
    rw [ha]
    exact (canonical17646 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1067 + difference 5 3) (sourceB1067 + difference 3 5) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA1067 + difference 5 3) (sourceB1067 + difference 3 5) sourceC1067) = raw17647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17647; decide +kernel
    rw [ha]
    exact (canonical17647 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1067 + difference 5 4) (sourceB1067 + difference 4 5) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA1067 + difference 5 4) (sourceB1067 + difference 4 5) sourceC1067) = raw17393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17393; decide +kernel
    rw [ha]
    exact (canonical17393 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1067 sourceB1067 sourceC1067
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1067, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1068 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB1068 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1068 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1068 : Integer.Sparse Master := [(Sum.inr 3514, 1), (Sum.inr 3515, 1), (Sum.inr 3517, 1), (Sum.inr 3534, 1), (Sum.inr 3558, 1), (Sum.inr 3793, 1), (Sum.inr 3794, 1), (Sum.inr 3795, 1), (Sum.inr 3796, 1), (Sum.inr 3807, 1), (Sum.inr 3808, 1), (Sum.inr 3832, 1), (Sum.inr 3834, 1), (Sum.inr 3837, 1), (Sum.inr 3839, 1), (Sum.inr 3840, 1), (Sum.inr 3841, 1), (Sum.inr 3845, 1), (Sum.inr 3852, 1), (Sum.inr 3853, 1), (Sum.inr 3861, 1), (Sum.inr 3866, 1), (Sum.inr 3871, 1), (Sum.inr 3872, 1), (Sum.inr 3876, 1), (Sum.inr 3880, 1), (Sum.inr 3971, 1), (Sum.inr 3981, 1), (Sum.inr 3989, 1), (Sum.inr 3990, 1)]

theorem sourceEq1068 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1068 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1068 + difference 0 1) (sourceB1068 + difference 1 0) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA1068 + difference 0 1) (sourceB1068 + difference 1 0) sourceC1068) = raw17648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17648; decide +kernel
    rw [ha]
    exact (canonical17648 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1068 + difference 0 2) (sourceB1068 + difference 2 0) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA1068 + difference 0 2) (sourceB1068 + difference 2 0) sourceC1068) = raw17649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17649; decide +kernel
    rw [ha]
    exact (canonical17649 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1068 + difference 0 3) (sourceB1068 + difference 3 0) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA1068 + difference 0 3) (sourceB1068 + difference 3 0) sourceC1068) = raw17650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17650; decide +kernel
    rw [ha]
    exact (canonical17650 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1068 + difference 0 4) (sourceB1068 + difference 4 0) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA1068 + difference 0 4) (sourceB1068 + difference 4 0) sourceC1068) = raw17397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17397; decide +kernel
    rw [ha]
    exact (canonical17397 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1068 + difference 0 5) (sourceB1068 + difference 5 0) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA1068 + difference 0 5) (sourceB1068 + difference 5 0) sourceC1068) = raw17497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17497; decide +kernel
    rw [ha]
    exact (canonical17497 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1068 + difference 1 0) (sourceB1068 + difference 0 1) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA1068 + difference 1 0) (sourceB1068 + difference 0 1) sourceC1068) = raw17651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17651; decide +kernel
    rw [ha]
    exact (canonical17651 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1068 + difference 1 2) (sourceB1068 + difference 2 1) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1068 + difference 1 2) (sourceB1068 + difference 2 1) sourceC1068) = raw17652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17652; decide +kernel
    rw [ha]
    exact (canonical17652 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1068 + difference 1 3) (sourceB1068 + difference 3 1) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA1068 + difference 1 3) (sourceB1068 + difference 3 1) sourceC1068) = raw17653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17653; decide +kernel
    rw [ha]
    exact (canonical17653 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1068 + difference 1 4) (sourceB1068 + difference 4 1) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA1068 + difference 1 4) (sourceB1068 + difference 4 1) sourceC1068) = raw17401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17401; decide +kernel
    rw [ha]
    exact (canonical17401 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1068 + difference 1 5) (sourceB1068 + difference 5 1) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3989) := by
    have ha : (tripleCharges (sourceA1068 + difference 1 5) (sourceB1068 + difference 5 1) sourceC1068) = raw17502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17502; decide +kernel
    rw [ha]
    exact (canonical17502 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1068 + difference 2 0) (sourceB1068 + difference 0 2) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA1068 + difference 2 0) (sourceB1068 + difference 0 2) sourceC1068) = raw17654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17654; decide +kernel
    rw [ha]
    exact (canonical17654 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1068 + difference 2 1) (sourceB1068 + difference 1 2) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA1068 + difference 2 1) (sourceB1068 + difference 1 2) sourceC1068) = raw17655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17655; decide +kernel
    rw [ha]
    exact (canonical17655 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1068 + difference 2 3) (sourceB1068 + difference 3 2) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA1068 + difference 2 3) (sourceB1068 + difference 3 2) sourceC1068) = raw17656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17656; decide +kernel
    rw [ha]
    exact (canonical17656 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1068 + difference 2 4) (sourceB1068 + difference 4 2) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA1068 + difference 2 4) (sourceB1068 + difference 4 2) sourceC1068) = raw17405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17405; decide +kernel
    rw [ha]
    exact (canonical17405 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1068 + difference 2 5) (sourceB1068 + difference 5 2) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1068 + difference 2 5) (sourceB1068 + difference 5 2) sourceC1068) = raw17507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17507; decide +kernel
    rw [ha]
    exact (canonical17507 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1068 + difference 3 0) (sourceB1068 + difference 0 3) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA1068 + difference 3 0) (sourceB1068 + difference 0 3) sourceC1068) = raw17410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17410; decide +kernel
    rw [ha]
    exact (canonical17410 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1068 + difference 3 1) (sourceB1068 + difference 1 3) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA1068 + difference 3 1) (sourceB1068 + difference 1 3) sourceC1068) = raw16889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw16889; decide +kernel
    rw [ha]
    exact (canonical16889 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1068 + difference 3 2) (sourceB1068 + difference 2 3) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3861) := by
    have ha : (tripleCharges (sourceA1068 + difference 3 2) (sourceB1068 + difference 2 3) sourceC1068) = raw17411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17411; decide +kernel
    rw [ha]
    exact (canonical17411 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1068 + difference 3 4) (sourceB1068 + difference 4 3) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1068 + difference 3 4) (sourceB1068 + difference 4 3) sourceC1068) = raw17657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17657; decide +kernel
    rw [ha]
    exact (canonical17657 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1068 + difference 3 5) (sourceB1068 + difference 5 3) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1068 + difference 3 5) (sourceB1068 + difference 5 3) sourceC1068) = raw16870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw16870; decide +kernel
    rw [ha]
    exact (canonical16870 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1068 + difference 4 0) (sourceB1068 + difference 0 4) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3793) := by
    have ha : (tripleCharges (sourceA1068 + difference 4 0) (sourceB1068 + difference 0 4) sourceC1068) = raw17517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17517; decide +kernel
    rw [ha]
    exact (canonical17517 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1068 + difference 4 1) (sourceB1068 + difference 1 4) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA1068 + difference 4 1) (sourceB1068 + difference 1 4) sourceC1068) = raw17518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17518; decide +kernel
    rw [ha]
    exact (canonical17518 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1068 + difference 4 2) (sourceB1068 + difference 2 4) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA1068 + difference 4 2) (sourceB1068 + difference 2 4) sourceC1068) = raw17519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17519; decide +kernel
    rw [ha]
    exact (canonical17519 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1068 + difference 4 3) (sourceB1068 + difference 3 4) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA1068 + difference 4 3) (sourceB1068 + difference 3 4) sourceC1068) = raw17520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17520; decide +kernel
    rw [ha]
    exact (canonical17520 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1068 + difference 4 5) (sourceB1068 + difference 5 4) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3971) := by
    have ha : (tripleCharges (sourceA1068 + difference 4 5) (sourceB1068 + difference 5 4) sourceC1068) = raw17658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17658; decide +kernel
    rw [ha]
    exact (canonical17658 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1068 + difference 5 0) (sourceB1068 + difference 0 5) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA1068 + difference 5 0) (sourceB1068 + difference 0 5) sourceC1068) = raw17659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17659; decide +kernel
    rw [ha]
    exact (canonical17659 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1068 + difference 5 1) (sourceB1068 + difference 1 5) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3515) := by
    have ha : (tripleCharges (sourceA1068 + difference 5 1) (sourceB1068 + difference 1 5) sourceC1068) = raw17660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17660; decide +kernel
    rw [ha]
    exact (canonical17660 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1068 + difference 5 2) (sourceB1068 + difference 2 5) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA1068 + difference 5 2) (sourceB1068 + difference 2 5) sourceC1068) = raw17661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17661; decide +kernel
    rw [ha]
    exact (canonical17661 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1068 + difference 5 3) (sourceB1068 + difference 3 5) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA1068 + difference 5 3) (sourceB1068 + difference 3 5) sourceC1068) = raw17662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17662; decide +kernel
    rw [ha]
    exact (canonical17662 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1068 + difference 5 4) (sourceB1068 + difference 4 5) sourceC1068) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA1068 + difference 5 4) (sourceB1068 + difference 4 5) sourceC1068) = raw17416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1068 sourceB1068 sourceC1068 difference raw17416; decide +kernel
    rw [ha]
    exact (canonical17416 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1068 sourceB1068 sourceC1068
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1068, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1069 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1069 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1069 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm1069 : Integer.Sparse Master := [(Sum.inr 4096, 1), (Sum.inr 5169, 4), (Sum.inr 5171, 1), (Sum.inr 5177, 2), (Sum.inr 5293, 2), (Sum.inr 5465, 4), (Sum.inr 5466, 1), (Sum.inr 5476, 2), (Sum.inr 5483, 4), (Sum.inr 5486, 4), (Sum.inr 5487, 2), (Sum.inr 5491, 1), (Sum.inr 5493, 2)]

theorem sourceEq1069 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1069 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1069 + difference 0 1) (sourceB1069 + difference 1 0) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA1069 + difference 0 1) (sourceB1069 + difference 1 0) sourceC1069) = raw17663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17663; decide +kernel
    rw [ha]
    exact (canonical17663 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1069 + difference 0 2) (sourceB1069 + difference 2 0) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1069 + difference 0 2) (sourceB1069 + difference 2 0) sourceC1069) = raw17664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17664; decide +kernel
    rw [ha]
    exact (canonical17664 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1069 + difference 0 3) (sourceB1069 + difference 3 0) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1069 + difference 0 3) (sourceB1069 + difference 3 0) sourceC1069) = raw17665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17665; decide +kernel
    rw [ha]
    exact (canonical17665 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1069 + difference 0 4) (sourceB1069 + difference 4 0) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA1069 + difference 0 4) (sourceB1069 + difference 4 0) sourceC1069) = raw2751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw2751; decide +kernel
    rw [ha]
    exact (canonical2751 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1069 + difference 0 5) (sourceB1069 + difference 5 0) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1069 + difference 0 5) (sourceB1069 + difference 5 0) sourceC1069) = raw17666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17666; decide +kernel
    rw [ha]
    exact (canonical17666 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1069 + difference 1 0) (sourceB1069 + difference 0 1) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1069 + difference 1 0) (sourceB1069 + difference 0 1) sourceC1069) = raw2771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw2771; decide +kernel
    rw [ha]
    exact (canonical2771 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1069 + difference 1 2) (sourceB1069 + difference 2 1) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1069 + difference 1 2) (sourceB1069 + difference 2 1) sourceC1069) = raw2773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw2773; decide +kernel
    rw [ha]
    exact (canonical2773 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1069 + difference 1 3) (sourceB1069 + difference 3 1) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1069 + difference 1 3) (sourceB1069 + difference 3 1) sourceC1069) = raw2774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw2774; decide +kernel
    rw [ha]
    exact (canonical2774 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1069 + difference 1 4) (sourceB1069 + difference 4 1) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1069 + difference 1 4) (sourceB1069 + difference 4 1) sourceC1069) = raw4922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw4922; decide +kernel
    rw [ha]
    exact (canonical4922 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1069 + difference 1 5) (sourceB1069 + difference 5 1) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA1069 + difference 1 5) (sourceB1069 + difference 5 1) sourceC1069) = raw2775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw2775; decide +kernel
    rw [ha]
    exact (canonical2775 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1069 + difference 2 0) (sourceB1069 + difference 0 2) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1069 + difference 2 0) (sourceB1069 + difference 0 2) sourceC1069) = raw17667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17667; decide +kernel
    rw [ha]
    exact (canonical17667 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1069 + difference 2 1) (sourceB1069 + difference 1 2) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA1069 + difference 2 1) (sourceB1069 + difference 1 2) sourceC1069) = raw17668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17668; decide +kernel
    rw [ha]
    exact (canonical17668 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1069 + difference 2 3) (sourceB1069 + difference 3 2) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5476) := by
    have ha : (tripleCharges (sourceA1069 + difference 2 3) (sourceB1069 + difference 3 2) sourceC1069) = raw17669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17669; decide +kernel
    rw [ha]
    exact (canonical17669 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1069 + difference 2 4) (sourceB1069 + difference 4 2) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1069 + difference 2 4) (sourceB1069 + difference 4 2) sourceC1069) = raw2762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw2762; decide +kernel
    rw [ha]
    exact (canonical2762 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1069 + difference 2 5) (sourceB1069 + difference 5 2) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1069 + difference 2 5) (sourceB1069 + difference 5 2) sourceC1069) = raw17670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17670; decide +kernel
    rw [ha]
    exact (canonical17670 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1069 + difference 3 0) (sourceB1069 + difference 0 3) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1069 + difference 3 0) (sourceB1069 + difference 0 3) sourceC1069) = raw17671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17671; decide +kernel
    rw [ha]
    exact (canonical17671 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1069 + difference 3 1) (sourceB1069 + difference 1 3) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA1069 + difference 3 1) (sourceB1069 + difference 1 3) sourceC1069) = raw17672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17672; decide +kernel
    rw [ha]
    exact (canonical17672 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1069 + difference 3 2) (sourceB1069 + difference 2 3) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5476) := by
    have ha : (tripleCharges (sourceA1069 + difference 3 2) (sourceB1069 + difference 2 3) sourceC1069) = raw17673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17673; decide +kernel
    rw [ha]
    exact (canonical17673 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1069 + difference 3 4) (sourceB1069 + difference 4 3) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1069 + difference 3 4) (sourceB1069 + difference 4 3) sourceC1069) = raw2767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw2767; decide +kernel
    rw [ha]
    exact (canonical2767 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1069 + difference 3 5) (sourceB1069 + difference 5 3) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1069 + difference 3 5) (sourceB1069 + difference 5 3) sourceC1069) = raw17674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17674; decide +kernel
    rw [ha]
    exact (canonical17674 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1069 + difference 4 0) (sourceB1069 + difference 0 4) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA1069 + difference 4 0) (sourceB1069 + difference 0 4) sourceC1069) = raw17675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17675; decide +kernel
    rw [ha]
    exact (canonical17675 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1069 + difference 4 1) (sourceB1069 + difference 1 4) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5466) := by
    have ha : (tripleCharges (sourceA1069 + difference 4 1) (sourceB1069 + difference 1 4) sourceC1069) = raw17676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17676; decide +kernel
    rw [ha]
    exact (canonical17676 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1069 + difference 4 2) (sourceB1069 + difference 2 4) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA1069 + difference 4 2) (sourceB1069 + difference 2 4) sourceC1069) = raw17677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17677; decide +kernel
    rw [ha]
    exact (canonical17677 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1069 + difference 4 3) (sourceB1069 + difference 3 4) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA1069 + difference 4 3) (sourceB1069 + difference 3 4) sourceC1069) = raw17678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17678; decide +kernel
    rw [ha]
    exact (canonical17678 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1069 + difference 4 5) (sourceB1069 + difference 5 4) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA1069 + difference 4 5) (sourceB1069 + difference 5 4) sourceC1069) = raw17679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17679; decide +kernel
    rw [ha]
    exact (canonical17679 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1069 + difference 5 0) (sourceB1069 + difference 0 5) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA1069 + difference 5 0) (sourceB1069 + difference 0 5) sourceC1069) = raw4936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw4936; decide +kernel
    rw [ha]
    exact (canonical4936 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1069 + difference 5 1) (sourceB1069 + difference 1 5) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA1069 + difference 5 1) (sourceB1069 + difference 1 5) sourceC1069) = raw17680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17680; decide +kernel
    rw [ha]
    exact (canonical17680 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1069 + difference 5 2) (sourceB1069 + difference 2 5) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1069 + difference 5 2) (sourceB1069 + difference 2 5) sourceC1069) = raw17681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17681; decide +kernel
    rw [ha]
    exact (canonical17681 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1069 + difference 5 3) (sourceB1069 + difference 3 5) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1069 + difference 5 3) (sourceB1069 + difference 3 5) sourceC1069) = raw17682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw17682; decide +kernel
    rw [ha]
    exact (canonical17682 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1069 + difference 5 4) (sourceB1069 + difference 4 5) sourceC1069) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1069 + difference 5 4) (sourceB1069 + difference 4 5) sourceC1069) = raw2777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1069 sourceB1069 sourceC1069 difference raw2777; decide +kernel
    rw [ha]
    exact (canonical2777 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1069 sourceB1069 sourceC1069
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1069, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1070 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1070 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1070 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm1070 : Integer.Sparse Master := [(Sum.inr 4093, 1), (Sum.inr 5169, 2), (Sum.inr 5172, 2), (Sum.inr 5174, 1), (Sum.inr 5176, 1), (Sum.inr 5177, 1), (Sum.inr 5294, 1), (Sum.inr 5309, 1), (Sum.inr 5388, 2), (Sum.inr 5390, 1), (Sum.inr 5416, 2), (Sum.inr 5418, 2), (Sum.inr 5434, 2), (Sum.inr 5440, 2), (Sum.inr 5442, 3), (Sum.inr 5451, 1), (Sum.inr 5455, 1), (Sum.inr 5485, 2), (Sum.inr 5492, 1), (Sum.inr 5493, 1)]

theorem sourceEq1070 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1070 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1070 + difference 0 1) (sourceB1070 + difference 1 0) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1070 + difference 0 1) (sourceB1070 + difference 1 0) sourceC1070) = raw17683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17683; decide +kernel
    rw [ha]
    exact (canonical17683 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1070 + difference 0 2) (sourceB1070 + difference 2 0) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1070 + difference 0 2) (sourceB1070 + difference 2 0) sourceC1070) = raw17684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17684; decide +kernel
    rw [ha]
    exact (canonical17684 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1070 + difference 0 3) (sourceB1070 + difference 3 0) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1070 + difference 0 3) (sourceB1070 + difference 3 0) sourceC1070) = raw17685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17685; decide +kernel
    rw [ha]
    exact (canonical17685 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1070 + difference 0 4) (sourceB1070 + difference 4 0) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA1070 + difference 0 4) (sourceB1070 + difference 4 0) sourceC1070) = raw17686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17686; decide +kernel
    rw [ha]
    exact (canonical17686 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1070 + difference 0 5) (sourceB1070 + difference 5 0) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA1070 + difference 0 5) (sourceB1070 + difference 5 0) sourceC1070) = raw3029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw3029; decide +kernel
    rw [ha]
    exact (canonical3029 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1070 + difference 1 0) (sourceB1070 + difference 0 1) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1070 + difference 1 0) (sourceB1070 + difference 0 1) sourceC1070) = raw3054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw3054; decide +kernel
    rw [ha]
    exact (canonical3054 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1070 + difference 1 2) (sourceB1070 + difference 2 1) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1070 + difference 1 2) (sourceB1070 + difference 2 1) sourceC1070) = raw3056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw3056; decide +kernel
    rw [ha]
    exact (canonical3056 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1070 + difference 1 3) (sourceB1070 + difference 3 1) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1070 + difference 1 3) (sourceB1070 + difference 3 1) sourceC1070) = raw3057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw3057; decide +kernel
    rw [ha]
    exact (canonical3057 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1070 + difference 1 4) (sourceB1070 + difference 4 1) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA1070 + difference 1 4) (sourceB1070 + difference 4 1) sourceC1070) = raw3058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw3058; decide +kernel
    rw [ha]
    exact (canonical3058 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1070 + difference 1 5) (sourceB1070 + difference 5 1) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1070 + difference 1 5) (sourceB1070 + difference 5 1) sourceC1070) = raw13573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw13573; decide +kernel
    rw [ha]
    exact (canonical13573 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1070 + difference 2 0) (sourceB1070 + difference 0 2) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA1070 + difference 2 0) (sourceB1070 + difference 0 2) sourceC1070) = raw17687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17687; decide +kernel
    rw [ha]
    exact (canonical17687 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1070 + difference 2 1) (sourceB1070 + difference 1 2) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA1070 + difference 2 1) (sourceB1070 + difference 1 2) sourceC1070) = raw17688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17688; decide +kernel
    rw [ha]
    exact (canonical17688 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1070 + difference 2 3) (sourceB1070 + difference 3 2) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA1070 + difference 2 3) (sourceB1070 + difference 3 2) sourceC1070) = raw17689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17689; decide +kernel
    rw [ha]
    exact (canonical17689 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1070 + difference 2 4) (sourceB1070 + difference 4 2) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1070 + difference 2 4) (sourceB1070 + difference 4 2) sourceC1070) = raw17690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17690; decide +kernel
    rw [ha]
    exact (canonical17690 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1070 + difference 2 5) (sourceB1070 + difference 5 2) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1070 + difference 2 5) (sourceB1070 + difference 5 2) sourceC1070) = raw3040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw3040; decide +kernel
    rw [ha]
    exact (canonical3040 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1070 + difference 3 0) (sourceB1070 + difference 0 3) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA1070 + difference 3 0) (sourceB1070 + difference 0 3) sourceC1070) = raw13592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw13592; decide +kernel
    rw [ha]
    exact (canonical13592 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1070 + difference 3 1) (sourceB1070 + difference 1 3) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA1070 + difference 3 1) (sourceB1070 + difference 1 3) sourceC1070) = raw17691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17691; decide +kernel
    rw [ha]
    exact (canonical17691 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1070 + difference 3 2) (sourceB1070 + difference 2 3) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA1070 + difference 3 2) (sourceB1070 + difference 2 3) sourceC1070) = raw17692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17692; decide +kernel
    rw [ha]
    exact (canonical17692 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1070 + difference 3 4) (sourceB1070 + difference 4 3) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1070 + difference 3 4) (sourceB1070 + difference 4 3) sourceC1070) = raw17693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17693; decide +kernel
    rw [ha]
    exact (canonical17693 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1070 + difference 3 5) (sourceB1070 + difference 5 3) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1070 + difference 3 5) (sourceB1070 + difference 5 3) sourceC1070) = raw3045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw3045; decide +kernel
    rw [ha]
    exact (canonical3045 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1070 + difference 4 0) (sourceB1070 + difference 0 4) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA1070 + difference 4 0) (sourceB1070 + difference 0 4) sourceC1070) = raw17694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17694; decide +kernel
    rw [ha]
    exact (canonical17694 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1070 + difference 4 1) (sourceB1070 + difference 1 4) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA1070 + difference 4 1) (sourceB1070 + difference 1 4) sourceC1070) = raw17695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17695; decide +kernel
    rw [ha]
    exact (canonical17695 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1070 + difference 4 2) (sourceB1070 + difference 2 4) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA1070 + difference 4 2) (sourceB1070 + difference 2 4) sourceC1070) = raw17696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17696; decide +kernel
    rw [ha]
    exact (canonical17696 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1070 + difference 4 3) (sourceB1070 + difference 3 4) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA1070 + difference 4 3) (sourceB1070 + difference 3 4) sourceC1070) = raw17697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17697; decide +kernel
    rw [ha]
    exact (canonical17697 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1070 + difference 4 5) (sourceB1070 + difference 5 4) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1070 + difference 4 5) (sourceB1070 + difference 5 4) sourceC1070) = raw3050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw3050; decide +kernel
    rw [ha]
    exact (canonical3050 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1070 + difference 5 0) (sourceB1070 + difference 0 5) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1070 + difference 5 0) (sourceB1070 + difference 0 5) sourceC1070) = raw17698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17698; decide +kernel
    rw [ha]
    exact (canonical17698 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1070 + difference 5 1) (sourceB1070 + difference 1 5) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA1070 + difference 5 1) (sourceB1070 + difference 1 5) sourceC1070) = raw17699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17699; decide +kernel
    rw [ha]
    exact (canonical17699 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1070 + difference 5 2) (sourceB1070 + difference 2 5) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1070 + difference 5 2) (sourceB1070 + difference 2 5) sourceC1070) = raw17700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17700; decide +kernel
    rw [ha]
    exact (canonical17700 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1070 + difference 5 3) (sourceB1070 + difference 3 5) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1070 + difference 5 3) (sourceB1070 + difference 3 5) sourceC1070) = raw17701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17701; decide +kernel
    rw [ha]
    exact (canonical17701 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1070 + difference 5 4) (sourceB1070 + difference 4 5) sourceC1070) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA1070 + difference 5 4) (sourceB1070 + difference 4 5) sourceC1070) = raw17702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1070 sourceB1070 sourceC1070 difference raw17702; decide +kernel
    rw [ha]
    exact (canonical17702 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1070 sourceB1070 sourceC1070
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1070, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1071 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1071 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1071 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm1071 : Integer.Sparse Master := [(Sum.inr 5145, 1), (Sum.inr 5147, 1), (Sum.inr 5152, 1), (Sum.inr 5164, 1), (Sum.inr 5185, 1), (Sum.inr 5189, 1), (Sum.inr 5203, 1), (Sum.inr 5266, 1), (Sum.inr 5282, 1), (Sum.inr 5352, 1), (Sum.inr 5356, 1), (Sum.inr 5369, 1), (Sum.inr 5410, 1), (Sum.inr 5445, 1), (Sum.inr 5446, 1), (Sum.inr 5448, 1), (Sum.inr 5450, 1), (Sum.inr 5459, 1), (Sum.inr 5463, 1), (Sum.inr 5469, 1), (Sum.inr 5470, 1), (Sum.inr 5471, 1), (Sum.inr 5472, 1), (Sum.inr 5473, 2), (Sum.inr 5474, 1), (Sum.inr 5478, 1), (Sum.inr 5484, 1), (Sum.inr 5485, 1), (Sum.inr 5486, 1)]

theorem sourceEq1071 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1071 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1071 + difference 0 1) (sourceB1071 + difference 1 0) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1071 + difference 0 1) (sourceB1071 + difference 1 0) sourceC1071) = raw17703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17703; decide +kernel
    rw [ha]
    exact (canonical17703 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1071 + difference 0 2) (sourceB1071 + difference 2 0) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1071 + difference 0 2) (sourceB1071 + difference 2 0) sourceC1071) = raw17704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17704; decide +kernel
    rw [ha]
    exact (canonical17704 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1071 + difference 0 3) (sourceB1071 + difference 3 0) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5474) := by
    have ha : (tripleCharges (sourceA1071 + difference 0 3) (sourceB1071 + difference 3 0) sourceC1071) = raw17705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17705; decide +kernel
    rw [ha]
    exact (canonical17705 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1071 + difference 0 4) (sourceB1071 + difference 4 0) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1071 + difference 0 4) (sourceB1071 + difference 4 0) sourceC1071) = raw17706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17706; decide +kernel
    rw [ha]
    exact (canonical17706 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1071 + difference 0 5) (sourceB1071 + difference 5 0) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1071 + difference 0 5) (sourceB1071 + difference 5 0) sourceC1071) = raw17707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17707; decide +kernel
    rw [ha]
    exact (canonical17707 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1071 + difference 1 0) (sourceB1071 + difference 0 1) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA1071 + difference 1 0) (sourceB1071 + difference 0 1) sourceC1071) = raw17708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17708; decide +kernel
    rw [ha]
    exact (canonical17708 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1071 + difference 1 2) (sourceB1071 + difference 2 1) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1071 + difference 1 2) (sourceB1071 + difference 2 1) sourceC1071) = raw17709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17709; decide +kernel
    rw [ha]
    exact (canonical17709 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1071 + difference 1 3) (sourceB1071 + difference 3 1) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1071 + difference 1 3) (sourceB1071 + difference 3 1) sourceC1071) = raw17710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17710; decide +kernel
    rw [ha]
    exact (canonical17710 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1071 + difference 1 4) (sourceB1071 + difference 4 1) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1071 + difference 1 4) (sourceB1071 + difference 4 1) sourceC1071) = raw17711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17711; decide +kernel
    rw [ha]
    exact (canonical17711 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1071 + difference 1 5) (sourceB1071 + difference 5 1) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1071 + difference 1 5) (sourceB1071 + difference 5 1) sourceC1071) = raw17712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17712; decide +kernel
    rw [ha]
    exact (canonical17712 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1071 + difference 2 0) (sourceB1071 + difference 0 2) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA1071 + difference 2 0) (sourceB1071 + difference 0 2) sourceC1071) = raw17713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17713; decide +kernel
    rw [ha]
    exact (canonical17713 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1071 + difference 2 1) (sourceB1071 + difference 1 2) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5459) := by
    have ha : (tripleCharges (sourceA1071 + difference 2 1) (sourceB1071 + difference 1 2) sourceC1071) = raw17714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17714; decide +kernel
    rw [ha]
    exact (canonical17714 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1071 + difference 2 3) (sourceB1071 + difference 3 2) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1071 + difference 2 3) (sourceB1071 + difference 3 2) sourceC1071) = raw17715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17715; decide +kernel
    rw [ha]
    exact (canonical17715 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1071 + difference 2 4) (sourceB1071 + difference 4 2) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1071 + difference 2 4) (sourceB1071 + difference 4 2) sourceC1071) = raw17716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17716; decide +kernel
    rw [ha]
    exact (canonical17716 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1071 + difference 2 5) (sourceB1071 + difference 5 2) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1071 + difference 2 5) (sourceB1071 + difference 5 2) sourceC1071) = raw17717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17717; decide +kernel
    rw [ha]
    exact (canonical17717 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1071 + difference 3 0) (sourceB1071 + difference 0 3) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA1071 + difference 3 0) (sourceB1071 + difference 0 3) sourceC1071) = raw17718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17718; decide +kernel
    rw [ha]
    exact (canonical17718 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1071 + difference 3 1) (sourceB1071 + difference 1 3) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5463) := by
    have ha : (tripleCharges (sourceA1071 + difference 3 1) (sourceB1071 + difference 1 3) sourceC1071) = raw17719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17719; decide +kernel
    rw [ha]
    exact (canonical17719 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1071 + difference 3 2) (sourceB1071 + difference 2 3) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA1071 + difference 3 2) (sourceB1071 + difference 2 3) sourceC1071) = raw17720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17720; decide +kernel
    rw [ha]
    exact (canonical17720 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1071 + difference 3 4) (sourceB1071 + difference 4 3) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1071 + difference 3 4) (sourceB1071 + difference 4 3) sourceC1071) = raw17721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17721; decide +kernel
    rw [ha]
    exact (canonical17721 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1071 + difference 3 5) (sourceB1071 + difference 5 3) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1071 + difference 3 5) (sourceB1071 + difference 5 3) sourceC1071) = raw17722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17722; decide +kernel
    rw [ha]
    exact (canonical17722 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1071 + difference 4 0) (sourceB1071 + difference 0 4) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA1071 + difference 4 0) (sourceB1071 + difference 0 4) sourceC1071) = raw17723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17723; decide +kernel
    rw [ha]
    exact (canonical17723 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1071 + difference 4 1) (sourceB1071 + difference 1 4) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA1071 + difference 4 1) (sourceB1071 + difference 1 4) sourceC1071) = raw17724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17724; decide +kernel
    rw [ha]
    exact (canonical17724 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1071 + difference 4 2) (sourceB1071 + difference 2 4) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1071 + difference 4 2) (sourceB1071 + difference 2 4) sourceC1071) = raw17725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17725; decide +kernel
    rw [ha]
    exact (canonical17725 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1071 + difference 4 3) (sourceB1071 + difference 3 4) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA1071 + difference 4 3) (sourceB1071 + difference 3 4) sourceC1071) = raw17726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17726; decide +kernel
    rw [ha]
    exact (canonical17726 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1071 + difference 4 5) (sourceB1071 + difference 5 4) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1071 + difference 4 5) (sourceB1071 + difference 5 4) sourceC1071) = raw17727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17727; decide +kernel
    rw [ha]
    exact (canonical17727 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1071 + difference 5 0) (sourceB1071 + difference 0 5) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA1071 + difference 5 0) (sourceB1071 + difference 0 5) sourceC1071) = raw17728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17728; decide +kernel
    rw [ha]
    exact (canonical17728 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1071 + difference 5 1) (sourceB1071 + difference 1 5) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA1071 + difference 5 1) (sourceB1071 + difference 1 5) sourceC1071) = raw17729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17729; decide +kernel
    rw [ha]
    exact (canonical17729 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1071 + difference 5 2) (sourceB1071 + difference 2 5) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA1071 + difference 5 2) (sourceB1071 + difference 2 5) sourceC1071) = raw17730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17730; decide +kernel
    rw [ha]
    exact (canonical17730 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1071 + difference 5 3) (sourceB1071 + difference 3 5) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA1071 + difference 5 3) (sourceB1071 + difference 3 5) sourceC1071) = raw17731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17731; decide +kernel
    rw [ha]
    exact (canonical17731 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1071 + difference 5 4) (sourceB1071 + difference 4 5) sourceC1071) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA1071 + difference 5 4) (sourceB1071 + difference 4 5) sourceC1071) = raw17732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1071 sourceB1071 sourceC1071 difference raw17732; decide +kernel
    rw [ha]
    exact (canonical17732 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1071 sourceB1071 sourceC1071
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1071, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1072 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1072 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1072 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm1072 : Integer.Sparse Master := [(Sum.inr 3529, 1), (Sum.inr 3530, 1), (Sum.inr 3535, 1), (Sum.inr 3542, 1), (Sum.inr 3562, 1), (Sum.inr 3565, 1), (Sum.inr 3580, 1), (Sum.inr 3612, 1), (Sum.inr 3621, 1), (Sum.inr 3764, 1), (Sum.inr 3773, 1), (Sum.inr 3774, 1), (Sum.inr 3816, 1), (Sum.inr 3951, 1), (Sum.inr 3952, 1), (Sum.inr 3955, 1), (Sum.inr 3956, 1), (Sum.inr 3957, 1), (Sum.inr 3959, 1), (Sum.inr 3960, 1), (Sum.inr 3961, 2), (Sum.inr 3962, 1), (Sum.inr 3974, 1), (Sum.inr 3983, 1), (Sum.inr 3984, 1), (Sum.inr 3985, 1), (Sum.inr 4024, 1), (Sum.inr 4028, 1), (Sum.inr 4029, 1)]

theorem sourceEq1072 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1072 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1072 + difference 0 1) (sourceB1072 + difference 1 0) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA1072 + difference 0 1) (sourceB1072 + difference 1 0) sourceC1072) = raw17733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17733; decide +kernel
    rw [ha]
    exact (canonical17733 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1072 + difference 0 2) (sourceB1072 + difference 2 0) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA1072 + difference 0 2) (sourceB1072 + difference 2 0) sourceC1072) = raw17734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17734; decide +kernel
    rw [ha]
    exact (canonical17734 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1072 + difference 0 3) (sourceB1072 + difference 3 0) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3962) := by
    have ha : (tripleCharges (sourceA1072 + difference 0 3) (sourceB1072 + difference 3 0) sourceC1072) = raw17735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17735; decide +kernel
    rw [ha]
    exact (canonical17735 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1072 + difference 0 4) (sourceB1072 + difference 4 0) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA1072 + difference 0 4) (sourceB1072 + difference 4 0) sourceC1072) = raw17736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17736; decide +kernel
    rw [ha]
    exact (canonical17736 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1072 + difference 0 5) (sourceB1072 + difference 5 0) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3985) := by
    have ha : (tripleCharges (sourceA1072 + difference 0 5) (sourceB1072 + difference 5 0) sourceC1072) = raw17737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17737; decide +kernel
    rw [ha]
    exact (canonical17737 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1072 + difference 1 0) (sourceB1072 + difference 0 1) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA1072 + difference 1 0) (sourceB1072 + difference 0 1) sourceC1072) = raw17738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17738; decide +kernel
    rw [ha]
    exact (canonical17738 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1072 + difference 1 2) (sourceB1072 + difference 2 1) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA1072 + difference 1 2) (sourceB1072 + difference 2 1) sourceC1072) = raw17739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17739; decide +kernel
    rw [ha]
    exact (canonical17739 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1072 + difference 1 3) (sourceB1072 + difference 3 1) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA1072 + difference 1 3) (sourceB1072 + difference 3 1) sourceC1072) = raw17740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17740; decide +kernel
    rw [ha]
    exact (canonical17740 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1072 + difference 1 4) (sourceB1072 + difference 4 1) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4028) := by
    have ha : (tripleCharges (sourceA1072 + difference 1 4) (sourceB1072 + difference 4 1) sourceC1072) = raw17741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17741; decide +kernel
    rw [ha]
    exact (canonical17741 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1072 + difference 1 5) (sourceB1072 + difference 5 1) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA1072 + difference 1 5) (sourceB1072 + difference 5 1) sourceC1072) = raw17742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17742; decide +kernel
    rw [ha]
    exact (canonical17742 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1072 + difference 2 0) (sourceB1072 + difference 0 2) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA1072 + difference 2 0) (sourceB1072 + difference 0 2) sourceC1072) = raw17743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17743; decide +kernel
    rw [ha]
    exact (canonical17743 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1072 + difference 2 1) (sourceB1072 + difference 1 2) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3951) := by
    have ha : (tripleCharges (sourceA1072 + difference 2 1) (sourceB1072 + difference 1 2) sourceC1072) = raw17744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17744; decide +kernel
    rw [ha]
    exact (canonical17744 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1072 + difference 2 3) (sourceB1072 + difference 3 2) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3952) := by
    have ha : (tripleCharges (sourceA1072 + difference 2 3) (sourceB1072 + difference 3 2) sourceC1072) = raw17745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17745; decide +kernel
    rw [ha]
    exact (canonical17745 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1072 + difference 2 4) (sourceB1072 + difference 4 2) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA1072 + difference 2 4) (sourceB1072 + difference 4 2) sourceC1072) = raw17746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17746; decide +kernel
    rw [ha]
    exact (canonical17746 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1072 + difference 2 5) (sourceB1072 + difference 5 2) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA1072 + difference 2 5) (sourceB1072 + difference 5 2) sourceC1072) = raw17747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17747; decide +kernel
    rw [ha]
    exact (canonical17747 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1072 + difference 3 0) (sourceB1072 + difference 0 3) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA1072 + difference 3 0) (sourceB1072 + difference 0 3) sourceC1072) = raw17748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17748; decide +kernel
    rw [ha]
    exact (canonical17748 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1072 + difference 3 1) (sourceB1072 + difference 1 3) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3960) := by
    have ha : (tripleCharges (sourceA1072 + difference 3 1) (sourceB1072 + difference 1 3) sourceC1072) = raw17749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17749; decide +kernel
    rw [ha]
    exact (canonical17749 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1072 + difference 3 2) (sourceB1072 + difference 2 3) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3955) := by
    have ha : (tripleCharges (sourceA1072 + difference 3 2) (sourceB1072 + difference 2 3) sourceC1072) = raw17750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17750; decide +kernel
    rw [ha]
    exact (canonical17750 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1072 + difference 3 4) (sourceB1072 + difference 4 3) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1072 + difference 3 4) (sourceB1072 + difference 4 3) sourceC1072) = raw17751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17751; decide +kernel
    rw [ha]
    exact (canonical17751 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1072 + difference 3 5) (sourceB1072 + difference 5 3) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA1072 + difference 3 5) (sourceB1072 + difference 5 3) sourceC1072) = raw17752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17752; decide +kernel
    rw [ha]
    exact (canonical17752 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1072 + difference 4 0) (sourceB1072 + difference 0 4) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA1072 + difference 4 0) (sourceB1072 + difference 0 4) sourceC1072) = raw17753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17753; decide +kernel
    rw [ha]
    exact (canonical17753 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1072 + difference 4 1) (sourceB1072 + difference 1 4) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3773) := by
    have ha : (tripleCharges (sourceA1072 + difference 4 1) (sourceB1072 + difference 1 4) sourceC1072) = raw17754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17754; decide +kernel
    rw [ha]
    exact (canonical17754 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1072 + difference 4 2) (sourceB1072 + difference 2 4) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA1072 + difference 4 2) (sourceB1072 + difference 2 4) sourceC1072) = raw17755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17755; decide +kernel
    rw [ha]
    exact (canonical17755 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1072 + difference 4 3) (sourceB1072 + difference 3 4) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3774) := by
    have ha : (tripleCharges (sourceA1072 + difference 4 3) (sourceB1072 + difference 3 4) sourceC1072) = raw17756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17756; decide +kernel
    rw [ha]
    exact (canonical17756 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1072 + difference 4 5) (sourceB1072 + difference 5 4) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA1072 + difference 4 5) (sourceB1072 + difference 5 4) sourceC1072) = raw17757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17757; decide +kernel
    rw [ha]
    exact (canonical17757 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1072 + difference 5 0) (sourceB1072 + difference 0 5) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA1072 + difference 5 0) (sourceB1072 + difference 0 5) sourceC1072) = raw17758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17758; decide +kernel
    rw [ha]
    exact (canonical17758 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1072 + difference 5 1) (sourceB1072 + difference 1 5) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA1072 + difference 5 1) (sourceB1072 + difference 1 5) sourceC1072) = raw17759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17759; decide +kernel
    rw [ha]
    exact (canonical17759 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1072 + difference 5 2) (sourceB1072 + difference 2 5) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA1072 + difference 5 2) (sourceB1072 + difference 2 5) sourceC1072) = raw17760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17760; decide +kernel
    rw [ha]
    exact (canonical17760 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1072 + difference 5 3) (sourceB1072 + difference 3 5) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3621) := by
    have ha : (tripleCharges (sourceA1072 + difference 5 3) (sourceB1072 + difference 3 5) sourceC1072) = raw17761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17761; decide +kernel
    rw [ha]
    exact (canonical17761 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1072 + difference 5 4) (sourceB1072 + difference 4 5) sourceC1072) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA1072 + difference 5 4) (sourceB1072 + difference 4 5) sourceC1072) = raw17762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1072 sourceB1072 sourceC1072 difference raw17762; decide +kernel
    rw [ha]
    exact (canonical17762 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1072 sourceB1072 sourceC1072
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1072, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1073 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1073 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1073 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceForm1073 : Integer.Sparse Master := [(Sum.inr 4998, 1), (Sum.inr 5000, 1), (Sum.inr 5003, 1), (Sum.inr 5013, 1), (Sum.inr 5014, 1), (Sum.inr 5015, 1), (Sum.inr 5018, 2), (Sum.inr 5059, 1), (Sum.inr 5102, 1), (Sum.inr 5259, 1), (Sum.inr 5271, 1), (Sum.inr 5275, 1), (Sum.inr 5346, 1), (Sum.inr 5368, 1), (Sum.inr 5428, 1), (Sum.inr 5467, 1), (Sum.inr 5469, 1), (Sum.inr 5472, 1), (Sum.inr 5473, 2), (Sum.inr 5475, 1), (Sum.inr 5477, 1), (Sum.inr 5478, 1), (Sum.inr 5483, 1), (Sum.inr 5485, 1), (Sum.inr 5490, 2), (Sum.inr 5491, 1), (Sum.inr 5492, 1)]

theorem sourceEq1073 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1073 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1073 + difference 0 1) (sourceB1073 + difference 1 0) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1073 + difference 0 1) (sourceB1073 + difference 1 0) sourceC1073) = raw17763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17763; decide +kernel
    rw [ha]
    exact (canonical17763 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1073 + difference 0 2) (sourceB1073 + difference 2 0) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1073 + difference 0 2) (sourceB1073 + difference 2 0) sourceC1073) = raw17764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17764; decide +kernel
    rw [ha]
    exact (canonical17764 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1073 + difference 0 3) (sourceB1073 + difference 3 0) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1073 + difference 0 3) (sourceB1073 + difference 3 0) sourceC1073) = raw17765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17765; decide +kernel
    rw [ha]
    exact (canonical17765 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1073 + difference 0 4) (sourceB1073 + difference 4 0) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1073 + difference 0 4) (sourceB1073 + difference 4 0) sourceC1073) = raw17766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17766; decide +kernel
    rw [ha]
    exact (canonical17766 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1073 + difference 0 5) (sourceB1073 + difference 5 0) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1073 + difference 0 5) (sourceB1073 + difference 5 0) sourceC1073) = raw17767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17767; decide +kernel
    rw [ha]
    exact (canonical17767 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1073 + difference 1 0) (sourceB1073 + difference 0 1) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA1073 + difference 1 0) (sourceB1073 + difference 0 1) sourceC1073) = raw17768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17768; decide +kernel
    rw [ha]
    exact (canonical17768 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1073 + difference 1 2) (sourceB1073 + difference 2 1) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1073 + difference 1 2) (sourceB1073 + difference 2 1) sourceC1073) = raw10451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10451; decide +kernel
    rw [ha]
    exact (canonical10451 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1073 + difference 1 3) (sourceB1073 + difference 3 1) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5475) := by
    have ha : (tripleCharges (sourceA1073 + difference 1 3) (sourceB1073 + difference 3 1) sourceC1073) = raw10452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10452; decide +kernel
    rw [ha]
    exact (canonical10452 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1073 + difference 1 4) (sourceB1073 + difference 4 1) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1073 + difference 1 4) (sourceB1073 + difference 4 1) sourceC1073) = raw10453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10453; decide +kernel
    rw [ha]
    exact (canonical10453 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1073 + difference 1 5) (sourceB1073 + difference 5 1) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1073 + difference 1 5) (sourceB1073 + difference 5 1) sourceC1073) = raw10454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10454; decide +kernel
    rw [ha]
    exact (canonical10454 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1073 + difference 2 0) (sourceB1073 + difference 0 2) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA1073 + difference 2 0) (sourceB1073 + difference 0 2) sourceC1073) = raw10461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10461; decide +kernel
    rw [ha]
    exact (canonical10461 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1073 + difference 2 1) (sourceB1073 + difference 1 2) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA1073 + difference 2 1) (sourceB1073 + difference 1 2) sourceC1073) = raw17769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17769; decide +kernel
    rw [ha]
    exact (canonical17769 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1073 + difference 2 3) (sourceB1073 + difference 3 2) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5467) := by
    have ha : (tripleCharges (sourceA1073 + difference 2 3) (sourceB1073 + difference 3 2) sourceC1073) = raw17770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17770; decide +kernel
    rw [ha]
    exact (canonical17770 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1073 + difference 2 4) (sourceB1073 + difference 4 2) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1073 + difference 2 4) (sourceB1073 + difference 4 2) sourceC1073) = raw17771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17771; decide +kernel
    rw [ha]
    exact (canonical17771 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1073 + difference 2 5) (sourceB1073 + difference 5 2) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1073 + difference 2 5) (sourceB1073 + difference 5 2) sourceC1073) = raw17772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17772; decide +kernel
    rw [ha]
    exact (canonical17772 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1073 + difference 3 0) (sourceB1073 + difference 0 3) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA1073 + difference 3 0) (sourceB1073 + difference 0 3) sourceC1073) = raw10466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10466; decide +kernel
    rw [ha]
    exact (canonical10466 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1073 + difference 3 1) (sourceB1073 + difference 1 3) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1073 + difference 3 1) (sourceB1073 + difference 1 3) sourceC1073) = raw17773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17773; decide +kernel
    rw [ha]
    exact (canonical17773 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1073 + difference 3 2) (sourceB1073 + difference 2 3) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1073 + difference 3 2) (sourceB1073 + difference 2 3) sourceC1073) = raw17774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17774; decide +kernel
    rw [ha]
    exact (canonical17774 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1073 + difference 3 4) (sourceB1073 + difference 4 3) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1073 + difference 3 4) (sourceB1073 + difference 4 3) sourceC1073) = raw17775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17775; decide +kernel
    rw [ha]
    exact (canonical17775 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1073 + difference 3 5) (sourceB1073 + difference 5 3) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1073 + difference 3 5) (sourceB1073 + difference 5 3) sourceC1073) = raw17776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17776; decide +kernel
    rw [ha]
    exact (canonical17776 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1073 + difference 4 0) (sourceB1073 + difference 0 4) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA1073 + difference 4 0) (sourceB1073 + difference 0 4) sourceC1073) = raw10471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10471; decide +kernel
    rw [ha]
    exact (canonical10471 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1073 + difference 4 1) (sourceB1073 + difference 1 4) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA1073 + difference 4 1) (sourceB1073 + difference 1 4) sourceC1073) = raw17777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17777; decide +kernel
    rw [ha]
    exact (canonical17777 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1073 + difference 4 2) (sourceB1073 + difference 2 4) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5013) := by
    have ha : (tripleCharges (sourceA1073 + difference 4 2) (sourceB1073 + difference 2 4) sourceC1073) = raw17778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17778; decide +kernel
    rw [ha]
    exact (canonical17778 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1073 + difference 4 3) (sourceB1073 + difference 3 4) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA1073 + difference 4 3) (sourceB1073 + difference 3 4) sourceC1073) = raw17779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17779; decide +kernel
    rw [ha]
    exact (canonical17779 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1073 + difference 4 5) (sourceB1073 + difference 5 4) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA1073 + difference 4 5) (sourceB1073 + difference 5 4) sourceC1073) = raw17780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17780; decide +kernel
    rw [ha]
    exact (canonical17780 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1073 + difference 5 0) (sourceB1073 + difference 0 5) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA1073 + difference 5 0) (sourceB1073 + difference 0 5) sourceC1073) = raw10476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10476; decide +kernel
    rw [ha]
    exact (canonical10476 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1073 + difference 5 1) (sourceB1073 + difference 1 5) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA1073 + difference 5 1) (sourceB1073 + difference 1 5) sourceC1073) = raw17781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17781; decide +kernel
    rw [ha]
    exact (canonical17781 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1073 + difference 5 2) (sourceB1073 + difference 2 5) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA1073 + difference 5 2) (sourceB1073 + difference 2 5) sourceC1073) = raw17782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17782; decide +kernel
    rw [ha]
    exact (canonical17782 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1073 + difference 5 3) (sourceB1073 + difference 3 5) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA1073 + difference 5 3) (sourceB1073 + difference 3 5) sourceC1073) = raw17783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17783; decide +kernel
    rw [ha]
    exact (canonical17783 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1073 + difference 5 4) (sourceB1073 + difference 4 5) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA1073 + difference 5 4) (sourceB1073 + difference 4 5) sourceC1073) = raw17784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17784; decide +kernel
    rw [ha]
    exact (canonical17784 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1073 sourceB1073 sourceC1073
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1073, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1074 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1074 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1074 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceForm1074 : Integer.Sparse Master := [(Sum.inr 2383, 1), (Sum.inr 2385, 1), (Sum.inr 2388, 1), (Sum.inr 2404, 1), (Sum.inr 2462, 1), (Sum.inr 2467, 1), (Sum.inr 2512, 1), (Sum.inr 2723, 1), (Sum.inr 2743, 1), (Sum.inr 3341, 1), (Sum.inr 3344, 1), (Sum.inr 3357, 1), (Sum.inr 3534, 1), (Sum.inr 3683, 1), (Sum.inr 3705, 1), (Sum.inr 3845, 1), (Sum.inr 3942, 1), (Sum.inr 3945, 1), (Sum.inr 3957, 1), (Sum.inr 3958, 1), (Sum.inr 3961, 1), (Sum.inr 3963, 1), (Sum.inr 3971, 1), (Sum.inr 3974, 1), (Sum.inr 3981, 1), (Sum.inr 3984, 1), (Sum.inr 4013, 1), (Sum.inr 4014, 1), (Sum.inr 4015, 1), (Sum.inr 4050, 1)]

theorem sourceEq1074 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1074 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1074 + difference 0 1) (sourceB1074 + difference 1 0) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA1074 + difference 0 1) (sourceB1074 + difference 1 0) sourceC1074) = raw17785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17785; decide +kernel
    rw [ha]
    exact (canonical17785 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1074 + difference 0 2) (sourceB1074 + difference 2 0) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA1074 + difference 0 2) (sourceB1074 + difference 2 0) sourceC1074) = raw17786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17786; decide +kernel
    rw [ha]
    exact (canonical17786 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1074 + difference 0 3) (sourceB1074 + difference 3 0) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA1074 + difference 0 3) (sourceB1074 + difference 3 0) sourceC1074) = raw17787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17787; decide +kernel
    rw [ha]
    exact (canonical17787 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1074 + difference 0 4) (sourceB1074 + difference 4 0) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA1074 + difference 0 4) (sourceB1074 + difference 4 0) sourceC1074) = raw17788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17788; decide +kernel
    rw [ha]
    exact (canonical17788 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1074 + difference 0 5) (sourceB1074 + difference 5 0) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4050) := by
    have ha : (tripleCharges (sourceA1074 + difference 0 5) (sourceB1074 + difference 5 0) sourceC1074) = raw17789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17789; decide +kernel
    rw [ha]
    exact (canonical17789 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1074 + difference 1 0) (sourceB1074 + difference 0 1) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA1074 + difference 1 0) (sourceB1074 + difference 0 1) sourceC1074) = raw17790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17790; decide +kernel
    rw [ha]
    exact (canonical17790 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1074 + difference 1 2) (sourceB1074 + difference 2 1) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1074 + difference 1 2) (sourceB1074 + difference 2 1) sourceC1074) = raw10481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw10481; decide +kernel
    rw [ha]
    exact (canonical10481 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1074 + difference 1 3) (sourceB1074 + difference 3 1) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA1074 + difference 1 3) (sourceB1074 + difference 3 1) sourceC1074) = raw10482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw10482; decide +kernel
    rw [ha]
    exact (canonical10482 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1074 + difference 1 4) (sourceB1074 + difference 4 1) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4014) := by
    have ha : (tripleCharges (sourceA1074 + difference 1 4) (sourceB1074 + difference 4 1) sourceC1074) = raw10483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw10483; decide +kernel
    rw [ha]
    exact (canonical10483 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1074 + difference 1 5) (sourceB1074 + difference 5 1) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4015) := by
    have ha : (tripleCharges (sourceA1074 + difference 1 5) (sourceB1074 + difference 5 1) sourceC1074) = raw10484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw10484; decide +kernel
    rw [ha]
    exact (canonical10484 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1074 + difference 2 0) (sourceB1074 + difference 0 2) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA1074 + difference 2 0) (sourceB1074 + difference 0 2) sourceC1074) = raw10491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw10491; decide +kernel
    rw [ha]
    exact (canonical10491 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1074 + difference 2 1) (sourceB1074 + difference 1 2) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3683) := by
    have ha : (tripleCharges (sourceA1074 + difference 2 1) (sourceB1074 + difference 1 2) sourceC1074) = raw17791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17791; decide +kernel
    rw [ha]
    exact (canonical17791 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1074 + difference 2 3) (sourceB1074 + difference 3 2) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3942) := by
    have ha : (tripleCharges (sourceA1074 + difference 2 3) (sourceB1074 + difference 3 2) sourceC1074) = raw17792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17792; decide +kernel
    rw [ha]
    exact (canonical17792 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1074 + difference 2 4) (sourceB1074 + difference 4 2) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3971) := by
    have ha : (tripleCharges (sourceA1074 + difference 2 4) (sourceB1074 + difference 4 2) sourceC1074) = raw17793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17793; decide +kernel
    rw [ha]
    exact (canonical17793 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1074 + difference 2 5) (sourceB1074 + difference 5 2) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA1074 + difference 2 5) (sourceB1074 + difference 5 2) sourceC1074) = raw17794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17794; decide +kernel
    rw [ha]
    exact (canonical17794 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1074 + difference 3 0) (sourceB1074 + difference 0 3) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA1074 + difference 3 0) (sourceB1074 + difference 0 3) sourceC1074) = raw10496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw10496; decide +kernel
    rw [ha]
    exact (canonical10496 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1074 + difference 3 1) (sourceB1074 + difference 1 3) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3705) := by
    have ha : (tripleCharges (sourceA1074 + difference 3 1) (sourceB1074 + difference 1 3) sourceC1074) = raw17795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17795; decide +kernel
    rw [ha]
    exact (canonical17795 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1074 + difference 3 2) (sourceB1074 + difference 2 3) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3945) := by
    have ha : (tripleCharges (sourceA1074 + difference 3 2) (sourceB1074 + difference 2 3) sourceC1074) = raw17796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17796; decide +kernel
    rw [ha]
    exact (canonical17796 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1074 + difference 3 4) (sourceB1074 + difference 4 3) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1074 + difference 3 4) (sourceB1074 + difference 4 3) sourceC1074) = raw17797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17797; decide +kernel
    rw [ha]
    exact (canonical17797 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1074 + difference 3 5) (sourceB1074 + difference 5 3) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA1074 + difference 3 5) (sourceB1074 + difference 5 3) sourceC1074) = raw17798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17798; decide +kernel
    rw [ha]
    exact (canonical17798 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1074 + difference 4 0) (sourceB1074 + difference 0 4) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2467) := by
    have ha : (tripleCharges (sourceA1074 + difference 4 0) (sourceB1074 + difference 0 4) sourceC1074) = raw10501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw10501; decide +kernel
    rw [ha]
    exact (canonical10501 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1074 + difference 4 1) (sourceB1074 + difference 1 4) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3344) := by
    have ha : (tripleCharges (sourceA1074 + difference 4 1) (sourceB1074 + difference 1 4) sourceC1074) = raw17799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17799; decide +kernel
    rw [ha]
    exact (canonical17799 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1074 + difference 4 2) (sourceB1074 + difference 2 4) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3341) := by
    have ha : (tripleCharges (sourceA1074 + difference 4 2) (sourceB1074 + difference 2 4) sourceC1074) = raw17800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17800; decide +kernel
    rw [ha]
    exact (canonical17800 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1074 + difference 4 3) (sourceB1074 + difference 3 4) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3357) := by
    have ha : (tripleCharges (sourceA1074 + difference 4 3) (sourceB1074 + difference 3 4) sourceC1074) = raw17801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17801; decide +kernel
    rw [ha]
    exact (canonical17801 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1074 + difference 4 5) (sourceB1074 + difference 5 4) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA1074 + difference 4 5) (sourceB1074 + difference 5 4) sourceC1074) = raw17802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17802; decide +kernel
    rw [ha]
    exact (canonical17802 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1074 + difference 5 0) (sourceB1074 + difference 0 5) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA1074 + difference 5 0) (sourceB1074 + difference 0 5) sourceC1074) = raw10506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw10506; decide +kernel
    rw [ha]
    exact (canonical10506 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1074 + difference 5 1) (sourceB1074 + difference 1 5) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2388) := by
    have ha : (tripleCharges (sourceA1074 + difference 5 1) (sourceB1074 + difference 1 5) sourceC1074) = raw17803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17803; decide +kernel
    rw [ha]
    exact (canonical17803 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1074 + difference 5 2) (sourceB1074 + difference 2 5) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2383) := by
    have ha : (tripleCharges (sourceA1074 + difference 5 2) (sourceB1074 + difference 2 5) sourceC1074) = raw17804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17804; decide +kernel
    rw [ha]
    exact (canonical17804 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1074 + difference 5 3) (sourceB1074 + difference 3 5) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2404) := by
    have ha : (tripleCharges (sourceA1074 + difference 5 3) (sourceB1074 + difference 3 5) sourceC1074) = raw17805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17805; decide +kernel
    rw [ha]
    exact (canonical17805 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1074 + difference 5 4) (sourceB1074 + difference 4 5) sourceC1074) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA1074 + difference 5 4) (sourceB1074 + difference 4 5) sourceC1074) = raw17806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1074 sourceB1074 sourceC1074 difference raw17806; decide +kernel
    rw [ha]
    exact (canonical17806 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1074 sourceB1074 sourceC1074
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1074, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1075 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB1075 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1075 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1075 : Integer.Sparse Master := [(Sum.inr 5197, 1), (Sum.inr 5198, 1), (Sum.inr 5199, 1), (Sum.inr 5204, 1), (Sum.inr 5299, 1), (Sum.inr 5365, 1), (Sum.inr 5367, 1), (Sum.inr 5368, 1), (Sum.inr 5370, 1), (Sum.inr 5395, 1), (Sum.inr 5410, 1), (Sum.inr 5413, 1), (Sum.inr 5421, 1), (Sum.inr 5428, 1), (Sum.inr 5429, 1), (Sum.inr 5430, 1), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5436, 1), (Sum.inr 5438, 1), (Sum.inr 5446, 2), (Sum.inr 5451, 1), (Sum.inr 5468, 1), (Sum.inr 5471, 1), (Sum.inr 5473, 1), (Sum.inr 5475, 1), (Sum.inr 5477, 1), (Sum.inr 5483, 1), (Sum.inr 5487, 1)]

theorem sourceEq1075 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1075 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1075 + difference 0 1) (sourceB1075 + difference 1 0) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1075 + difference 0 1) (sourceB1075 + difference 1 0) sourceC1075) = raw17807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17807; decide +kernel
    rw [ha]
    exact (canonical17807 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1075 + difference 0 2) (sourceB1075 + difference 2 0) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1075 + difference 0 2) (sourceB1075 + difference 2 0) sourceC1075) = raw17808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17808; decide +kernel
    rw [ha]
    exact (canonical17808 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1075 + difference 0 3) (sourceB1075 + difference 3 0) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA1075 + difference 0 3) (sourceB1075 + difference 3 0) sourceC1075) = raw17809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17809; decide +kernel
    rw [ha]
    exact (canonical17809 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1075 + difference 0 4) (sourceB1075 + difference 4 0) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1075 + difference 0 4) (sourceB1075 + difference 4 0) sourceC1075) = raw17470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17470; decide +kernel
    rw [ha]
    exact (canonical17470 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1075 + difference 0 5) (sourceB1075 + difference 5 0) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1075 + difference 0 5) (sourceB1075 + difference 5 0) sourceC1075) = raw17810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17810; decide +kernel
    rw [ha]
    exact (canonical17810 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1075 + difference 1 0) (sourceB1075 + difference 0 1) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1075 + difference 1 0) (sourceB1075 + difference 0 1) sourceC1075) = raw14993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw14993; decide +kernel
    rw [ha]
    exact (canonical14993 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1075 + difference 1 2) (sourceB1075 + difference 2 1) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1075 + difference 1 2) (sourceB1075 + difference 2 1) sourceC1075) = raw17811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17811; decide +kernel
    rw [ha]
    exact (canonical17811 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1075 + difference 1 3) (sourceB1075 + difference 3 1) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1075 + difference 1 3) (sourceB1075 + difference 3 1) sourceC1075) = raw17812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17812; decide +kernel
    rw [ha]
    exact (canonical17812 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1075 + difference 1 4) (sourceB1075 + difference 4 1) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1075 + difference 1 4) (sourceB1075 + difference 4 1) sourceC1075) = raw17475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17475; decide +kernel
    rw [ha]
    exact (canonical17475 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1075 + difference 1 5) (sourceB1075 + difference 5 1) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1075 + difference 1 5) (sourceB1075 + difference 5 1) sourceC1075) = raw14974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw14974; decide +kernel
    rw [ha]
    exact (canonical14974 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1075 + difference 2 0) (sourceB1075 + difference 0 2) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1075 + difference 2 0) (sourceB1075 + difference 0 2) sourceC1075) = raw17485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17485; decide +kernel
    rw [ha]
    exact (canonical17485 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1075 + difference 2 1) (sourceB1075 + difference 1 2) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5468) := by
    have ha : (tripleCharges (sourceA1075 + difference 2 1) (sourceB1075 + difference 1 2) sourceC1075) = raw17486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17486; decide +kernel
    rw [ha]
    exact (canonical17486 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1075 + difference 2 3) (sourceB1075 + difference 3 2) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1075 + difference 2 3) (sourceB1075 + difference 3 2) sourceC1075) = raw17488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17488; decide +kernel
    rw [ha]
    exact (canonical17488 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1075 + difference 2 4) (sourceB1075 + difference 4 2) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1075 + difference 2 4) (sourceB1075 + difference 4 2) sourceC1075) = raw17643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17643; decide +kernel
    rw [ha]
    exact (canonical17643 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1075 + difference 2 5) (sourceB1075 + difference 5 2) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1075 + difference 2 5) (sourceB1075 + difference 5 2) sourceC1075) = raw17489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17489; decide +kernel
    rw [ha]
    exact (canonical17489 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1075 + difference 3 0) (sourceB1075 + difference 0 3) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA1075 + difference 3 0) (sourceB1075 + difference 0 3) sourceC1075) = raw14992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw14992; decide +kernel
    rw [ha]
    exact (canonical14992 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1075 + difference 3 1) (sourceB1075 + difference 1 3) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5475) := by
    have ha : (tripleCharges (sourceA1075 + difference 3 1) (sourceB1075 + difference 1 3) sourceC1075) = raw17813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17813; decide +kernel
    rw [ha]
    exact (canonical17813 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1075 + difference 3 2) (sourceB1075 + difference 2 3) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1075 + difference 3 2) (sourceB1075 + difference 2 3) sourceC1075) = raw17814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17814; decide +kernel
    rw [ha]
    exact (canonical17814 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1075 + difference 3 4) (sourceB1075 + difference 4 3) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA1075 + difference 3 4) (sourceB1075 + difference 4 3) sourceC1075) = raw17125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17125; decide +kernel
    rw [ha]
    exact (canonical17125 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1075 + difference 3 5) (sourceB1075 + difference 5 3) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1075 + difference 3 5) (sourceB1075 + difference 5 3) sourceC1075) = raw14973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw14973; decide +kernel
    rw [ha]
    exact (canonical14973 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1075 + difference 4 0) (sourceB1075 + difference 0 4) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA1075 + difference 4 0) (sourceB1075 + difference 0 4) sourceC1075) = raw17815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17815; decide +kernel
    rw [ha]
    exact (canonical17815 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1075 + difference 4 1) (sourceB1075 + difference 1 4) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA1075 + difference 4 1) (sourceB1075 + difference 1 4) sourceC1075) = raw17816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17816; decide +kernel
    rw [ha]
    exact (canonical17816 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1075 + difference 4 2) (sourceB1075 + difference 2 4) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA1075 + difference 4 2) (sourceB1075 + difference 2 4) sourceC1075) = raw17817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17817; decide +kernel
    rw [ha]
    exact (canonical17817 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1075 + difference 4 3) (sourceB1075 + difference 3 4) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA1075 + difference 4 3) (sourceB1075 + difference 3 4) sourceC1075) = raw17818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17818; decide +kernel
    rw [ha]
    exact (canonical17818 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1075 + difference 4 5) (sourceB1075 + difference 5 4) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA1075 + difference 4 5) (sourceB1075 + difference 5 4) sourceC1075) = raw17819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17819; decide +kernel
    rw [ha]
    exact (canonical17819 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1075 + difference 5 0) (sourceB1075 + difference 0 5) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA1075 + difference 5 0) (sourceB1075 + difference 0 5) sourceC1075) = raw17820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17820; decide +kernel
    rw [ha]
    exact (canonical17820 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1075 + difference 5 1) (sourceB1075 + difference 1 5) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1075 + difference 5 1) (sourceB1075 + difference 1 5) sourceC1075) = raw17821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17821; decide +kernel
    rw [ha]
    exact (canonical17821 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1075 + difference 5 2) (sourceB1075 + difference 2 5) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA1075 + difference 5 2) (sourceB1075 + difference 2 5) sourceC1075) = raw17822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17822; decide +kernel
    rw [ha]
    exact (canonical17822 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1075 + difference 5 3) (sourceB1075 + difference 3 5) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA1075 + difference 5 3) (sourceB1075 + difference 3 5) sourceC1075) = raw17823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17823; decide +kernel
    rw [ha]
    exact (canonical17823 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1075 + difference 5 4) (sourceB1075 + difference 4 5) sourceC1075) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1075 + difference 5 4) (sourceB1075 + difference 4 5) sourceC1075) = raw17492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1075 sourceB1075 sourceC1075 difference raw17492; decide +kernel
    rw [ha]
    exact (canonical17492 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1075 sourceB1075 sourceC1075
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1075, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1076 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB1076 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1076 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1076 : Integer.Sparse Master := [(Sum.inr 3569, 1), (Sum.inr 3570, 1), (Sum.inr 3573, 1), (Sum.inr 3578, 1), (Sum.inr 3624, 1), (Sum.inr 3758, 1), (Sum.inr 3766, 1), (Sum.inr 3767, 1), (Sum.inr 3771, 1), (Sum.inr 3794, 1), (Sum.inr 3808, 1), (Sum.inr 3817, 1), (Sum.inr 3845, 1), (Sum.inr 3873, 1), (Sum.inr 3877, 1), (Sum.inr 3884, 1), (Sum.inr 3950, 1), (Sum.inr 3953, 1), (Sum.inr 3954, 1), (Sum.inr 3958, 1), (Sum.inr 3959, 1), (Sum.inr 3963, 1), (Sum.inr 3971, 1), (Sum.inr 3972, 1), (Sum.inr 3981, 1), (Sum.inr 3982, 1), (Sum.inr 3986, 1), (Sum.inr 3987, 1), (Sum.inr 3993, 1), (Sum.inr 4027, 1)]

theorem sourceEq1076 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1076 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1076 + difference 0 1) (sourceB1076 + difference 1 0) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1076 + difference 0 1) (sourceB1076 + difference 1 0) sourceC1076) = raw17824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17824; decide +kernel
    rw [ha]
    exact (canonical17824 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1076 + difference 0 2) (sourceB1076 + difference 2 0) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA1076 + difference 0 2) (sourceB1076 + difference 2 0) sourceC1076) = raw17825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17825; decide +kernel
    rw [ha]
    exact (canonical17825 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1076 + difference 0 3) (sourceB1076 + difference 3 0) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA1076 + difference 0 3) (sourceB1076 + difference 3 0) sourceC1076) = raw17826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17826; decide +kernel
    rw [ha]
    exact (canonical17826 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1076 + difference 0 4) (sourceB1076 + difference 4 0) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA1076 + difference 0 4) (sourceB1076 + difference 4 0) sourceC1076) = raw17495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17495; decide +kernel
    rw [ha]
    exact (canonical17495 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1076 + difference 0 5) (sourceB1076 + difference 5 0) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4027) := by
    have ha : (tripleCharges (sourceA1076 + difference 0 5) (sourceB1076 + difference 5 0) sourceC1076) = raw17827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17827; decide +kernel
    rw [ha]
    exact (canonical17827 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1076 + difference 1 0) (sourceB1076 + difference 0 1) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA1076 + difference 1 0) (sourceB1076 + difference 0 1) sourceC1076) = raw17828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17828; decide +kernel
    rw [ha]
    exact (canonical17828 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1076 + difference 1 2) (sourceB1076 + difference 2 1) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA1076 + difference 1 2) (sourceB1076 + difference 2 1) sourceC1076) = raw17829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17829; decide +kernel
    rw [ha]
    exact (canonical17829 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1076 + difference 1 3) (sourceB1076 + difference 3 1) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA1076 + difference 1 3) (sourceB1076 + difference 3 1) sourceC1076) = raw17830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17830; decide +kernel
    rw [ha]
    exact (canonical17830 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1076 + difference 1 4) (sourceB1076 + difference 4 1) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1076 + difference 1 4) (sourceB1076 + difference 4 1) sourceC1076) = raw17500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17500; decide +kernel
    rw [ha]
    exact (canonical17500 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1076 + difference 1 5) (sourceB1076 + difference 5 1) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA1076 + difference 1 5) (sourceB1076 + difference 5 1) sourceC1076) = raw17831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17831; decide +kernel
    rw [ha]
    exact (canonical17831 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1076 + difference 2 0) (sourceB1076 + difference 0 2) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA1076 + difference 2 0) (sourceB1076 + difference 0 2) sourceC1076) = raw17512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17512; decide +kernel
    rw [ha]
    exact (canonical17512 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1076 + difference 2 1) (sourceB1076 + difference 1 2) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3950) := by
    have ha : (tripleCharges (sourceA1076 + difference 2 1) (sourceB1076 + difference 1 2) sourceC1076) = raw17513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17513; decide +kernel
    rw [ha]
    exact (canonical17513 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1076 + difference 2 3) (sourceB1076 + difference 3 2) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA1076 + difference 2 3) (sourceB1076 + difference 3 2) sourceC1076) = raw17515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17515; decide +kernel
    rw [ha]
    exact (canonical17515 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1076 + difference 2 4) (sourceB1076 + difference 4 2) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3971) := by
    have ha : (tripleCharges (sourceA1076 + difference 2 4) (sourceB1076 + difference 4 2) sourceC1076) = raw17658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17658; decide +kernel
    rw [ha]
    exact (canonical17658 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1076 + difference 2 5) (sourceB1076 + difference 5 2) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA1076 + difference 2 5) (sourceB1076 + difference 5 2) sourceC1076) = raw17516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17516; decide +kernel
    rw [ha]
    exact (canonical17516 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1076 + difference 3 0) (sourceB1076 + difference 0 3) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA1076 + difference 3 0) (sourceB1076 + difference 0 3) sourceC1076) = raw17832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17832; decide +kernel
    rw [ha]
    exact (canonical17832 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1076 + difference 3 1) (sourceB1076 + difference 1 3) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA1076 + difference 3 1) (sourceB1076 + difference 1 3) sourceC1076) = raw17833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17833; decide +kernel
    rw [ha]
    exact (canonical17833 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1076 + difference 3 2) (sourceB1076 + difference 2 3) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1076 + difference 3 2) (sourceB1076 + difference 2 3) sourceC1076) = raw17834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17834; decide +kernel
    rw [ha]
    exact (canonical17834 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1076 + difference 3 4) (sourceB1076 + difference 4 3) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3986) := by
    have ha : (tripleCharges (sourceA1076 + difference 3 4) (sourceB1076 + difference 4 3) sourceC1076) = raw17510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17510; decide +kernel
    rw [ha]
    exact (canonical17510 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1076 + difference 3 5) (sourceB1076 + difference 5 3) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA1076 + difference 3 5) (sourceB1076 + difference 5 3) sourceC1076) = raw17835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17835; decide +kernel
    rw [ha]
    exact (canonical17835 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1076 + difference 4 0) (sourceB1076 + difference 0 4) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA1076 + difference 4 0) (sourceB1076 + difference 0 4) sourceC1076) = raw17836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17836; decide +kernel
    rw [ha]
    exact (canonical17836 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1076 + difference 4 1) (sourceB1076 + difference 1 4) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA1076 + difference 4 1) (sourceB1076 + difference 1 4) sourceC1076) = raw17837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17837; decide +kernel
    rw [ha]
    exact (canonical17837 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1076 + difference 4 2) (sourceB1076 + difference 2 4) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3569) := by
    have ha : (tripleCharges (sourceA1076 + difference 4 2) (sourceB1076 + difference 2 4) sourceC1076) = raw17838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17838; decide +kernel
    rw [ha]
    exact (canonical17838 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1076 + difference 4 3) (sourceB1076 + difference 3 4) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA1076 + difference 4 3) (sourceB1076 + difference 3 4) sourceC1076) = raw17839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17839; decide +kernel
    rw [ha]
    exact (canonical17839 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1076 + difference 4 5) (sourceB1076 + difference 5 4) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA1076 + difference 4 5) (sourceB1076 + difference 5 4) sourceC1076) = raw17840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17840; decide +kernel
    rw [ha]
    exact (canonical17840 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1076 + difference 5 0) (sourceB1076 + difference 0 5) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA1076 + difference 5 0) (sourceB1076 + difference 0 5) sourceC1076) = raw17841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17841; decide +kernel
    rw [ha]
    exact (canonical17841 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1076 + difference 5 1) (sourceB1076 + difference 1 5) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA1076 + difference 5 1) (sourceB1076 + difference 1 5) sourceC1076) = raw17842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17842; decide +kernel
    rw [ha]
    exact (canonical17842 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1076 + difference 5 2) (sourceB1076 + difference 2 5) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA1076 + difference 5 2) (sourceB1076 + difference 2 5) sourceC1076) = raw17843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17843; decide +kernel
    rw [ha]
    exact (canonical17843 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1076 + difference 5 3) (sourceB1076 + difference 3 5) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3771) := by
    have ha : (tripleCharges (sourceA1076 + difference 5 3) (sourceB1076 + difference 3 5) sourceC1076) = raw17844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17844; decide +kernel
    rw [ha]
    exact (canonical17844 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1076 + difference 5 4) (sourceB1076 + difference 4 5) sourceC1076) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA1076 + difference 5 4) (sourceB1076 + difference 4 5) sourceC1076) = raw17519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1076 sourceB1076 sourceC1076 difference raw17519; decide +kernel
    rw [ha]
    exact (canonical17519 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1076 sourceB1076 sourceC1076
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1076, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1077 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1077 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1077 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceForm1077 : Integer.Sparse Master := [(Sum.inr 4091, 1), (Sum.inr 5073, 1), (Sum.inr 5078, 1), (Sum.inr 5081, 1), (Sum.inr 5104, 1), (Sum.inr 5149, 1), (Sum.inr 5152, 1), (Sum.inr 5170, 1), (Sum.inr 5259, 1), (Sum.inr 5284, 1), (Sum.inr 5352, 1), (Sum.inr 5356, 1), (Sum.inr 5369, 1), (Sum.inr 5393, 1), (Sum.inr 5396, 1), (Sum.inr 5401, 1), (Sum.inr 5404, 1), (Sum.inr 5405, 1), (Sum.inr 5408, 1), (Sum.inr 5410, 2), (Sum.inr 5424, 1), (Sum.inr 5438, 1), (Sum.inr 5439, 1), (Sum.inr 5440, 1), (Sum.inr 5473, 1), (Sum.inr 5478, 1), (Sum.inr 5484, 1), (Sum.inr 5485, 1), (Sum.inr 5486, 1)]

theorem sourceEq1077 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1077 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1077 + difference 0 1) (sourceB1077 + difference 1 0) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1077 + difference 0 1) (sourceB1077 + difference 1 0) sourceC1077) = raw17845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17845; decide +kernel
    rw [ha]
    exact (canonical17845 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1077 + difference 0 2) (sourceB1077 + difference 2 0) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA1077 + difference 0 2) (sourceB1077 + difference 2 0) sourceC1077) = raw17846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17846; decide +kernel
    rw [ha]
    exact (canonical17846 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1077 + difference 0 3) (sourceB1077 + difference 3 0) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1077 + difference 0 3) (sourceB1077 + difference 3 0) sourceC1077) = raw17847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17847; decide +kernel
    rw [ha]
    exact (canonical17847 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1077 + difference 0 4) (sourceB1077 + difference 4 0) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1077 + difference 0 4) (sourceB1077 + difference 4 0) sourceC1077) = raw17848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17848; decide +kernel
    rw [ha]
    exact (canonical17848 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1077 + difference 0 5) (sourceB1077 + difference 5 0) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1077 + difference 0 5) (sourceB1077 + difference 5 0) sourceC1077) = raw17849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17849; decide +kernel
    rw [ha]
    exact (canonical17849 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1077 + difference 1 0) (sourceB1077 + difference 0 1) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA1077 + difference 1 0) (sourceB1077 + difference 0 1) sourceC1077) = raw17850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17850; decide +kernel
    rw [ha]
    exact (canonical17850 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1077 + difference 1 2) (sourceB1077 + difference 2 1) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1077 + difference 1 2) (sourceB1077 + difference 2 1) sourceC1077) = raw17851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17851; decide +kernel
    rw [ha]
    exact (canonical17851 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1077 + difference 1 3) (sourceB1077 + difference 3 1) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1077 + difference 1 3) (sourceB1077 + difference 3 1) sourceC1077) = raw17852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17852; decide +kernel
    rw [ha]
    exact (canonical17852 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1077 + difference 1 4) (sourceB1077 + difference 4 1) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1077 + difference 1 4) (sourceB1077 + difference 4 1) sourceC1077) = raw17853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17853; decide +kernel
    rw [ha]
    exact (canonical17853 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1077 + difference 1 5) (sourceB1077 + difference 5 1) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1077 + difference 1 5) (sourceB1077 + difference 5 1) sourceC1077) = raw17854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17854; decide +kernel
    rw [ha]
    exact (canonical17854 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1077 + difference 2 0) (sourceB1077 + difference 0 2) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA1077 + difference 2 0) (sourceB1077 + difference 0 2) sourceC1077) = raw17855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17855; decide +kernel
    rw [ha]
    exact (canonical17855 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1077 + difference 2 1) (sourceB1077 + difference 1 2) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA1077 + difference 2 1) (sourceB1077 + difference 1 2) sourceC1077) = raw17856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17856; decide +kernel
    rw [ha]
    exact (canonical17856 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1077 + difference 2 3) (sourceB1077 + difference 3 2) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA1077 + difference 2 3) (sourceB1077 + difference 3 2) sourceC1077) = raw17857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17857; decide +kernel
    rw [ha]
    exact (canonical17857 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1077 + difference 2 4) (sourceB1077 + difference 4 2) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1077 + difference 2 4) (sourceB1077 + difference 4 2) sourceC1077) = raw17858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17858; decide +kernel
    rw [ha]
    exact (canonical17858 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1077 + difference 2 5) (sourceB1077 + difference 5 2) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1077 + difference 2 5) (sourceB1077 + difference 5 2) sourceC1077) = raw17859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17859; decide +kernel
    rw [ha]
    exact (canonical17859 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1077 + difference 3 0) (sourceB1077 + difference 0 3) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA1077 + difference 3 0) (sourceB1077 + difference 0 3) sourceC1077) = raw17860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17860; decide +kernel
    rw [ha]
    exact (canonical17860 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1077 + difference 3 1) (sourceB1077 + difference 1 3) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA1077 + difference 3 1) (sourceB1077 + difference 1 3) sourceC1077) = raw17861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17861; decide +kernel
    rw [ha]
    exact (canonical17861 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1077 + difference 3 2) (sourceB1077 + difference 2 3) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1077 + difference 3 2) (sourceB1077 + difference 2 3) sourceC1077) = raw17862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17862; decide +kernel
    rw [ha]
    exact (canonical17862 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1077 + difference 3 4) (sourceB1077 + difference 4 3) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1077 + difference 3 4) (sourceB1077 + difference 4 3) sourceC1077) = raw17863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17863; decide +kernel
    rw [ha]
    exact (canonical17863 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1077 + difference 3 5) (sourceB1077 + difference 5 3) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1077 + difference 3 5) (sourceB1077 + difference 5 3) sourceC1077) = raw17864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17864; decide +kernel
    rw [ha]
    exact (canonical17864 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1077 + difference 4 0) (sourceB1077 + difference 0 4) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA1077 + difference 4 0) (sourceB1077 + difference 0 4) sourceC1077) = raw17865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17865; decide +kernel
    rw [ha]
    exact (canonical17865 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1077 + difference 4 1) (sourceB1077 + difference 1 4) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA1077 + difference 4 1) (sourceB1077 + difference 1 4) sourceC1077) = raw17866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17866; decide +kernel
    rw [ha]
    exact (canonical17866 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1077 + difference 4 2) (sourceB1077 + difference 2 4) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1077 + difference 4 2) (sourceB1077 + difference 2 4) sourceC1077) = raw17867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17867; decide +kernel
    rw [ha]
    exact (canonical17867 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1077 + difference 4 3) (sourceB1077 + difference 3 4) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA1077 + difference 4 3) (sourceB1077 + difference 3 4) sourceC1077) = raw17868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17868; decide +kernel
    rw [ha]
    exact (canonical17868 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1077 + difference 4 5) (sourceB1077 + difference 5 4) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1077 + difference 4 5) (sourceB1077 + difference 5 4) sourceC1077) = raw17869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17869; decide +kernel
    rw [ha]
    exact (canonical17869 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1077 + difference 5 0) (sourceB1077 + difference 0 5) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1077 + difference 5 0) (sourceB1077 + difference 0 5) sourceC1077) = raw17870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17870; decide +kernel
    rw [ha]
    exact (canonical17870 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1077 + difference 5 1) (sourceB1077 + difference 1 5) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA1077 + difference 5 1) (sourceB1077 + difference 1 5) sourceC1077) = raw17871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17871; decide +kernel
    rw [ha]
    exact (canonical17871 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1077 + difference 5 2) (sourceB1077 + difference 2 5) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1077 + difference 5 2) (sourceB1077 + difference 2 5) sourceC1077) = raw17872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17872; decide +kernel
    rw [ha]
    exact (canonical17872 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1077 + difference 5 3) (sourceB1077 + difference 3 5) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA1077 + difference 5 3) (sourceB1077 + difference 3 5) sourceC1077) = raw17873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17873; decide +kernel
    rw [ha]
    exact (canonical17873 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1077 + difference 5 4) (sourceB1077 + difference 4 5) sourceC1077) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA1077 + difference 5 4) (sourceB1077 + difference 4 5) sourceC1077) = raw17874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1077 sourceB1077 sourceC1077 difference raw17874; decide +kernel
    rw [ha]
    exact (canonical17874 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1077 sourceB1077 sourceC1077
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1077, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1078 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceB1078 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceC1078 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm1078 : Integer.Sparse Master := [(Sum.inr 4092, 1), (Sum.inr 5098, 1), (Sum.inr 5101, 1), (Sum.inr 5102, 1), (Sum.inr 5105, 1), (Sum.inr 5271, 1), (Sum.inr 5365, 1), (Sum.inr 5367, 1), (Sum.inr 5368, 1), (Sum.inr 5370, 1), (Sum.inr 5394, 1), (Sum.inr 5395, 1), (Sum.inr 5397, 1), (Sum.inr 5405, 1), (Sum.inr 5406, 1), (Sum.inr 5409, 1), (Sum.inr 5410, 1), (Sum.inr 5411, 2), (Sum.inr 5412, 1), (Sum.inr 5413, 1), (Sum.inr 5424, 1), (Sum.inr 5434, 2), (Sum.inr 5435, 1), (Sum.inr 5442, 1), (Sum.inr 5473, 1), (Sum.inr 5477, 1), (Sum.inr 5483, 1), (Sum.inr 5487, 1)]

theorem sourceEq1078 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1078 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1078 + difference 0 1) (sourceB1078 + difference 1 0) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1078 + difference 0 1) (sourceB1078 + difference 1 0) sourceC1078) = raw17875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17875; decide +kernel
    rw [ha]
    exact (canonical17875 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1078 + difference 0 2) (sourceB1078 + difference 2 0) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1078 + difference 0 2) (sourceB1078 + difference 2 0) sourceC1078) = raw17876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17876; decide +kernel
    rw [ha]
    exact (canonical17876 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1078 + difference 0 3) (sourceB1078 + difference 3 0) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1078 + difference 0 3) (sourceB1078 + difference 3 0) sourceC1078) = raw17877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17877; decide +kernel
    rw [ha]
    exact (canonical17877 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1078 + difference 0 4) (sourceB1078 + difference 4 0) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1078 + difference 0 4) (sourceB1078 + difference 4 0) sourceC1078) = raw17634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17634; decide +kernel
    rw [ha]
    exact (canonical17634 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1078 + difference 0 5) (sourceB1078 + difference 5 0) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1078 + difference 0 5) (sourceB1078 + difference 5 0) sourceC1078) = raw17470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17470; decide +kernel
    rw [ha]
    exact (canonical17470 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1078 + difference 1 0) (sourceB1078 + difference 0 1) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1078 + difference 1 0) (sourceB1078 + difference 0 1) sourceC1078) = raw17878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17878; decide +kernel
    rw [ha]
    exact (canonical17878 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1078 + difference 1 2) (sourceB1078 + difference 2 1) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1078 + difference 1 2) (sourceB1078 + difference 2 1) sourceC1078) = raw17879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17879; decide +kernel
    rw [ha]
    exact (canonical17879 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1078 + difference 1 3) (sourceB1078 + difference 3 1) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1078 + difference 1 3) (sourceB1078 + difference 3 1) sourceC1078) = raw17880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17880; decide +kernel
    rw [ha]
    exact (canonical17880 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1078 + difference 1 4) (sourceB1078 + difference 4 1) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1078 + difference 1 4) (sourceB1078 + difference 4 1) sourceC1078) = raw17637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17637; decide +kernel
    rw [ha]
    exact (canonical17637 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1078 + difference 1 5) (sourceB1078 + difference 5 1) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1078 + difference 1 5) (sourceB1078 + difference 5 1) sourceC1078) = raw17475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17475; decide +kernel
    rw [ha]
    exact (canonical17475 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1078 + difference 2 0) (sourceB1078 + difference 0 2) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA1078 + difference 2 0) (sourceB1078 + difference 0 2) sourceC1078) = raw17490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17490; decide +kernel
    rw [ha]
    exact (canonical17490 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1078 + difference 2 1) (sourceB1078 + difference 1 2) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1078 + difference 2 1) (sourceB1078 + difference 1 2) sourceC1078) = raw17491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17491; decide +kernel
    rw [ha]
    exact (canonical17491 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1078 + difference 2 3) (sourceB1078 + difference 3 2) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1078 + difference 2 3) (sourceB1078 + difference 3 2) sourceC1078) = raw17493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17493; decide +kernel
    rw [ha]
    exact (canonical17493 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1078 + difference 2 4) (sourceB1078 + difference 4 2) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1078 + difference 2 4) (sourceB1078 + difference 4 2) sourceC1078) = raw17389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17389; decide +kernel
    rw [ha]
    exact (canonical17389 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1078 + difference 2 5) (sourceB1078 + difference 5 2) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1078 + difference 2 5) (sourceB1078 + difference 5 2) sourceC1078) = raw17643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17643; decide +kernel
    rw [ha]
    exact (canonical17643 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1078 + difference 3 0) (sourceB1078 + difference 0 3) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA1078 + difference 3 0) (sourceB1078 + difference 0 3) sourceC1078) = raw17881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17881; decide +kernel
    rw [ha]
    exact (canonical17881 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1078 + difference 3 1) (sourceB1078 + difference 1 3) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA1078 + difference 3 1) (sourceB1078 + difference 1 3) sourceC1078) = raw17882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17882; decide +kernel
    rw [ha]
    exact (canonical17882 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1078 + difference 3 2) (sourceB1078 + difference 2 3) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1078 + difference 3 2) (sourceB1078 + difference 2 3) sourceC1078) = raw17883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17883; decide +kernel
    rw [ha]
    exact (canonical17883 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1078 + difference 3 4) (sourceB1078 + difference 4 3) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1078 + difference 3 4) (sourceB1078 + difference 4 3) sourceC1078) = raw17126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17126; decide +kernel
    rw [ha]
    exact (canonical17126 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1078 + difference 3 5) (sourceB1078 + difference 5 3) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA1078 + difference 3 5) (sourceB1078 + difference 5 3) sourceC1078) = raw17125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17125; decide +kernel
    rw [ha]
    exact (canonical17125 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1078 + difference 4 0) (sourceB1078 + difference 0 4) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA1078 + difference 4 0) (sourceB1078 + difference 0 4) sourceC1078) = raw17820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17820; decide +kernel
    rw [ha]
    exact (canonical17820 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1078 + difference 4 1) (sourceB1078 + difference 1 4) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1078 + difference 4 1) (sourceB1078 + difference 1 4) sourceC1078) = raw17821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17821; decide +kernel
    rw [ha]
    exact (canonical17821 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1078 + difference 4 2) (sourceB1078 + difference 2 4) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA1078 + difference 4 2) (sourceB1078 + difference 2 4) sourceC1078) = raw17822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17822; decide +kernel
    rw [ha]
    exact (canonical17822 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1078 + difference 4 3) (sourceB1078 + difference 3 4) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA1078 + difference 4 3) (sourceB1078 + difference 3 4) sourceC1078) = raw17823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17823; decide +kernel
    rw [ha]
    exact (canonical17823 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1078 + difference 4 5) (sourceB1078 + difference 5 4) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1078 + difference 4 5) (sourceB1078 + difference 5 4) sourceC1078) = raw17487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17487; decide +kernel
    rw [ha]
    exact (canonical17487 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1078 + difference 5 0) (sourceB1078 + difference 0 5) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA1078 + difference 5 0) (sourceB1078 + difference 0 5) sourceC1078) = raw17884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17884; decide +kernel
    rw [ha]
    exact (canonical17884 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1078 + difference 5 1) (sourceB1078 + difference 1 5) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA1078 + difference 5 1) (sourceB1078 + difference 1 5) sourceC1078) = raw17885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17885; decide +kernel
    rw [ha]
    exact (canonical17885 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1078 + difference 5 2) (sourceB1078 + difference 2 5) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA1078 + difference 5 2) (sourceB1078 + difference 2 5) sourceC1078) = raw17886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17886; decide +kernel
    rw [ha]
    exact (canonical17886 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1078 + difference 5 3) (sourceB1078 + difference 3 5) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA1078 + difference 5 3) (sourceB1078 + difference 3 5) sourceC1078) = raw17887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17887; decide +kernel
    rw [ha]
    exact (canonical17887 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1078 + difference 5 4) (sourceB1078 + difference 4 5) sourceC1078) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA1078 + difference 5 4) (sourceB1078 + difference 4 5) sourceC1078) = raw17646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1078 sourceB1078 sourceC1078 difference raw17646; decide +kernel
    rw [ha]
    exact (canonical17646 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1078 sourceB1078 sourceC1078
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1078, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1079 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1079 : Charge := ![1, -1, 1, 0, -1, 0]
def sourceC1079 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceForm1079 : Integer.Sparse Master := [(Sum.inr 5135, 1), (Sum.inr 5139, 1), (Sum.inr 5141, 1), (Sum.inr 5164, 1), (Sum.inr 5187, 1), (Sum.inr 5188, 1), (Sum.inr 5204, 1), (Sum.inr 5267, 1), (Sum.inr 5275, 1), (Sum.inr 5351, 1), (Sum.inr 5355, 1), (Sum.inr 5367, 1), (Sum.inr 5379, 1), (Sum.inr 5385, 1), (Sum.inr 5395, 1), (Sum.inr 5409, 1), (Sum.inr 5413, 1), (Sum.inr 5414, 1), (Sum.inr 5424, 1), (Sum.inr 5425, 1), (Sum.inr 5428, 1), (Sum.inr 5436, 1), (Sum.inr 5438, 2), (Sum.inr 5442, 1), (Sum.inr 5443, 1), (Sum.inr 5446, 1), (Sum.inr 5471, 1), (Sum.inr 5473, 1), (Sum.inr 5483, 1)]

theorem sourceEq1079 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1079 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1079 + difference 0 1) (sourceB1079 + difference 1 0) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1079 + difference 0 1) (sourceB1079 + difference 1 0) sourceC1079) = raw17888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17888; decide +kernel
    rw [ha]
    exact (canonical17888 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1079 + difference 0 2) (sourceB1079 + difference 2 0) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1079 + difference 0 2) (sourceB1079 + difference 2 0) sourceC1079) = raw17889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17889; decide +kernel
    rw [ha]
    exact (canonical17889 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1079 + difference 0 3) (sourceB1079 + difference 3 0) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1079 + difference 0 3) (sourceB1079 + difference 3 0) sourceC1079) = raw17890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17890; decide +kernel
    rw [ha]
    exact (canonical17890 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1079 + difference 0 4) (sourceB1079 + difference 4 0) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1079 + difference 0 4) (sourceB1079 + difference 4 0) sourceC1079) = raw17891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17891; decide +kernel
    rw [ha]
    exact (canonical17891 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1079 + difference 0 5) (sourceB1079 + difference 5 0) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1079 + difference 0 5) (sourceB1079 + difference 5 0) sourceC1079) = raw17892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17892; decide +kernel
    rw [ha]
    exact (canonical17892 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1079 + difference 1 0) (sourceB1079 + difference 0 1) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA1079 + difference 1 0) (sourceB1079 + difference 0 1) sourceC1079) = raw17893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17893; decide +kernel
    rw [ha]
    exact (canonical17893 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1079 + difference 1 2) (sourceB1079 + difference 2 1) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA1079 + difference 1 2) (sourceB1079 + difference 2 1) sourceC1079) = raw17894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17894; decide +kernel
    rw [ha]
    exact (canonical17894 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1079 + difference 1 3) (sourceB1079 + difference 3 1) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1079 + difference 1 3) (sourceB1079 + difference 3 1) sourceC1079) = raw17895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17895; decide +kernel
    rw [ha]
    exact (canonical17895 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1079 + difference 1 4) (sourceB1079 + difference 4 1) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1079 + difference 1 4) (sourceB1079 + difference 4 1) sourceC1079) = raw17896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17896; decide +kernel
    rw [ha]
    exact (canonical17896 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1079 + difference 1 5) (sourceB1079 + difference 5 1) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1079 + difference 1 5) (sourceB1079 + difference 5 1) sourceC1079) = raw17897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17897; decide +kernel
    rw [ha]
    exact (canonical17897 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1079 + difference 2 0) (sourceB1079 + difference 0 2) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA1079 + difference 2 0) (sourceB1079 + difference 0 2) sourceC1079) = raw17898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17898; decide +kernel
    rw [ha]
    exact (canonical17898 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1079 + difference 2 1) (sourceB1079 + difference 1 2) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA1079 + difference 2 1) (sourceB1079 + difference 1 2) sourceC1079) = raw17899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17899; decide +kernel
    rw [ha]
    exact (canonical17899 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1079 + difference 2 3) (sourceB1079 + difference 3 2) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1079 + difference 2 3) (sourceB1079 + difference 3 2) sourceC1079) = raw17900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17900; decide +kernel
    rw [ha]
    exact (canonical17900 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1079 + difference 2 4) (sourceB1079 + difference 4 2) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA1079 + difference 2 4) (sourceB1079 + difference 4 2) sourceC1079) = raw17901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17901; decide +kernel
    rw [ha]
    exact (canonical17901 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1079 + difference 2 5) (sourceB1079 + difference 5 2) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1079 + difference 2 5) (sourceB1079 + difference 5 2) sourceC1079) = raw17902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17902; decide +kernel
    rw [ha]
    exact (canonical17902 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1079 + difference 3 0) (sourceB1079 + difference 0 3) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA1079 + difference 3 0) (sourceB1079 + difference 0 3) sourceC1079) = raw17903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17903; decide +kernel
    rw [ha]
    exact (canonical17903 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1079 + difference 3 1) (sourceB1079 + difference 1 3) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1079 + difference 3 1) (sourceB1079 + difference 1 3) sourceC1079) = raw17904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17904; decide +kernel
    rw [ha]
    exact (canonical17904 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1079 + difference 3 2) (sourceB1079 + difference 2 3) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA1079 + difference 3 2) (sourceB1079 + difference 2 3) sourceC1079) = raw17905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17905; decide +kernel
    rw [ha]
    exact (canonical17905 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1079 + difference 3 4) (sourceB1079 + difference 4 3) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1079 + difference 3 4) (sourceB1079 + difference 4 3) sourceC1079) = raw17906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17906; decide +kernel
    rw [ha]
    exact (canonical17906 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1079 + difference 3 5) (sourceB1079 + difference 5 3) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1079 + difference 3 5) (sourceB1079 + difference 5 3) sourceC1079) = raw17907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17907; decide +kernel
    rw [ha]
    exact (canonical17907 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1079 + difference 4 0) (sourceB1079 + difference 0 4) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA1079 + difference 4 0) (sourceB1079 + difference 0 4) sourceC1079) = raw17908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17908; decide +kernel
    rw [ha]
    exact (canonical17908 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1079 + difference 4 1) (sourceB1079 + difference 1 4) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA1079 + difference 4 1) (sourceB1079 + difference 1 4) sourceC1079) = raw17909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17909; decide +kernel
    rw [ha]
    exact (canonical17909 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1079 + difference 4 2) (sourceB1079 + difference 2 4) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5385) := by
    have ha : (tripleCharges (sourceA1079 + difference 4 2) (sourceB1079 + difference 2 4) sourceC1079) = raw17910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17910; decide +kernel
    rw [ha]
    exact (canonical17910 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1079 + difference 4 3) (sourceB1079 + difference 3 4) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA1079 + difference 4 3) (sourceB1079 + difference 3 4) sourceC1079) = raw17911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17911; decide +kernel
    rw [ha]
    exact (canonical17911 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1079 + difference 4 5) (sourceB1079 + difference 5 4) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1079 + difference 4 5) (sourceB1079 + difference 5 4) sourceC1079) = raw17912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17912; decide +kernel
    rw [ha]
    exact (canonical17912 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1079 + difference 5 0) (sourceB1079 + difference 0 5) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1079 + difference 5 0) (sourceB1079 + difference 0 5) sourceC1079) = raw17913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17913; decide +kernel
    rw [ha]
    exact (canonical17913 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1079 + difference 5 1) (sourceB1079 + difference 1 5) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA1079 + difference 5 1) (sourceB1079 + difference 1 5) sourceC1079) = raw17914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17914; decide +kernel
    rw [ha]
    exact (canonical17914 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1079 + difference 5 2) (sourceB1079 + difference 2 5) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA1079 + difference 5 2) (sourceB1079 + difference 2 5) sourceC1079) = raw17915 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17915; decide +kernel
    rw [ha]
    exact (canonical17915 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1079 + difference 5 3) (sourceB1079 + difference 3 5) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA1079 + difference 5 3) (sourceB1079 + difference 3 5) sourceC1079) = raw17916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17916; decide +kernel
    rw [ha]
    exact (canonical17916 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1079 + difference 5 4) (sourceB1079 + difference 4 5) sourceC1079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA1079 + difference 5 4) (sourceB1079 + difference 4 5) sourceC1079) = raw17917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1079 sourceB1079 sourceC1079 difference raw17917; decide +kernel
    rw [ha]
    exact (canonical17917 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1079 sourceB1079 sourceC1079
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1079, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1080 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1080 : Charge := ![1, -1, 1, 0, -1, 0]
def sourceC1080 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceForm1080 : Integer.Sparse Master := [(Sum.inr 3515, 1), (Sum.inr 3522, 1), (Sum.inr 3523, 1), (Sum.inr 3537, 1), (Sum.inr 3538, 1), (Sum.inr 3541, 1), (Sum.inr 3548, 1), (Sum.inr 3565, 1), (Sum.inr 3624, 1), (Sum.inr 3757, 1), (Sum.inr 3766, 1), (Sum.inr 3770, 1), (Sum.inr 3794, 1), (Sum.inr 3807, 1), (Sum.inr 3817, 1), (Sum.inr 3832, 1), (Sum.inr 3838, 1), (Sum.inr 3839, 1), (Sum.inr 3845, 1), (Sum.inr 3861, 1), (Sum.inr 3862, 1), (Sum.inr 3868, 1), (Sum.inr 3869, 1), (Sum.inr 3876, 1), (Sum.inr 3877, 1), (Sum.inr 3884, 1), (Sum.inr 3953, 1), (Sum.inr 3958, 1), (Sum.inr 3981, 1), (Sum.inr 3993, 1)]

theorem sourceEq1080 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1080 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1080 + difference 0 1) (sourceB1080 + difference 1 0) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA1080 + difference 0 1) (sourceB1080 + difference 1 0) sourceC1080) = raw17918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17918; decide +kernel
    rw [ha]
    exact (canonical17918 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1080 + difference 0 2) (sourceB1080 + difference 2 0) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1080 + difference 0 2) (sourceB1080 + difference 2 0) sourceC1080) = raw17919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17919; decide +kernel
    rw [ha]
    exact (canonical17919 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1080 + difference 0 3) (sourceB1080 + difference 3 0) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA1080 + difference 0 3) (sourceB1080 + difference 3 0) sourceC1080) = raw17920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17920; decide +kernel
    rw [ha]
    exact (canonical17920 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1080 + difference 0 4) (sourceB1080 + difference 4 0) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3861) := by
    have ha : (tripleCharges (sourceA1080 + difference 0 4) (sourceB1080 + difference 4 0) sourceC1080) = raw17921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17921; decide +kernel
    rw [ha]
    exact (canonical17921 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1080 + difference 0 5) (sourceB1080 + difference 5 0) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1080 + difference 0 5) (sourceB1080 + difference 5 0) sourceC1080) = raw17922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17922; decide +kernel
    rw [ha]
    exact (canonical17922 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1080 + difference 1 0) (sourceB1080 + difference 0 1) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA1080 + difference 1 0) (sourceB1080 + difference 0 1) sourceC1080) = raw17923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17923; decide +kernel
    rw [ha]
    exact (canonical17923 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1080 + difference 1 2) (sourceB1080 + difference 2 1) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA1080 + difference 1 2) (sourceB1080 + difference 2 1) sourceC1080) = raw17924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17924; decide +kernel
    rw [ha]
    exact (canonical17924 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1080 + difference 1 3) (sourceB1080 + difference 3 1) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA1080 + difference 1 3) (sourceB1080 + difference 3 1) sourceC1080) = raw17925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17925; decide +kernel
    rw [ha]
    exact (canonical17925 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1080 + difference 1 4) (sourceB1080 + difference 4 1) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA1080 + difference 1 4) (sourceB1080 + difference 4 1) sourceC1080) = raw17926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17926; decide +kernel
    rw [ha]
    exact (canonical17926 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1080 + difference 1 5) (sourceB1080 + difference 5 1) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA1080 + difference 1 5) (sourceB1080 + difference 5 1) sourceC1080) = raw17927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17927; decide +kernel
    rw [ha]
    exact (canonical17927 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1080 + difference 2 0) (sourceB1080 + difference 0 2) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA1080 + difference 2 0) (sourceB1080 + difference 0 2) sourceC1080) = raw17928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17928; decide +kernel
    rw [ha]
    exact (canonical17928 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1080 + difference 2 1) (sourceB1080 + difference 1 2) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA1080 + difference 2 1) (sourceB1080 + difference 1 2) sourceC1080) = raw17929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17929; decide +kernel
    rw [ha]
    exact (canonical17929 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1080 + difference 2 3) (sourceB1080 + difference 3 2) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA1080 + difference 2 3) (sourceB1080 + difference 3 2) sourceC1080) = raw17930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17930; decide +kernel
    rw [ha]
    exact (canonical17930 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1080 + difference 2 4) (sourceB1080 + difference 4 2) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA1080 + difference 2 4) (sourceB1080 + difference 4 2) sourceC1080) = raw17931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17931; decide +kernel
    rw [ha]
    exact (canonical17931 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1080 + difference 2 5) (sourceB1080 + difference 5 2) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1080 + difference 2 5) (sourceB1080 + difference 5 2) sourceC1080) = raw17932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17932; decide +kernel
    rw [ha]
    exact (canonical17932 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1080 + difference 3 0) (sourceB1080 + difference 0 3) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA1080 + difference 3 0) (sourceB1080 + difference 0 3) sourceC1080) = raw17933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17933; decide +kernel
    rw [ha]
    exact (canonical17933 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1080 + difference 3 1) (sourceB1080 + difference 1 3) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA1080 + difference 3 1) (sourceB1080 + difference 1 3) sourceC1080) = raw17934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17934; decide +kernel
    rw [ha]
    exact (canonical17934 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1080 + difference 3 2) (sourceB1080 + difference 2 3) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA1080 + difference 3 2) (sourceB1080 + difference 2 3) sourceC1080) = raw17935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17935; decide +kernel
    rw [ha]
    exact (canonical17935 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1080 + difference 3 4) (sourceB1080 + difference 4 3) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA1080 + difference 3 4) (sourceB1080 + difference 4 3) sourceC1080) = raw17936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17936; decide +kernel
    rw [ha]
    exact (canonical17936 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1080 + difference 3 5) (sourceB1080 + difference 5 3) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA1080 + difference 3 5) (sourceB1080 + difference 5 3) sourceC1080) = raw17937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17937; decide +kernel
    rw [ha]
    exact (canonical17937 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1080 + difference 4 0) (sourceB1080 + difference 0 4) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA1080 + difference 4 0) (sourceB1080 + difference 0 4) sourceC1080) = raw17938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17938; decide +kernel
    rw [ha]
    exact (canonical17938 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1080 + difference 4 1) (sourceB1080 + difference 1 4) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA1080 + difference 4 1) (sourceB1080 + difference 1 4) sourceC1080) = raw17939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17939; decide +kernel
    rw [ha]
    exact (canonical17939 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1080 + difference 4 2) (sourceB1080 + difference 2 4) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3868) := by
    have ha : (tripleCharges (sourceA1080 + difference 4 2) (sourceB1080 + difference 2 4) sourceC1080) = raw17940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17940; decide +kernel
    rw [ha]
    exact (canonical17940 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1080 + difference 4 3) (sourceB1080 + difference 3 4) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA1080 + difference 4 3) (sourceB1080 + difference 3 4) sourceC1080) = raw17941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17941; decide +kernel
    rw [ha]
    exact (canonical17941 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1080 + difference 4 5) (sourceB1080 + difference 5 4) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA1080 + difference 4 5) (sourceB1080 + difference 5 4) sourceC1080) = raw17942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17942; decide +kernel
    rw [ha]
    exact (canonical17942 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1080 + difference 5 0) (sourceB1080 + difference 0 5) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1080 + difference 5 0) (sourceB1080 + difference 0 5) sourceC1080) = raw17943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17943; decide +kernel
    rw [ha]
    exact (canonical17943 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1080 + difference 5 1) (sourceB1080 + difference 1 5) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA1080 + difference 5 1) (sourceB1080 + difference 1 5) sourceC1080) = raw17944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17944; decide +kernel
    rw [ha]
    exact (canonical17944 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1080 + difference 5 2) (sourceB1080 + difference 2 5) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA1080 + difference 5 2) (sourceB1080 + difference 2 5) sourceC1080) = raw17945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17945; decide +kernel
    rw [ha]
    exact (canonical17945 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1080 + difference 5 3) (sourceB1080 + difference 3 5) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3515) := by
    have ha : (tripleCharges (sourceA1080 + difference 5 3) (sourceB1080 + difference 3 5) sourceC1080) = raw17946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17946; decide +kernel
    rw [ha]
    exact (canonical17946 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1080 + difference 5 4) (sourceB1080 + difference 4 5) sourceC1080) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA1080 + difference 5 4) (sourceB1080 + difference 4 5) sourceC1080) = raw17947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1080 sourceB1080 sourceC1080 difference raw17947; decide +kernel
    rw [ha]
    exact (canonical17947 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1080 sourceB1080 sourceC1080
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1080, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1081 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1081 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceC1081 : Charge := ![1, -1, 1, 0, -1, 0]
def sourceForm1081 : Integer.Sparse Master := [(Sum.inr 4787, 1), (Sum.inr 4788, 2), (Sum.inr 4835, 2), (Sum.inr 4996, 2), (Sum.inr 5003, 2), (Sum.inr 5015, 2), (Sum.inr 5258, 2), (Sum.inr 5346, 2), (Sum.inr 5368, 2), (Sum.inr 5395, 2), (Sum.inr 5424, 2), (Sum.inr 5434, 2), (Sum.inr 5439, 2), (Sum.inr 5472, 1), (Sum.inr 5473, 2), (Sum.inr 5490, 2)]

theorem sourceEq1081 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1081 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1081 + difference 0 1) (sourceB1081 + difference 1 0) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1081 + difference 0 1) (sourceB1081 + difference 1 0) sourceC1081) = raw17948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17948; decide +kernel
    rw [ha]
    exact (canonical17948 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1081 + difference 0 2) (sourceB1081 + difference 2 0) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1081 + difference 0 2) (sourceB1081 + difference 2 0) sourceC1081) = raw17949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17949; decide +kernel
    rw [ha]
    exact (canonical17949 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1081 + difference 0 3) (sourceB1081 + difference 3 0) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1081 + difference 0 3) (sourceB1081 + difference 3 0) sourceC1081) = raw17950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17950; decide +kernel
    rw [ha]
    exact (canonical17950 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1081 + difference 0 4) (sourceB1081 + difference 4 0) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1081 + difference 0 4) (sourceB1081 + difference 4 0) sourceC1081) = raw17951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17951; decide +kernel
    rw [ha]
    exact (canonical17951 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1081 + difference 0 5) (sourceB1081 + difference 5 0) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1081 + difference 0 5) (sourceB1081 + difference 5 0) sourceC1081) = raw17952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17952; decide +kernel
    rw [ha]
    exact (canonical17952 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1081 + difference 1 0) (sourceB1081 + difference 0 1) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1081 + difference 1 0) (sourceB1081 + difference 0 1) sourceC1081) = raw17953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17953; decide +kernel
    rw [ha]
    exact (canonical17953 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1081 + difference 1 2) (sourceB1081 + difference 2 1) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1081 + difference 1 2) (sourceB1081 + difference 2 1) sourceC1081) = raw17954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17954; decide +kernel
    rw [ha]
    exact (canonical17954 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1081 + difference 1 3) (sourceB1081 + difference 3 1) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1081 + difference 1 3) (sourceB1081 + difference 3 1) sourceC1081) = raw17955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17955; decide +kernel
    rw [ha]
    exact (canonical17955 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1081 + difference 1 4) (sourceB1081 + difference 4 1) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1081 + difference 1 4) (sourceB1081 + difference 4 1) sourceC1081) = raw17956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17956; decide +kernel
    rw [ha]
    exact (canonical17956 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1081 + difference 1 5) (sourceB1081 + difference 5 1) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1081 + difference 1 5) (sourceB1081 + difference 5 1) sourceC1081) = raw17957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17957; decide +kernel
    rw [ha]
    exact (canonical17957 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1081 + difference 2 0) (sourceB1081 + difference 0 2) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA1081 + difference 2 0) (sourceB1081 + difference 0 2) sourceC1081) = raw17958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17958; decide +kernel
    rw [ha]
    exact (canonical17958 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1081 + difference 2 1) (sourceB1081 + difference 1 2) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA1081 + difference 2 1) (sourceB1081 + difference 1 2) sourceC1081) = raw17959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17959; decide +kernel
    rw [ha]
    exact (canonical17959 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1081 + difference 2 3) (sourceB1081 + difference 3 2) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA1081 + difference 2 3) (sourceB1081 + difference 3 2) sourceC1081) = raw17960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17960; decide +kernel
    rw [ha]
    exact (canonical17960 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1081 + difference 2 4) (sourceB1081 + difference 4 2) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1081 + difference 2 4) (sourceB1081 + difference 4 2) sourceC1081) = raw17961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17961; decide +kernel
    rw [ha]
    exact (canonical17961 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1081 + difference 2 5) (sourceB1081 + difference 5 2) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1081 + difference 2 5) (sourceB1081 + difference 5 2) sourceC1081) = raw17962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17962; decide +kernel
    rw [ha]
    exact (canonical17962 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1081 + difference 3 0) (sourceB1081 + difference 0 3) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA1081 + difference 3 0) (sourceB1081 + difference 0 3) sourceC1081) = raw17963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17963; decide +kernel
    rw [ha]
    exact (canonical17963 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1081 + difference 3 1) (sourceB1081 + difference 1 3) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA1081 + difference 3 1) (sourceB1081 + difference 1 3) sourceC1081) = raw17964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17964; decide +kernel
    rw [ha]
    exact (canonical17964 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1081 + difference 3 2) (sourceB1081 + difference 2 3) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1081 + difference 3 2) (sourceB1081 + difference 2 3) sourceC1081) = raw17965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17965; decide +kernel
    rw [ha]
    exact (canonical17965 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1081 + difference 3 4) (sourceB1081 + difference 4 3) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1081 + difference 3 4) (sourceB1081 + difference 4 3) sourceC1081) = raw17966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17966; decide +kernel
    rw [ha]
    exact (canonical17966 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1081 + difference 3 5) (sourceB1081 + difference 5 3) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1081 + difference 3 5) (sourceB1081 + difference 5 3) sourceC1081) = raw17967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17967; decide +kernel
    rw [ha]
    exact (canonical17967 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1081 + difference 4 0) (sourceB1081 + difference 0 4) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA1081 + difference 4 0) (sourceB1081 + difference 0 4) sourceC1081) = raw17968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17968; decide +kernel
    rw [ha]
    exact (canonical17968 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1081 + difference 4 1) (sourceB1081 + difference 1 4) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA1081 + difference 4 1) (sourceB1081 + difference 1 4) sourceC1081) = raw17969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17969; decide +kernel
    rw [ha]
    exact (canonical17969 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1081 + difference 4 2) (sourceB1081 + difference 2 4) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1081 + difference 4 2) (sourceB1081 + difference 2 4) sourceC1081) = raw17970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17970; decide +kernel
    rw [ha]
    exact (canonical17970 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1081 + difference 4 3) (sourceB1081 + difference 3 4) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA1081 + difference 4 3) (sourceB1081 + difference 3 4) sourceC1081) = raw17971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17971; decide +kernel
    rw [ha]
    exact (canonical17971 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1081 + difference 4 5) (sourceB1081 + difference 5 4) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1081 + difference 4 5) (sourceB1081 + difference 5 4) sourceC1081) = raw17972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17972; decide +kernel
    rw [ha]
    exact (canonical17972 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1081 + difference 5 0) (sourceB1081 + difference 0 5) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA1081 + difference 5 0) (sourceB1081 + difference 0 5) sourceC1081) = raw17973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17973; decide +kernel
    rw [ha]
    exact (canonical17973 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1081 + difference 5 1) (sourceB1081 + difference 1 5) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA1081 + difference 5 1) (sourceB1081 + difference 1 5) sourceC1081) = raw17974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17974; decide +kernel
    rw [ha]
    exact (canonical17974 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1081 + difference 5 2) (sourceB1081 + difference 2 5) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA1081 + difference 5 2) (sourceB1081 + difference 2 5) sourceC1081) = raw17975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17975; decide +kernel
    rw [ha]
    exact (canonical17975 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1081 + difference 5 3) (sourceB1081 + difference 3 5) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA1081 + difference 5 3) (sourceB1081 + difference 3 5) sourceC1081) = raw17976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17976; decide +kernel
    rw [ha]
    exact (canonical17976 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1081 + difference 5 4) (sourceB1081 + difference 4 5) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA1081 + difference 5 4) (sourceB1081 + difference 4 5) sourceC1081) = raw17977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17977; decide +kernel
    rw [ha]
    exact (canonical17977 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1081 sourceB1081 sourceC1081
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1081, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1082 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1082 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceC1082 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceForm1082 : Integer.Sparse Master := [(Sum.inr 5199, 4), (Sum.inr 5201, 1), (Sum.inr 5207, 2), (Sum.inr 5300, 2), (Sum.inr 5368, 4), (Sum.inr 5371, 1), (Sum.inr 5413, 2), (Sum.inr 5446, 4), (Sum.inr 5449, 1), (Sum.inr 5451, 2), (Sum.inr 5468, 2), (Sum.inr 5473, 4), (Sum.inr 5487, 1)]

theorem sourceEq1082 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1082 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1082 + difference 0 1) (sourceB1082 + difference 1 0) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA1082 + difference 0 1) (sourceB1082 + difference 1 0) sourceC1082) = raw17978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17978; decide +kernel
    rw [ha]
    exact (canonical17978 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1082 + difference 0 2) (sourceB1082 + difference 2 0) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1082 + difference 0 2) (sourceB1082 + difference 2 0) sourceC1082) = raw17979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17979; decide +kernel
    rw [ha]
    exact (canonical17979 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1082 + difference 0 3) (sourceB1082 + difference 3 0) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1082 + difference 0 3) (sourceB1082 + difference 3 0) sourceC1082) = raw17980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17980; decide +kernel
    rw [ha]
    exact (canonical17980 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1082 + difference 0 4) (sourceB1082 + difference 4 0) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1082 + difference 0 4) (sourceB1082 + difference 4 0) sourceC1082) = raw17981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17981; decide +kernel
    rw [ha]
    exact (canonical17981 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1082 + difference 0 5) (sourceB1082 + difference 5 0) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA1082 + difference 0 5) (sourceB1082 + difference 5 0) sourceC1082) = raw17982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17982; decide +kernel
    rw [ha]
    exact (canonical17982 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1082 + difference 1 0) (sourceB1082 + difference 0 1) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA1082 + difference 1 0) (sourceB1082 + difference 0 1) sourceC1082) = raw17983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17983; decide +kernel
    rw [ha]
    exact (canonical17983 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1082 + difference 1 2) (sourceB1082 + difference 2 1) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1082 + difference 1 2) (sourceB1082 + difference 2 1) sourceC1082) = raw17984 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17984; decide +kernel
    rw [ha]
    exact (canonical17984 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1082 + difference 1 3) (sourceB1082 + difference 3 1) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1082 + difference 1 3) (sourceB1082 + difference 3 1) sourceC1082) = raw17985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17985; decide +kernel
    rw [ha]
    exact (canonical17985 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1082 + difference 1 4) (sourceB1082 + difference 4 1) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5449) := by
    have ha : (tripleCharges (sourceA1082 + difference 1 4) (sourceB1082 + difference 4 1) sourceC1082) = raw17986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17986; decide +kernel
    rw [ha]
    exact (canonical17986 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1082 + difference 1 5) (sourceB1082 + difference 5 1) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1082 + difference 1 5) (sourceB1082 + difference 5 1) sourceC1082) = raw17987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17987; decide +kernel
    rw [ha]
    exact (canonical17987 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1082 + difference 2 0) (sourceB1082 + difference 0 2) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA1082 + difference 2 0) (sourceB1082 + difference 0 2) sourceC1082) = raw17988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17988; decide +kernel
    rw [ha]
    exact (canonical17988 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1082 + difference 2 1) (sourceB1082 + difference 1 2) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1082 + difference 2 1) (sourceB1082 + difference 1 2) sourceC1082) = raw17989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17989; decide +kernel
    rw [ha]
    exact (canonical17989 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1082 + difference 2 3) (sourceB1082 + difference 3 2) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5468) := by
    have ha : (tripleCharges (sourceA1082 + difference 2 3) (sourceB1082 + difference 3 2) sourceC1082) = raw17990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17990; decide +kernel
    rw [ha]
    exact (canonical17990 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1082 + difference 2 4) (sourceB1082 + difference 4 2) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1082 + difference 2 4) (sourceB1082 + difference 4 2) sourceC1082) = raw17991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17991; decide +kernel
    rw [ha]
    exact (canonical17991 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1082 + difference 2 5) (sourceB1082 + difference 5 2) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1082 + difference 2 5) (sourceB1082 + difference 5 2) sourceC1082) = raw17992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17992; decide +kernel
    rw [ha]
    exact (canonical17992 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1082 + difference 3 0) (sourceB1082 + difference 0 3) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA1082 + difference 3 0) (sourceB1082 + difference 0 3) sourceC1082) = raw17993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17993; decide +kernel
    rw [ha]
    exact (canonical17993 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1082 + difference 3 1) (sourceB1082 + difference 1 3) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1082 + difference 3 1) (sourceB1082 + difference 1 3) sourceC1082) = raw17994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17994; decide +kernel
    rw [ha]
    exact (canonical17994 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1082 + difference 3 2) (sourceB1082 + difference 2 3) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5468) := by
    have ha : (tripleCharges (sourceA1082 + difference 3 2) (sourceB1082 + difference 2 3) sourceC1082) = raw17995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17995; decide +kernel
    rw [ha]
    exact (canonical17995 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1082 + difference 3 4) (sourceB1082 + difference 4 3) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1082 + difference 3 4) (sourceB1082 + difference 4 3) sourceC1082) = raw17996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17996; decide +kernel
    rw [ha]
    exact (canonical17996 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1082 + difference 3 5) (sourceB1082 + difference 5 3) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1082 + difference 3 5) (sourceB1082 + difference 5 3) sourceC1082) = raw17997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17997; decide +kernel
    rw [ha]
    exact (canonical17997 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1082 + difference 4 0) (sourceB1082 + difference 0 4) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA1082 + difference 4 0) (sourceB1082 + difference 0 4) sourceC1082) = raw17998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17998; decide +kernel
    rw [ha]
    exact (canonical17998 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1082 + difference 4 1) (sourceB1082 + difference 1 4) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA1082 + difference 4 1) (sourceB1082 + difference 1 4) sourceC1082) = raw17999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw17999; decide +kernel
    rw [ha]
    exact (canonical17999 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1082 + difference 4 2) (sourceB1082 + difference 2 4) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1082 + difference 4 2) (sourceB1082 + difference 2 4) sourceC1082) = raw18000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw18000; decide +kernel
    rw [ha]
    exact (canonical18000 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1082 + difference 4 3) (sourceB1082 + difference 3 4) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1082 + difference 4 3) (sourceB1082 + difference 3 4) sourceC1082) = raw18001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw18001; decide +kernel
    rw [ha]
    exact (canonical18001 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1082 + difference 4 5) (sourceB1082 + difference 5 4) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA1082 + difference 4 5) (sourceB1082 + difference 5 4) sourceC1082) = raw18002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw18002; decide +kernel
    rw [ha]
    exact (canonical18002 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1082 + difference 5 0) (sourceB1082 + difference 0 5) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5201) := by
    have ha : (tripleCharges (sourceA1082 + difference 5 0) (sourceB1082 + difference 0 5) sourceC1082) = raw18003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw18003; decide +kernel
    rw [ha]
    exact (canonical18003 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1082 + difference 5 1) (sourceB1082 + difference 1 5) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA1082 + difference 5 1) (sourceB1082 + difference 1 5) sourceC1082) = raw18004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw18004; decide +kernel
    rw [ha]
    exact (canonical18004 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1082 + difference 5 2) (sourceB1082 + difference 2 5) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA1082 + difference 5 2) (sourceB1082 + difference 2 5) sourceC1082) = raw18005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw18005; decide +kernel
    rw [ha]
    exact (canonical18005 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1082 + difference 5 3) (sourceB1082 + difference 3 5) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA1082 + difference 5 3) (sourceB1082 + difference 3 5) sourceC1082) = raw18006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw18006; decide +kernel
    rw [ha]
    exact (canonical18006 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1082 + difference 5 4) (sourceB1082 + difference 4 5) sourceC1082) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA1082 + difference 5 4) (sourceB1082 + difference 4 5) sourceC1082) = raw18007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1082 sourceB1082 sourceC1082 difference raw18007; decide +kernel
    rw [ha]
    exact (canonical18007 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1082 sourceB1082 sourceC1082
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1082, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1083 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1083 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceC1083 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceForm1083 : Integer.Sparse Master := [(Sum.inr 3578, 4), (Sum.inr 3579, 1), (Sum.inr 3584, 2), (Sum.inr 3631, 2), (Sum.inr 3767, 4), (Sum.inr 3775, 1), (Sum.inr 3817, 2), (Sum.inr 3950, 2), (Sum.inr 3958, 4), (Sum.inr 3959, 4), (Sum.inr 3986, 1), (Sum.inr 3987, 2), (Sum.inr 4030, 1)]

theorem sourceEq1083 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1083 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1083 + difference 0 1) (sourceB1083 + difference 1 0) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA1083 + difference 0 1) (sourceB1083 + difference 1 0) sourceC1083) = raw18008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18008; decide +kernel
    rw [ha]
    exact (canonical18008 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1083 + difference 0 2) (sourceB1083 + difference 2 0) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1083 + difference 0 2) (sourceB1083 + difference 2 0) sourceC1083) = raw18009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18009; decide +kernel
    rw [ha]
    exact (canonical18009 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1083 + difference 0 3) (sourceB1083 + difference 3 0) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1083 + difference 0 3) (sourceB1083 + difference 3 0) sourceC1083) = raw18010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18010; decide +kernel
    rw [ha]
    exact (canonical18010 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1083 + difference 0 4) (sourceB1083 + difference 4 0) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA1083 + difference 0 4) (sourceB1083 + difference 4 0) sourceC1083) = raw18011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18011; decide +kernel
    rw [ha]
    exact (canonical18011 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1083 + difference 0 5) (sourceB1083 + difference 5 0) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3986) := by
    have ha : (tripleCharges (sourceA1083 + difference 0 5) (sourceB1083 + difference 5 0) sourceC1083) = raw18012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18012; decide +kernel
    rw [ha]
    exact (canonical18012 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1083 + difference 1 0) (sourceB1083 + difference 0 1) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA1083 + difference 1 0) (sourceB1083 + difference 0 1) sourceC1083) = raw18013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18013; decide +kernel
    rw [ha]
    exact (canonical18013 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1083 + difference 1 2) (sourceB1083 + difference 2 1) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1083 + difference 1 2) (sourceB1083 + difference 2 1) sourceC1083) = raw18014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18014; decide +kernel
    rw [ha]
    exact (canonical18014 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1083 + difference 1 3) (sourceB1083 + difference 3 1) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1083 + difference 1 3) (sourceB1083 + difference 3 1) sourceC1083) = raw18015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18015; decide +kernel
    rw [ha]
    exact (canonical18015 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1083 + difference 1 4) (sourceB1083 + difference 4 1) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4030) := by
    have ha : (tripleCharges (sourceA1083 + difference 1 4) (sourceB1083 + difference 4 1) sourceC1083) = raw18016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18016; decide +kernel
    rw [ha]
    exact (canonical18016 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1083 + difference 1 5) (sourceB1083 + difference 5 1) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA1083 + difference 1 5) (sourceB1083 + difference 5 1) sourceC1083) = raw18017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18017; decide +kernel
    rw [ha]
    exact (canonical18017 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1083 + difference 2 0) (sourceB1083 + difference 0 2) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA1083 + difference 2 0) (sourceB1083 + difference 0 2) sourceC1083) = raw18018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18018; decide +kernel
    rw [ha]
    exact (canonical18018 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1083 + difference 2 1) (sourceB1083 + difference 1 2) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA1083 + difference 2 1) (sourceB1083 + difference 1 2) sourceC1083) = raw18019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18019; decide +kernel
    rw [ha]
    exact (canonical18019 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1083 + difference 2 3) (sourceB1083 + difference 3 2) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3950) := by
    have ha : (tripleCharges (sourceA1083 + difference 2 3) (sourceB1083 + difference 3 2) sourceC1083) = raw18020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18020; decide +kernel
    rw [ha]
    exact (canonical18020 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1083 + difference 2 4) (sourceB1083 + difference 4 2) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1083 + difference 2 4) (sourceB1083 + difference 4 2) sourceC1083) = raw18021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18021; decide +kernel
    rw [ha]
    exact (canonical18021 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1083 + difference 2 5) (sourceB1083 + difference 5 2) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1083 + difference 2 5) (sourceB1083 + difference 5 2) sourceC1083) = raw18022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18022; decide +kernel
    rw [ha]
    exact (canonical18022 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1083 + difference 3 0) (sourceB1083 + difference 0 3) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA1083 + difference 3 0) (sourceB1083 + difference 0 3) sourceC1083) = raw18023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18023; decide +kernel
    rw [ha]
    exact (canonical18023 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1083 + difference 3 1) (sourceB1083 + difference 1 3) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA1083 + difference 3 1) (sourceB1083 + difference 1 3) sourceC1083) = raw18024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18024; decide +kernel
    rw [ha]
    exact (canonical18024 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1083 + difference 3 2) (sourceB1083 + difference 2 3) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3950) := by
    have ha : (tripleCharges (sourceA1083 + difference 3 2) (sourceB1083 + difference 2 3) sourceC1083) = raw18025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18025; decide +kernel
    rw [ha]
    exact (canonical18025 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1083 + difference 3 4) (sourceB1083 + difference 4 3) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1083 + difference 3 4) (sourceB1083 + difference 4 3) sourceC1083) = raw18026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18026; decide +kernel
    rw [ha]
    exact (canonical18026 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1083 + difference 3 5) (sourceB1083 + difference 5 3) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1083 + difference 3 5) (sourceB1083 + difference 5 3) sourceC1083) = raw18027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18027; decide +kernel
    rw [ha]
    exact (canonical18027 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1083 + difference 4 0) (sourceB1083 + difference 0 4) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA1083 + difference 4 0) (sourceB1083 + difference 0 4) sourceC1083) = raw18028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18028; decide +kernel
    rw [ha]
    exact (canonical18028 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1083 + difference 4 1) (sourceB1083 + difference 1 4) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3775) := by
    have ha : (tripleCharges (sourceA1083 + difference 4 1) (sourceB1083 + difference 1 4) sourceC1083) = raw18029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18029; decide +kernel
    rw [ha]
    exact (canonical18029 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1083 + difference 4 2) (sourceB1083 + difference 2 4) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA1083 + difference 4 2) (sourceB1083 + difference 2 4) sourceC1083) = raw18030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18030; decide +kernel
    rw [ha]
    exact (canonical18030 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1083 + difference 4 3) (sourceB1083 + difference 3 4) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA1083 + difference 4 3) (sourceB1083 + difference 3 4) sourceC1083) = raw18031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18031; decide +kernel
    rw [ha]
    exact (canonical18031 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1083 + difference 4 5) (sourceB1083 + difference 5 4) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA1083 + difference 4 5) (sourceB1083 + difference 5 4) sourceC1083) = raw18032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18032; decide +kernel
    rw [ha]
    exact (canonical18032 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1083 + difference 5 0) (sourceB1083 + difference 0 5) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3579) := by
    have ha : (tripleCharges (sourceA1083 + difference 5 0) (sourceB1083 + difference 0 5) sourceC1083) = raw18033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18033; decide +kernel
    rw [ha]
    exact (canonical18033 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1083 + difference 5 1) (sourceB1083 + difference 1 5) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA1083 + difference 5 1) (sourceB1083 + difference 1 5) sourceC1083) = raw18034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18034; decide +kernel
    rw [ha]
    exact (canonical18034 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1083 + difference 5 2) (sourceB1083 + difference 2 5) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA1083 + difference 5 2) (sourceB1083 + difference 2 5) sourceC1083) = raw18035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18035; decide +kernel
    rw [ha]
    exact (canonical18035 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1083 + difference 5 3) (sourceB1083 + difference 3 5) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA1083 + difference 5 3) (sourceB1083 + difference 3 5) sourceC1083) = raw18036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18036; decide +kernel
    rw [ha]
    exact (canonical18036 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1083 + difference 5 4) (sourceB1083 + difference 4 5) sourceC1083) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA1083 + difference 5 4) (sourceB1083 + difference 4 5) sourceC1083) = raw18037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1083 sourceB1083 sourceC1083 difference raw18037; decide +kernel
    rw [ha]
    exact (canonical18037 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1083 sourceB1083 sourceC1083
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1083, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1084 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1084 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceC1084 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceForm1084 : Integer.Sparse Master := [(Sum.inr 5018, 8), (Sum.inr 5021, 2), (Sum.inr 5023, 2), (Sum.inr 5275, 4), (Sum.inr 5467, 2), (Sum.inr 5473, 8), (Sum.inr 5491, 2), (Sum.inr 5492, 2)]

theorem sourceEq1084 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1084 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1084 + difference 0 1) (sourceB1084 + difference 1 0) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA1084 + difference 0 1) (sourceB1084 + difference 1 0) sourceC1084) = raw18038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18038; decide +kernel
    rw [ha]
    exact (canonical18038 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1084 + difference 0 2) (sourceB1084 + difference 2 0) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1084 + difference 0 2) (sourceB1084 + difference 2 0) sourceC1084) = raw18039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18039; decide +kernel
    rw [ha]
    exact (canonical18039 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1084 + difference 0 3) (sourceB1084 + difference 3 0) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1084 + difference 0 3) (sourceB1084 + difference 3 0) sourceC1084) = raw18040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18040; decide +kernel
    rw [ha]
    exact (canonical18040 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1084 + difference 0 4) (sourceB1084 + difference 4 0) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1084 + difference 0 4) (sourceB1084 + difference 4 0) sourceC1084) = raw18041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18041; decide +kernel
    rw [ha]
    exact (canonical18041 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1084 + difference 0 5) (sourceB1084 + difference 5 0) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1084 + difference 0 5) (sourceB1084 + difference 5 0) sourceC1084) = raw18042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18042; decide +kernel
    rw [ha]
    exact (canonical18042 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1084 + difference 1 0) (sourceB1084 + difference 0 1) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA1084 + difference 1 0) (sourceB1084 + difference 0 1) sourceC1084) = raw18043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18043; decide +kernel
    rw [ha]
    exact (canonical18043 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1084 + difference 1 2) (sourceB1084 + difference 2 1) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1084 + difference 1 2) (sourceB1084 + difference 2 1) sourceC1084) = raw18044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18044; decide +kernel
    rw [ha]
    exact (canonical18044 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1084 + difference 1 3) (sourceB1084 + difference 3 1) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1084 + difference 1 3) (sourceB1084 + difference 3 1) sourceC1084) = raw18045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18045; decide +kernel
    rw [ha]
    exact (canonical18045 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1084 + difference 1 4) (sourceB1084 + difference 4 1) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1084 + difference 1 4) (sourceB1084 + difference 4 1) sourceC1084) = raw18046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18046; decide +kernel
    rw [ha]
    exact (canonical18046 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1084 + difference 1 5) (sourceB1084 + difference 5 1) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1084 + difference 1 5) (sourceB1084 + difference 5 1) sourceC1084) = raw18047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18047; decide +kernel
    rw [ha]
    exact (canonical18047 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1084 + difference 2 0) (sourceB1084 + difference 0 2) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA1084 + difference 2 0) (sourceB1084 + difference 0 2) sourceC1084) = raw18048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18048; decide +kernel
    rw [ha]
    exact (canonical18048 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1084 + difference 2 1) (sourceB1084 + difference 1 2) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA1084 + difference 2 1) (sourceB1084 + difference 1 2) sourceC1084) = raw18049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18049; decide +kernel
    rw [ha]
    exact (canonical18049 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1084 + difference 2 3) (sourceB1084 + difference 3 2) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5467) := by
    have ha : (tripleCharges (sourceA1084 + difference 2 3) (sourceB1084 + difference 3 2) sourceC1084) = raw18050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18050; decide +kernel
    rw [ha]
    exact (canonical18050 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1084 + difference 2 4) (sourceB1084 + difference 4 2) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1084 + difference 2 4) (sourceB1084 + difference 4 2) sourceC1084) = raw18051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18051; decide +kernel
    rw [ha]
    exact (canonical18051 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1084 + difference 2 5) (sourceB1084 + difference 5 2) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1084 + difference 2 5) (sourceB1084 + difference 5 2) sourceC1084) = raw18052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18052; decide +kernel
    rw [ha]
    exact (canonical18052 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1084 + difference 3 0) (sourceB1084 + difference 0 3) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA1084 + difference 3 0) (sourceB1084 + difference 0 3) sourceC1084) = raw18053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18053; decide +kernel
    rw [ha]
    exact (canonical18053 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1084 + difference 3 1) (sourceB1084 + difference 1 3) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA1084 + difference 3 1) (sourceB1084 + difference 1 3) sourceC1084) = raw18054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18054; decide +kernel
    rw [ha]
    exact (canonical18054 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1084 + difference 3 2) (sourceB1084 + difference 2 3) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5467) := by
    have ha : (tripleCharges (sourceA1084 + difference 3 2) (sourceB1084 + difference 2 3) sourceC1084) = raw18055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18055; decide +kernel
    rw [ha]
    exact (canonical18055 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1084 + difference 3 4) (sourceB1084 + difference 4 3) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1084 + difference 3 4) (sourceB1084 + difference 4 3) sourceC1084) = raw18056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18056; decide +kernel
    rw [ha]
    exact (canonical18056 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1084 + difference 3 5) (sourceB1084 + difference 5 3) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1084 + difference 3 5) (sourceB1084 + difference 5 3) sourceC1084) = raw18057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18057; decide +kernel
    rw [ha]
    exact (canonical18057 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1084 + difference 4 0) (sourceB1084 + difference 0 4) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5023) := by
    have ha : (tripleCharges (sourceA1084 + difference 4 0) (sourceB1084 + difference 0 4) sourceC1084) = raw18058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18058; decide +kernel
    rw [ha]
    exact (canonical18058 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1084 + difference 4 1) (sourceB1084 + difference 1 4) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5021) := by
    have ha : (tripleCharges (sourceA1084 + difference 4 1) (sourceB1084 + difference 1 4) sourceC1084) = raw18059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18059; decide +kernel
    rw [ha]
    exact (canonical18059 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1084 + difference 4 2) (sourceB1084 + difference 2 4) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA1084 + difference 4 2) (sourceB1084 + difference 2 4) sourceC1084) = raw18060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18060; decide +kernel
    rw [ha]
    exact (canonical18060 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1084 + difference 4 3) (sourceB1084 + difference 3 4) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA1084 + difference 4 3) (sourceB1084 + difference 3 4) sourceC1084) = raw18061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18061; decide +kernel
    rw [ha]
    exact (canonical18061 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1084 + difference 4 5) (sourceB1084 + difference 5 4) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA1084 + difference 4 5) (sourceB1084 + difference 5 4) sourceC1084) = raw18062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18062; decide +kernel
    rw [ha]
    exact (canonical18062 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1084 + difference 5 0) (sourceB1084 + difference 0 5) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5021) := by
    have ha : (tripleCharges (sourceA1084 + difference 5 0) (sourceB1084 + difference 0 5) sourceC1084) = raw18063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18063; decide +kernel
    rw [ha]
    exact (canonical18063 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1084 + difference 5 1) (sourceB1084 + difference 1 5) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5023) := by
    have ha : (tripleCharges (sourceA1084 + difference 5 1) (sourceB1084 + difference 1 5) sourceC1084) = raw18064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18064; decide +kernel
    rw [ha]
    exact (canonical18064 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1084 + difference 5 2) (sourceB1084 + difference 2 5) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA1084 + difference 5 2) (sourceB1084 + difference 2 5) sourceC1084) = raw18065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18065; decide +kernel
    rw [ha]
    exact (canonical18065 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1084 + difference 5 3) (sourceB1084 + difference 3 5) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA1084 + difference 5 3) (sourceB1084 + difference 3 5) sourceC1084) = raw18066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18066; decide +kernel
    rw [ha]
    exact (canonical18066 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1084 + difference 5 4) (sourceB1084 + difference 4 5) sourceC1084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA1084 + difference 5 4) (sourceB1084 + difference 4 5) sourceC1084) = raw18067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1084 sourceB1084 sourceC1084 difference raw18067; decide +kernel
    rw [ha]
    exact (canonical18067 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1084 sourceB1084 sourceC1084
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1084, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1085 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1085 : Charge := ![0, 2, 0, 0, -2, 0]
def sourceC1085 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm1085 : Integer.Sparse Master := [(Sum.inr 5198, 4), (Sum.inr 5201, 1), (Sum.inr 5206, 2), (Sum.inr 5233, 4), (Sum.inr 5235, 1), (Sum.inr 5291, 2), (Sum.inr 5300, 2), (Sum.inr 5420, 2), (Sum.inr 5432, 4), (Sum.inr 5441, 1), (Sum.inr 5446, 4), (Sum.inr 5451, 2), (Sum.inr 5475, 1)]

theorem sourceEq1085 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1085 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1085 + difference 0 1) (sourceB1085 + difference 1 0) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA1085 + difference 0 1) (sourceB1085 + difference 1 0) sourceC1085) = raw18068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18068; decide +kernel
    rw [ha]
    exact (canonical18068 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1085 + difference 0 2) (sourceB1085 + difference 2 0) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1085 + difference 0 2) (sourceB1085 + difference 2 0) sourceC1085) = raw18069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18069; decide +kernel
    rw [ha]
    exact (canonical18069 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1085 + difference 0 3) (sourceB1085 + difference 3 0) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1085 + difference 0 3) (sourceB1085 + difference 3 0) sourceC1085) = raw18070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18070; decide +kernel
    rw [ha]
    exact (canonical18070 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1085 + difference 0 4) (sourceB1085 + difference 4 0) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1085 + difference 0 4) (sourceB1085 + difference 4 0) sourceC1085) = raw18071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18071; decide +kernel
    rw [ha]
    exact (canonical18071 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1085 + difference 0 5) (sourceB1085 + difference 5 0) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5475) := by
    have ha : (tripleCharges (sourceA1085 + difference 0 5) (sourceB1085 + difference 5 0) sourceC1085) = raw18072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18072; decide +kernel
    rw [ha]
    exact (canonical18072 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1085 + difference 1 0) (sourceB1085 + difference 0 1) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA1085 + difference 1 0) (sourceB1085 + difference 0 1) sourceC1085) = raw4833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw4833; decide +kernel
    rw [ha]
    exact (canonical4833 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1085 + difference 1 2) (sourceB1085 + difference 2 1) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1085 + difference 1 2) (sourceB1085 + difference 2 1) sourceC1085) = raw9510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw9510; decide +kernel
    rw [ha]
    exact (canonical9510 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1085 + difference 1 3) (sourceB1085 + difference 3 1) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1085 + difference 1 3) (sourceB1085 + difference 3 1) sourceC1085) = raw9511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw9511; decide +kernel
    rw [ha]
    exact (canonical9511 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1085 + difference 1 4) (sourceB1085 + difference 4 1) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA1085 + difference 1 4) (sourceB1085 + difference 4 1) sourceC1085) = raw4813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw4813; decide +kernel
    rw [ha]
    exact (canonical4813 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1085 + difference 1 5) (sourceB1085 + difference 5 1) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1085 + difference 1 5) (sourceB1085 + difference 5 1) sourceC1085) = raw9512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw9512; decide +kernel
    rw [ha]
    exact (canonical9512 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1085 + difference 2 0) (sourceB1085 + difference 0 2) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA1085 + difference 2 0) (sourceB1085 + difference 0 2) sourceC1085) = raw9518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw9518; decide +kernel
    rw [ha]
    exact (canonical9518 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1085 + difference 2 1) (sourceB1085 + difference 1 2) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA1085 + difference 2 1) (sourceB1085 + difference 1 2) sourceC1085) = raw18073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18073; decide +kernel
    rw [ha]
    exact (canonical18073 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1085 + difference 2 3) (sourceB1085 + difference 3 2) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5420) := by
    have ha : (tripleCharges (sourceA1085 + difference 2 3) (sourceB1085 + difference 3 2) sourceC1085) = raw18074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18074; decide +kernel
    rw [ha]
    exact (canonical18074 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1085 + difference 2 4) (sourceB1085 + difference 4 2) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1085 + difference 2 4) (sourceB1085 + difference 4 2) sourceC1085) = raw18075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18075; decide +kernel
    rw [ha]
    exact (canonical18075 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1085 + difference 2 5) (sourceB1085 + difference 5 2) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1085 + difference 2 5) (sourceB1085 + difference 5 2) sourceC1085) = raw18076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18076; decide +kernel
    rw [ha]
    exact (canonical18076 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1085 + difference 3 0) (sourceB1085 + difference 0 3) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA1085 + difference 3 0) (sourceB1085 + difference 0 3) sourceC1085) = raw9522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw9522; decide +kernel
    rw [ha]
    exact (canonical9522 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1085 + difference 3 1) (sourceB1085 + difference 1 3) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA1085 + difference 3 1) (sourceB1085 + difference 1 3) sourceC1085) = raw18077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18077; decide +kernel
    rw [ha]
    exact (canonical18077 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1085 + difference 3 2) (sourceB1085 + difference 2 3) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5420) := by
    have ha : (tripleCharges (sourceA1085 + difference 3 2) (sourceB1085 + difference 2 3) sourceC1085) = raw18078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18078; decide +kernel
    rw [ha]
    exact (canonical18078 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1085 + difference 3 4) (sourceB1085 + difference 4 3) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1085 + difference 3 4) (sourceB1085 + difference 4 3) sourceC1085) = raw18079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18079; decide +kernel
    rw [ha]
    exact (canonical18079 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1085 + difference 3 5) (sourceB1085 + difference 5 3) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1085 + difference 3 5) (sourceB1085 + difference 5 3) sourceC1085) = raw18080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18080; decide +kernel
    rw [ha]
    exact (canonical18080 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1085 + difference 4 0) (sourceB1085 + difference 0 4) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA1085 + difference 4 0) (sourceB1085 + difference 0 4) sourceC1085) = raw9526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw9526; decide +kernel
    rw [ha]
    exact (canonical9526 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1085 + difference 4 1) (sourceB1085 + difference 1 4) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5235) := by
    have ha : (tripleCharges (sourceA1085 + difference 4 1) (sourceB1085 + difference 1 4) sourceC1085) = raw18081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18081; decide +kernel
    rw [ha]
    exact (canonical18081 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1085 + difference 4 2) (sourceB1085 + difference 2 4) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA1085 + difference 4 2) (sourceB1085 + difference 2 4) sourceC1085) = raw18082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18082; decide +kernel
    rw [ha]
    exact (canonical18082 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1085 + difference 4 3) (sourceB1085 + difference 3 4) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA1085 + difference 4 3) (sourceB1085 + difference 3 4) sourceC1085) = raw18083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18083; decide +kernel
    rw [ha]
    exact (canonical18083 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1085 + difference 4 5) (sourceB1085 + difference 5 4) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA1085 + difference 4 5) (sourceB1085 + difference 5 4) sourceC1085) = raw18084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18084; decide +kernel
    rw [ha]
    exact (canonical18084 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1085 + difference 5 0) (sourceB1085 + difference 0 5) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5201) := by
    have ha : (tripleCharges (sourceA1085 + difference 5 0) (sourceB1085 + difference 0 5) sourceC1085) = raw4830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw4830; decide +kernel
    rw [ha]
    exact (canonical4830 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1085 + difference 5 1) (sourceB1085 + difference 1 5) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA1085 + difference 5 1) (sourceB1085 + difference 1 5) sourceC1085) = raw18085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18085; decide +kernel
    rw [ha]
    exact (canonical18085 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1085 + difference 5 2) (sourceB1085 + difference 2 5) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA1085 + difference 5 2) (sourceB1085 + difference 2 5) sourceC1085) = raw18086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18086; decide +kernel
    rw [ha]
    exact (canonical18086 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1085 + difference 5 3) (sourceB1085 + difference 3 5) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA1085 + difference 5 3) (sourceB1085 + difference 3 5) sourceC1085) = raw18087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw18087; decide +kernel
    rw [ha]
    exact (canonical18087 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1085 + difference 5 4) (sourceB1085 + difference 4 5) sourceC1085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA1085 + difference 5 4) (sourceB1085 + difference 4 5) sourceC1085) = raw4809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1085 sourceB1085 sourceC1085 difference raw4809; decide +kernel
    rw [ha]
    exact (canonical4809 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1085 sourceB1085 sourceC1085
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1085, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1086 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1086 : Charge := ![0, 2, 0, 0, -2, 0]
def sourceC1086 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm1086 : Integer.Sparse Master := [(Sum.inr 2678, 4), (Sum.inr 2680, 1), (Sum.inr 2687, 2), (Sum.inr 2774, 2), (Sum.inr 3570, 4), (Sum.inr 3579, 1), (Sum.inr 3582, 2), (Sum.inr 3850, 4), (Sum.inr 3860, 1), (Sum.inr 3870, 2), (Sum.inr 3881, 4), (Sum.inr 3888, 2), (Sum.inr 4004, 1)]

theorem sourceEq1086 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1086 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1086 + difference 0 1) (sourceB1086 + difference 1 0) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA1086 + difference 0 1) (sourceB1086 + difference 1 0) sourceC1086) = raw18088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18088; decide +kernel
    rw [ha]
    exact (canonical18088 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1086 + difference 0 2) (sourceB1086 + difference 2 0) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1086 + difference 0 2) (sourceB1086 + difference 2 0) sourceC1086) = raw18089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18089; decide +kernel
    rw [ha]
    exact (canonical18089 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1086 + difference 0 3) (sourceB1086 + difference 3 0) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1086 + difference 0 3) (sourceB1086 + difference 3 0) sourceC1086) = raw18090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18090; decide +kernel
    rw [ha]
    exact (canonical18090 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1086 + difference 0 4) (sourceB1086 + difference 4 0) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA1086 + difference 0 4) (sourceB1086 + difference 4 0) sourceC1086) = raw18091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18091; decide +kernel
    rw [ha]
    exact (canonical18091 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1086 + difference 0 5) (sourceB1086 + difference 5 0) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4004) := by
    have ha : (tripleCharges (sourceA1086 + difference 0 5) (sourceB1086 + difference 5 0) sourceC1086) = raw18092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18092; decide +kernel
    rw [ha]
    exact (canonical18092 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1086 + difference 1 0) (sourceB1086 + difference 0 1) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA1086 + difference 1 0) (sourceB1086 + difference 0 1) sourceC1086) = raw4893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw4893; decide +kernel
    rw [ha]
    exact (canonical4893 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1086 + difference 1 2) (sourceB1086 + difference 2 1) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA1086 + difference 1 2) (sourceB1086 + difference 2 1) sourceC1086) = raw9554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw9554; decide +kernel
    rw [ha]
    exact (canonical9554 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1086 + difference 1 3) (sourceB1086 + difference 3 1) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA1086 + difference 1 3) (sourceB1086 + difference 3 1) sourceC1086) = raw9555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw9555; decide +kernel
    rw [ha]
    exact (canonical9555 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1086 + difference 1 4) (sourceB1086 + difference 4 1) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3860) := by
    have ha : (tripleCharges (sourceA1086 + difference 1 4) (sourceB1086 + difference 4 1) sourceC1086) = raw4873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw4873; decide +kernel
    rw [ha]
    exact (canonical4873 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1086 + difference 1 5) (sourceB1086 + difference 5 1) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA1086 + difference 1 5) (sourceB1086 + difference 5 1) sourceC1086) = raw9556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw9556; decide +kernel
    rw [ha]
    exact (canonical9556 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1086 + difference 2 0) (sourceB1086 + difference 0 2) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA1086 + difference 2 0) (sourceB1086 + difference 0 2) sourceC1086) = raw9562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw9562; decide +kernel
    rw [ha]
    exact (canonical9562 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1086 + difference 2 1) (sourceB1086 + difference 1 2) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA1086 + difference 2 1) (sourceB1086 + difference 1 2) sourceC1086) = raw18093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18093; decide +kernel
    rw [ha]
    exact (canonical18093 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1086 + difference 2 3) (sourceB1086 + difference 3 2) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3870) := by
    have ha : (tripleCharges (sourceA1086 + difference 2 3) (sourceB1086 + difference 3 2) sourceC1086) = raw18094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18094; decide +kernel
    rw [ha]
    exact (canonical18094 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1086 + difference 2 4) (sourceB1086 + difference 4 2) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA1086 + difference 2 4) (sourceB1086 + difference 4 2) sourceC1086) = raw18095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18095; decide +kernel
    rw [ha]
    exact (canonical18095 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1086 + difference 2 5) (sourceB1086 + difference 5 2) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1086 + difference 2 5) (sourceB1086 + difference 5 2) sourceC1086) = raw18096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18096; decide +kernel
    rw [ha]
    exact (canonical18096 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1086 + difference 3 0) (sourceB1086 + difference 0 3) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA1086 + difference 3 0) (sourceB1086 + difference 0 3) sourceC1086) = raw9566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw9566; decide +kernel
    rw [ha]
    exact (canonical9566 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1086 + difference 3 1) (sourceB1086 + difference 1 3) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA1086 + difference 3 1) (sourceB1086 + difference 1 3) sourceC1086) = raw18097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18097; decide +kernel
    rw [ha]
    exact (canonical18097 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1086 + difference 3 2) (sourceB1086 + difference 2 3) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3870) := by
    have ha : (tripleCharges (sourceA1086 + difference 3 2) (sourceB1086 + difference 2 3) sourceC1086) = raw18098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18098; decide +kernel
    rw [ha]
    exact (canonical18098 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1086 + difference 3 4) (sourceB1086 + difference 4 3) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA1086 + difference 3 4) (sourceB1086 + difference 4 3) sourceC1086) = raw18099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18099; decide +kernel
    rw [ha]
    exact (canonical18099 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1086 + difference 3 5) (sourceB1086 + difference 5 3) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1086 + difference 3 5) (sourceB1086 + difference 5 3) sourceC1086) = raw18100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18100; decide +kernel
    rw [ha]
    exact (canonical18100 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1086 + difference 4 0) (sourceB1086 + difference 0 4) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA1086 + difference 4 0) (sourceB1086 + difference 0 4) sourceC1086) = raw9570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw9570; decide +kernel
    rw [ha]
    exact (canonical9570 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1086 + difference 4 1) (sourceB1086 + difference 1 4) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2680) := by
    have ha : (tripleCharges (sourceA1086 + difference 4 1) (sourceB1086 + difference 1 4) sourceC1086) = raw18101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18101; decide +kernel
    rw [ha]
    exact (canonical18101 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1086 + difference 4 2) (sourceB1086 + difference 2 4) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA1086 + difference 4 2) (sourceB1086 + difference 2 4) sourceC1086) = raw18102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18102; decide +kernel
    rw [ha]
    exact (canonical18102 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1086 + difference 4 3) (sourceB1086 + difference 3 4) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA1086 + difference 4 3) (sourceB1086 + difference 3 4) sourceC1086) = raw18103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18103; decide +kernel
    rw [ha]
    exact (canonical18103 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1086 + difference 4 5) (sourceB1086 + difference 5 4) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA1086 + difference 4 5) (sourceB1086 + difference 5 4) sourceC1086) = raw18104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18104; decide +kernel
    rw [ha]
    exact (canonical18104 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1086 + difference 5 0) (sourceB1086 + difference 0 5) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3579) := by
    have ha : (tripleCharges (sourceA1086 + difference 5 0) (sourceB1086 + difference 0 5) sourceC1086) = raw4890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw4890; decide +kernel
    rw [ha]
    exact (canonical4890 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1086 + difference 5 1) (sourceB1086 + difference 1 5) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA1086 + difference 5 1) (sourceB1086 + difference 1 5) sourceC1086) = raw18105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18105; decide +kernel
    rw [ha]
    exact (canonical18105 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1086 + difference 5 2) (sourceB1086 + difference 2 5) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA1086 + difference 5 2) (sourceB1086 + difference 2 5) sourceC1086) = raw18106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18106; decide +kernel
    rw [ha]
    exact (canonical18106 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1086 + difference 5 3) (sourceB1086 + difference 3 5) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA1086 + difference 5 3) (sourceB1086 + difference 3 5) sourceC1086) = raw18107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw18107; decide +kernel
    rw [ha]
    exact (canonical18107 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1086 + difference 5 4) (sourceB1086 + difference 4 5) sourceC1086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA1086 + difference 5 4) (sourceB1086 + difference 4 5) sourceC1086) = raw4869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1086 sourceB1086 sourceC1086 difference raw4869; decide +kernel
    rw [ha]
    exact (canonical4869 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1086 sourceB1086 sourceC1086
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1086, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1087 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1087 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1087 : Charge := ![0, 2, 0, 0, -2, 0]
def sourceForm1087 : Integer.Sparse Master := [(Sum.inr 4860, 4), (Sum.inr 4862, 1), (Sum.inr 4874, 4), (Sum.inr 5384, 8), (Sum.inr 5389, 2), (Sum.inr 5398, 2), (Sum.inr 5443, 4), (Sum.inr 5448, 4), (Sum.inr 5491, 1)]

theorem sourceEq1087 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1087 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1087 + difference 0 1) (sourceB1087 + difference 1 0) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1087 + difference 0 1) (sourceB1087 + difference 1 0) sourceC1087) = raw18108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18108; decide +kernel
    rw [ha]
    exact (canonical18108 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1087 + difference 0 2) (sourceB1087 + difference 2 0) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1087 + difference 0 2) (sourceB1087 + difference 2 0) sourceC1087) = raw18109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18109; decide +kernel
    rw [ha]
    exact (canonical18109 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1087 + difference 0 3) (sourceB1087 + difference 3 0) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1087 + difference 0 3) (sourceB1087 + difference 3 0) sourceC1087) = raw18110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18110; decide +kernel
    rw [ha]
    exact (canonical18110 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1087 + difference 0 4) (sourceB1087 + difference 4 0) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1087 + difference 0 4) (sourceB1087 + difference 4 0) sourceC1087) = raw18111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18111; decide +kernel
    rw [ha]
    exact (canonical18111 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1087 + difference 0 5) (sourceB1087 + difference 5 0) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1087 + difference 0 5) (sourceB1087 + difference 5 0) sourceC1087) = raw18112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18112; decide +kernel
    rw [ha]
    exact (canonical18112 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1087 + difference 1 0) (sourceB1087 + difference 0 1) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA1087 + difference 1 0) (sourceB1087 + difference 0 1) sourceC1087) = raw18113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18113; decide +kernel
    rw [ha]
    exact (canonical18113 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1087 + difference 1 2) (sourceB1087 + difference 2 1) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1087 + difference 1 2) (sourceB1087 + difference 2 1) sourceC1087) = raw18114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18114; decide +kernel
    rw [ha]
    exact (canonical18114 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1087 + difference 1 3) (sourceB1087 + difference 3 1) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1087 + difference 1 3) (sourceB1087 + difference 3 1) sourceC1087) = raw18115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18115; decide +kernel
    rw [ha]
    exact (canonical18115 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1087 + difference 1 4) (sourceB1087 + difference 4 1) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5389) := by
    have ha : (tripleCharges (sourceA1087 + difference 1 4) (sourceB1087 + difference 4 1) sourceC1087) = raw18116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18116; decide +kernel
    rw [ha]
    exact (canonical18116 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1087 + difference 1 5) (sourceB1087 + difference 5 1) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1087 + difference 1 5) (sourceB1087 + difference 5 1) sourceC1087) = raw18117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18117; decide +kernel
    rw [ha]
    exact (canonical18117 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1087 + difference 2 0) (sourceB1087 + difference 0 2) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA1087 + difference 2 0) (sourceB1087 + difference 0 2) sourceC1087) = raw18118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18118; decide +kernel
    rw [ha]
    exact (canonical18118 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1087 + difference 2 1) (sourceB1087 + difference 1 2) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1087 + difference 2 1) (sourceB1087 + difference 1 2) sourceC1087) = raw18119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18119; decide +kernel
    rw [ha]
    exact (canonical18119 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1087 + difference 2 3) (sourceB1087 + difference 3 2) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5398) := by
    have ha : (tripleCharges (sourceA1087 + difference 2 3) (sourceB1087 + difference 3 2) sourceC1087) = raw18120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18120; decide +kernel
    rw [ha]
    exact (canonical18120 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1087 + difference 2 4) (sourceB1087 + difference 4 2) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1087 + difference 2 4) (sourceB1087 + difference 4 2) sourceC1087) = raw18121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18121; decide +kernel
    rw [ha]
    exact (canonical18121 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1087 + difference 2 5) (sourceB1087 + difference 5 2) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1087 + difference 2 5) (sourceB1087 + difference 5 2) sourceC1087) = raw18122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18122; decide +kernel
    rw [ha]
    exact (canonical18122 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1087 + difference 3 0) (sourceB1087 + difference 0 3) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA1087 + difference 3 0) (sourceB1087 + difference 0 3) sourceC1087) = raw18123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18123; decide +kernel
    rw [ha]
    exact (canonical18123 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1087 + difference 3 1) (sourceB1087 + difference 1 3) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1087 + difference 3 1) (sourceB1087 + difference 1 3) sourceC1087) = raw18124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18124; decide +kernel
    rw [ha]
    exact (canonical18124 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1087 + difference 3 2) (sourceB1087 + difference 2 3) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5398) := by
    have ha : (tripleCharges (sourceA1087 + difference 3 2) (sourceB1087 + difference 2 3) sourceC1087) = raw18125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18125; decide +kernel
    rw [ha]
    exact (canonical18125 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1087 + difference 3 4) (sourceB1087 + difference 4 3) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1087 + difference 3 4) (sourceB1087 + difference 4 3) sourceC1087) = raw18126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18126; decide +kernel
    rw [ha]
    exact (canonical18126 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1087 + difference 3 5) (sourceB1087 + difference 5 3) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1087 + difference 3 5) (sourceB1087 + difference 5 3) sourceC1087) = raw18127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18127; decide +kernel
    rw [ha]
    exact (canonical18127 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1087 + difference 4 0) (sourceB1087 + difference 0 4) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA1087 + difference 4 0) (sourceB1087 + difference 0 4) sourceC1087) = raw18128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18128; decide +kernel
    rw [ha]
    exact (canonical18128 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1087 + difference 4 1) (sourceB1087 + difference 1 4) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5389) := by
    have ha : (tripleCharges (sourceA1087 + difference 4 1) (sourceB1087 + difference 1 4) sourceC1087) = raw18129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18129; decide +kernel
    rw [ha]
    exact (canonical18129 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1087 + difference 4 2) (sourceB1087 + difference 2 4) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1087 + difference 4 2) (sourceB1087 + difference 2 4) sourceC1087) = raw18130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18130; decide +kernel
    rw [ha]
    exact (canonical18130 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1087 + difference 4 3) (sourceB1087 + difference 3 4) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1087 + difference 4 3) (sourceB1087 + difference 3 4) sourceC1087) = raw18131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18131; decide +kernel
    rw [ha]
    exact (canonical18131 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1087 + difference 4 5) (sourceB1087 + difference 5 4) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1087 + difference 4 5) (sourceB1087 + difference 5 4) sourceC1087) = raw18132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18132; decide +kernel
    rw [ha]
    exact (canonical18132 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1087 + difference 5 0) (sourceB1087 + difference 0 5) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4862) := by
    have ha : (tripleCharges (sourceA1087 + difference 5 0) (sourceB1087 + difference 0 5) sourceC1087) = raw18133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18133; decide +kernel
    rw [ha]
    exact (canonical18133 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1087 + difference 5 1) (sourceB1087 + difference 1 5) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA1087 + difference 5 1) (sourceB1087 + difference 1 5) sourceC1087) = raw18134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18134; decide +kernel
    rw [ha]
    exact (canonical18134 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1087 + difference 5 2) (sourceB1087 + difference 2 5) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA1087 + difference 5 2) (sourceB1087 + difference 2 5) sourceC1087) = raw18135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18135; decide +kernel
    rw [ha]
    exact (canonical18135 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1087 + difference 5 3) (sourceB1087 + difference 3 5) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA1087 + difference 5 3) (sourceB1087 + difference 3 5) sourceC1087) = raw18136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18136; decide +kernel
    rw [ha]
    exact (canonical18136 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1087 + difference 5 4) (sourceB1087 + difference 4 5) sourceC1087) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA1087 + difference 5 4) (sourceB1087 + difference 4 5) sourceC1087) = raw18137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1087 sourceB1087 sourceC1087 difference raw18137; decide +kernel
    rw [ha]
    exact (canonical18137 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1087 sourceB1087 sourceC1087
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1087, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
