import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical117
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical152
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical164
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical174
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical177
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical178

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1472 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1472 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC1472 : Charge := ![2, -1, 1, 1, -2, -1]
def sourceForm1472 : Integer.Sparse Master := [(Sum.inr 1196, 1), (Sum.inr 2452, 2), (Sum.inr 2609, 1), (Sum.inr 2694, 1), (Sum.inr 2695, 1), (Sum.inr 4090, -1)]

theorem sourceEq1472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1472 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1472 + difference 0 0) (sourceB1472 + difference 0 0) sourceC1472) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1196) := by
    have ha : (tripleCharges (sourceA1472 + difference 0 0) (sourceB1472 + difference 0 0) sourceC1472) = raw22464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1472 sourceB1472 sourceC1472 difference raw22464; decide +kernel
    rw [ha]
    exact (canonical22464 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1472 + difference 0 1) (sourceB1472 + difference 1 0) sourceC1472) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2609) := by
    have ha : (tripleCharges (sourceA1472 + difference 0 1) (sourceB1472 + difference 1 0) sourceC1472) = raw22465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1472 sourceB1472 sourceC1472 difference raw22465; decide +kernel
    rw [ha]
    exact (canonical22465 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1472 + difference 0 2) (sourceB1472 + difference 2 0) sourceC1472) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA1472 + difference 0 2) (sourceB1472 + difference 2 0) sourceC1472) = raw22466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1472 sourceB1472 sourceC1472 difference raw22466; decide +kernel
    rw [ha]
    exact (canonical22466 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1472 + difference 0 3) (sourceB1472 + difference 3 0) sourceC1472) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA1472 + difference 0 3) (sourceB1472 + difference 3 0) sourceC1472) = raw22467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1472 sourceB1472 sourceC1472 difference raw22467; decide +kernel
    rw [ha]
    exact (canonical22467 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1472 + difference 0 4) (sourceB1472 + difference 4 0) sourceC1472) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2695) := by
    have ha : (tripleCharges (sourceA1472 + difference 0 4) (sourceB1472 + difference 4 0) sourceC1472) = raw22468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1472 sourceB1472 sourceC1472 difference raw22468; decide +kernel
    rw [ha]
    exact (canonical22468 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1472 + difference 0 5) (sourceB1472 + difference 5 0) sourceC1472) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA1472 + difference 0 5) (sourceB1472 + difference 5 0) sourceC1472) = raw22469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1472 sourceB1472 sourceC1472 difference raw22469; decide +kernel
    rw [ha]
    exact (canonical22469 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1472 + sourceB1472) sourceC1472) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1472 + sourceB1472) sourceC1472) = raw22470 := by
      apply Matrix.ext; unfold doubleCharges sourceA1472 sourceB1472 sourceC1472 raw22470; decide +kernel
    rw [ha]
    exact (canonical22470 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1472 sourceB1472 sourceC1472
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1472, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1473 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1473 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1473 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm1473 : Integer.Sparse Master := [(Sum.inr 4185, 3), (Sum.inr 4190, 1), (Sum.inr 4192, 1), (Sum.inr 4553, 6), (Sum.inr 4557, 3), (Sum.inr 4559, 3), (Sum.inr 4619, 3), (Sum.inr 4621, 1), (Sum.inr 4623, 3), (Sum.inr 4625, 1), (Sum.inr 5176, 3), (Sum.inr 5308, 1), (Sum.inr 5310, 1)]

theorem sourceEq1473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1473 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1473 + difference 0 1) (sourceB1473 + difference 1 0) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA1473 + difference 0 1) (sourceB1473 + difference 1 0) sourceC1473) = raw10233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw10233; decide +kernel
    rw [ha]
    exact (canonical10233 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1473 + difference 0 2) (sourceB1473 + difference 2 0) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA1473 + difference 0 2) (sourceB1473 + difference 2 0) sourceC1473) = raw10234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw10234; decide +kernel
    rw [ha]
    exact (canonical10234 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1473 + difference 0 3) (sourceB1473 + difference 3 0) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA1473 + difference 0 3) (sourceB1473 + difference 3 0) sourceC1473) = raw10235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw10235; decide +kernel
    rw [ha]
    exact (canonical10235 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1473 + difference 0 4) (sourceB1473 + difference 4 0) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA1473 + difference 0 4) (sourceB1473 + difference 4 0) sourceC1473) = raw5082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw5082; decide +kernel
    rw [ha]
    exact (canonical5082 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1473 + difference 0 5) (sourceB1473 + difference 5 0) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA1473 + difference 0 5) (sourceB1473 + difference 5 0) sourceC1473) = raw10236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw10236; decide +kernel
    rw [ha]
    exact (canonical10236 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1473 + difference 1 0) (sourceB1473 + difference 0 1) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4185) := by
    have ha : (tripleCharges (sourceA1473 + difference 1 0) (sourceB1473 + difference 0 1) sourceC1473) = raw22471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22471; decide +kernel
    rw [ha]
    exact (canonical22471 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1473 + difference 1 2) (sourceB1473 + difference 2 1) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA1473 + difference 1 2) (sourceB1473 + difference 2 1) sourceC1473) = raw22472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22472; decide +kernel
    rw [ha]
    exact (canonical22472 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1473 + difference 1 3) (sourceB1473 + difference 3 1) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA1473 + difference 1 3) (sourceB1473 + difference 3 1) sourceC1473) = raw22473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22473; decide +kernel
    rw [ha]
    exact (canonical22473 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1473 + difference 1 4) (sourceB1473 + difference 4 1) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1473 + difference 1 4) (sourceB1473 + difference 4 1) sourceC1473) = raw10220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw10220; decide +kernel
    rw [ha]
    exact (canonical10220 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1473 + difference 1 5) (sourceB1473 + difference 5 1) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1473 + difference 1 5) (sourceB1473 + difference 5 1) sourceC1473) = raw22474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22474; decide +kernel
    rw [ha]
    exact (canonical22474 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1473 + difference 2 0) (sourceB1473 + difference 0 2) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4185) := by
    have ha : (tripleCharges (sourceA1473 + difference 2 0) (sourceB1473 + difference 0 2) sourceC1473) = raw22475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22475; decide +kernel
    rw [ha]
    exact (canonical22475 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1473 + difference 2 1) (sourceB1473 + difference 1 2) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA1473 + difference 2 1) (sourceB1473 + difference 1 2) sourceC1473) = raw22476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22476; decide +kernel
    rw [ha]
    exact (canonical22476 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1473 + difference 2 3) (sourceB1473 + difference 3 2) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA1473 + difference 2 3) (sourceB1473 + difference 3 2) sourceC1473) = raw22477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22477; decide +kernel
    rw [ha]
    exact (canonical22477 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1473 + difference 2 4) (sourceB1473 + difference 4 2) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1473 + difference 2 4) (sourceB1473 + difference 4 2) sourceC1473) = raw10224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw10224; decide +kernel
    rw [ha]
    exact (canonical10224 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1473 + difference 2 5) (sourceB1473 + difference 5 2) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1473 + difference 2 5) (sourceB1473 + difference 5 2) sourceC1473) = raw22478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22478; decide +kernel
    rw [ha]
    exact (canonical22478 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1473 + difference 3 0) (sourceB1473 + difference 0 3) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4185) := by
    have ha : (tripleCharges (sourceA1473 + difference 3 0) (sourceB1473 + difference 0 3) sourceC1473) = raw22479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22479; decide +kernel
    rw [ha]
    exact (canonical22479 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1473 + difference 3 1) (sourceB1473 + difference 1 3) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA1473 + difference 3 1) (sourceB1473 + difference 1 3) sourceC1473) = raw22480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22480; decide +kernel
    rw [ha]
    exact (canonical22480 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1473 + difference 3 2) (sourceB1473 + difference 2 3) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA1473 + difference 3 2) (sourceB1473 + difference 2 3) sourceC1473) = raw22481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22481; decide +kernel
    rw [ha]
    exact (canonical22481 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1473 + difference 3 4) (sourceB1473 + difference 4 3) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1473 + difference 3 4) (sourceB1473 + difference 4 3) sourceC1473) = raw10228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw10228; decide +kernel
    rw [ha]
    exact (canonical10228 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1473 + difference 3 5) (sourceB1473 + difference 5 3) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1473 + difference 3 5) (sourceB1473 + difference 5 3) sourceC1473) = raw12097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw12097; decide +kernel
    rw [ha]
    exact (canonical12097 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1473 + difference 4 0) (sourceB1473 + difference 0 4) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4190) := by
    have ha : (tripleCharges (sourceA1473 + difference 4 0) (sourceB1473 + difference 0 4) sourceC1473) = raw22482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22482; decide +kernel
    rw [ha]
    exact (canonical22482 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1473 + difference 4 1) (sourceB1473 + difference 1 4) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4557) := by
    have ha : (tripleCharges (sourceA1473 + difference 4 1) (sourceB1473 + difference 1 4) sourceC1473) = raw22483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22483; decide +kernel
    rw [ha]
    exact (canonical22483 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1473 + difference 4 2) (sourceB1473 + difference 2 4) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4557) := by
    have ha : (tripleCharges (sourceA1473 + difference 4 2) (sourceB1473 + difference 2 4) sourceC1473) = raw22484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22484; decide +kernel
    rw [ha]
    exact (canonical22484 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1473 + difference 4 3) (sourceB1473 + difference 3 4) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4557) := by
    have ha : (tripleCharges (sourceA1473 + difference 4 3) (sourceB1473 + difference 3 4) sourceC1473) = raw22485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22485; decide +kernel
    rw [ha]
    exact (canonical22485 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1473 + difference 4 5) (sourceB1473 + difference 5 4) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA1473 + difference 4 5) (sourceB1473 + difference 5 4) sourceC1473) = raw22486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw22486; decide +kernel
    rw [ha]
    exact (canonical22486 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1473 + difference 5 0) (sourceB1473 + difference 0 5) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4192) := by
    have ha : (tripleCharges (sourceA1473 + difference 5 0) (sourceB1473 + difference 0 5) sourceC1473) = raw20360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw20360; decide +kernel
    rw [ha]
    exact (canonical20360 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1473 + difference 5 1) (sourceB1473 + difference 1 5) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4559) := by
    have ha : (tripleCharges (sourceA1473 + difference 5 1) (sourceB1473 + difference 1 5) sourceC1473) = raw20361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw20361; decide +kernel
    rw [ha]
    exact (canonical20361 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1473 + difference 5 2) (sourceB1473 + difference 2 5) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4559) := by
    have ha : (tripleCharges (sourceA1473 + difference 5 2) (sourceB1473 + difference 2 5) sourceC1473) = raw20362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw20362; decide +kernel
    rw [ha]
    exact (canonical20362 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1473 + difference 5 3) (sourceB1473 + difference 3 5) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4559) := by
    have ha : (tripleCharges (sourceA1473 + difference 5 3) (sourceB1473 + difference 3 5) sourceC1473) = raw20363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw20363; decide +kernel
    rw [ha]
    exact (canonical20363 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1473 + difference 5 4) (sourceB1473 + difference 4 5) sourceC1473) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1473 + difference 5 4) (sourceB1473 + difference 4 5) sourceC1473) = raw5078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1473 sourceB1473 sourceC1473 difference raw5078; decide +kernel
    rw [ha]
    exact (canonical5078 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1473 sourceB1473 sourceC1473
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1473, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1474 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1474 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1474 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm1474 : Integer.Sparse Master := [(Sum.inr 613, 3), (Sum.inr 618, 1), (Sum.inr 620, 1), (Sum.inr 1138, 6), (Sum.inr 1143, 3), (Sum.inr 1145, 3), (Sum.inr 1294, 3), (Sum.inr 1297, 1), (Sum.inr 1305, 3), (Sum.inr 1307, 1), (Sum.inr 2968, 3), (Sum.inr 3121, 1), (Sum.inr 3124, 1)]

theorem sourceEq1474 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1474 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1474 + difference 0 1) (sourceB1474 + difference 1 0) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA1474 + difference 0 1) (sourceB1474 + difference 1 0) sourceC1474) = raw22487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22487; decide +kernel
    rw [ha]
    exact (canonical22487 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1474 + difference 0 2) (sourceB1474 + difference 2 0) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA1474 + difference 0 2) (sourceB1474 + difference 2 0) sourceC1474) = raw22488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22488; decide +kernel
    rw [ha]
    exact (canonical22488 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1474 + difference 0 3) (sourceB1474 + difference 3 0) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA1474 + difference 0 3) (sourceB1474 + difference 3 0) sourceC1474) = raw22489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22489; decide +kernel
    rw [ha]
    exact (canonical22489 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1474 + difference 0 4) (sourceB1474 + difference 4 0) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA1474 + difference 0 4) (sourceB1474 + difference 4 0) sourceC1474) = raw12129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw12129; decide +kernel
    rw [ha]
    exact (canonical12129 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1474 + difference 0 5) (sourceB1474 + difference 5 0) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA1474 + difference 0 5) (sourceB1474 + difference 5 0) sourceC1474) = raw12124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw12124; decide +kernel
    rw [ha]
    exact (canonical12124 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1474 + difference 1 0) (sourceB1474 + difference 0 1) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 613) := by
    have ha : (tripleCharges (sourceA1474 + difference 1 0) (sourceB1474 + difference 0 1) sourceC1474) = raw22490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22490; decide +kernel
    rw [ha]
    exact (canonical22490 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1474 + difference 1 2) (sourceB1474 + difference 2 1) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1474 + difference 1 2) (sourceB1474 + difference 2 1) sourceC1474) = raw22491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22491; decide +kernel
    rw [ha]
    exact (canonical22491 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1474 + difference 1 3) (sourceB1474 + difference 3 1) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1474 + difference 1 3) (sourceB1474 + difference 3 1) sourceC1474) = raw22492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22492; decide +kernel
    rw [ha]
    exact (canonical22492 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1474 + difference 1 4) (sourceB1474 + difference 4 1) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1474 + difference 1 4) (sourceB1474 + difference 4 1) sourceC1474) = raw20370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw20370; decide +kernel
    rw [ha]
    exact (canonical20370 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1474 + difference 1 5) (sourceB1474 + difference 5 1) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1474 + difference 1 5) (sourceB1474 + difference 5 1) sourceC1474) = raw22493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22493; decide +kernel
    rw [ha]
    exact (canonical22493 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1474 + difference 2 0) (sourceB1474 + difference 0 2) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 613) := by
    have ha : (tripleCharges (sourceA1474 + difference 2 0) (sourceB1474 + difference 0 2) sourceC1474) = raw22494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22494; decide +kernel
    rw [ha]
    exact (canonical22494 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1474 + difference 2 1) (sourceB1474 + difference 1 2) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1474 + difference 2 1) (sourceB1474 + difference 1 2) sourceC1474) = raw22495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22495; decide +kernel
    rw [ha]
    exact (canonical22495 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1474 + difference 2 3) (sourceB1474 + difference 3 2) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1474 + difference 2 3) (sourceB1474 + difference 3 2) sourceC1474) = raw22496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22496; decide +kernel
    rw [ha]
    exact (canonical22496 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1474 + difference 2 4) (sourceB1474 + difference 4 2) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1474 + difference 2 4) (sourceB1474 + difference 4 2) sourceC1474) = raw20374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw20374; decide +kernel
    rw [ha]
    exact (canonical20374 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1474 + difference 2 5) (sourceB1474 + difference 5 2) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1474 + difference 2 5) (sourceB1474 + difference 5 2) sourceC1474) = raw22497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22497; decide +kernel
    rw [ha]
    exact (canonical22497 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1474 + difference 3 0) (sourceB1474 + difference 0 3) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 613) := by
    have ha : (tripleCharges (sourceA1474 + difference 3 0) (sourceB1474 + difference 0 3) sourceC1474) = raw22498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22498; decide +kernel
    rw [ha]
    exact (canonical22498 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1474 + difference 3 1) (sourceB1474 + difference 1 3) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1474 + difference 3 1) (sourceB1474 + difference 1 3) sourceC1474) = raw22499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22499; decide +kernel
    rw [ha]
    exact (canonical22499 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1474 + difference 3 2) (sourceB1474 + difference 2 3) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1474 + difference 3 2) (sourceB1474 + difference 2 3) sourceC1474) = raw22500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22500; decide +kernel
    rw [ha]
    exact (canonical22500 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1474 + difference 3 4) (sourceB1474 + difference 4 3) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1474 + difference 3 4) (sourceB1474 + difference 4 3) sourceC1474) = raw12126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw12126; decide +kernel
    rw [ha]
    exact (canonical12126 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1474 + difference 3 5) (sourceB1474 + difference 5 3) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1474 + difference 3 5) (sourceB1474 + difference 5 3) sourceC1474) = raw12121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw12121; decide +kernel
    rw [ha]
    exact (canonical12121 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1474 + difference 4 0) (sourceB1474 + difference 0 4) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 618) := by
    have ha : (tripleCharges (sourceA1474 + difference 4 0) (sourceB1474 + difference 0 4) sourceC1474) = raw22501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22501; decide +kernel
    rw [ha]
    exact (canonical22501 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1474 + difference 4 1) (sourceB1474 + difference 1 4) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1143) := by
    have ha : (tripleCharges (sourceA1474 + difference 4 1) (sourceB1474 + difference 1 4) sourceC1474) = raw22502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22502; decide +kernel
    rw [ha]
    exact (canonical22502 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1474 + difference 4 2) (sourceB1474 + difference 2 4) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1143) := by
    have ha : (tripleCharges (sourceA1474 + difference 4 2) (sourceB1474 + difference 2 4) sourceC1474) = raw22503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22503; decide +kernel
    rw [ha]
    exact (canonical22503 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1474 + difference 4 3) (sourceB1474 + difference 3 4) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1143) := by
    have ha : (tripleCharges (sourceA1474 + difference 4 3) (sourceB1474 + difference 3 4) sourceC1474) = raw22504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22504; decide +kernel
    rw [ha]
    exact (canonical22504 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1474 + difference 4 5) (sourceB1474 + difference 5 4) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA1474 + difference 4 5) (sourceB1474 + difference 5 4) sourceC1474) = raw22505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw22505; decide +kernel
    rw [ha]
    exact (canonical22505 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1474 + difference 5 0) (sourceB1474 + difference 0 5) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 620) := by
    have ha : (tripleCharges (sourceA1474 + difference 5 0) (sourceB1474 + difference 0 5) sourceC1474) = raw20378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw20378; decide +kernel
    rw [ha]
    exact (canonical20378 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1474 + difference 5 1) (sourceB1474 + difference 1 5) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1145) := by
    have ha : (tripleCharges (sourceA1474 + difference 5 1) (sourceB1474 + difference 1 5) sourceC1474) = raw20379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw20379; decide +kernel
    rw [ha]
    exact (canonical20379 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1474 + difference 5 2) (sourceB1474 + difference 2 5) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1145) := by
    have ha : (tripleCharges (sourceA1474 + difference 5 2) (sourceB1474 + difference 2 5) sourceC1474) = raw20380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw20380; decide +kernel
    rw [ha]
    exact (canonical20380 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1474 + difference 5 3) (sourceB1474 + difference 3 5) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1145) := by
    have ha : (tripleCharges (sourceA1474 + difference 5 3) (sourceB1474 + difference 3 5) sourceC1474) = raw20381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw20381; decide +kernel
    rw [ha]
    exact (canonical20381 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1474 + difference 5 4) (sourceB1474 + difference 4 5) sourceC1474) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1474 + difference 5 4) (sourceB1474 + difference 4 5) sourceC1474) = raw19549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1474 sourceB1474 sourceC1474 difference raw19549; decide +kernel
    rw [ha]
    exact (canonical19549 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1474 sourceB1474 sourceC1474
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1474, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1475 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1475 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1475 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1475 : Integer.Sparse Master := [(Sum.inr 4466, 6), (Sum.inr 4510, 2), (Sum.inr 4511, 2), (Sum.inr 4592, 6), (Sum.inr 4611, 6), (Sum.inr 4612, 6), (Sum.inr 4626, 1), (Sum.inr 4628, 1)]

theorem sourceEq1475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1475 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1475 + difference 0 1) (sourceB1475 + difference 1 0) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1475 + difference 0 1) (sourceB1475 + difference 1 0) sourceC1475) = raw22506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22506; decide +kernel
    rw [ha]
    exact (canonical22506 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1475 + difference 0 2) (sourceB1475 + difference 2 0) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1475 + difference 0 2) (sourceB1475 + difference 2 0) sourceC1475) = raw22507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22507; decide +kernel
    rw [ha]
    exact (canonical22507 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1475 + difference 0 3) (sourceB1475 + difference 3 0) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1475 + difference 0 3) (sourceB1475 + difference 3 0) sourceC1475) = raw22508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22508; decide +kernel
    rw [ha]
    exact (canonical22508 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1475 + difference 0 4) (sourceB1475 + difference 4 0) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA1475 + difference 0 4) (sourceB1475 + difference 4 0) sourceC1475) = raw22509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22509; decide +kernel
    rw [ha]
    exact (canonical22509 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1475 + difference 0 5) (sourceB1475 + difference 5 0) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1475 + difference 0 5) (sourceB1475 + difference 5 0) sourceC1475) = raw22510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22510; decide +kernel
    rw [ha]
    exact (canonical22510 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1475 + difference 1 0) (sourceB1475 + difference 0 1) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1475 + difference 1 0) (sourceB1475 + difference 0 1) sourceC1475) = raw22511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22511; decide +kernel
    rw [ha]
    exact (canonical22511 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1475 + difference 1 2) (sourceB1475 + difference 2 1) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1475 + difference 1 2) (sourceB1475 + difference 2 1) sourceC1475) = raw22512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22512; decide +kernel
    rw [ha]
    exact (canonical22512 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1475 + difference 1 3) (sourceB1475 + difference 3 1) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1475 + difference 1 3) (sourceB1475 + difference 3 1) sourceC1475) = raw22513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22513; decide +kernel
    rw [ha]
    exact (canonical22513 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1475 + difference 1 4) (sourceB1475 + difference 4 1) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1475 + difference 1 4) (sourceB1475 + difference 4 1) sourceC1475) = raw22514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22514; decide +kernel
    rw [ha]
    exact (canonical22514 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1475 + difference 1 5) (sourceB1475 + difference 5 1) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1475 + difference 1 5) (sourceB1475 + difference 5 1) sourceC1475) = raw22515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22515; decide +kernel
    rw [ha]
    exact (canonical22515 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1475 + difference 2 0) (sourceB1475 + difference 0 2) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1475 + difference 2 0) (sourceB1475 + difference 0 2) sourceC1475) = raw22516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22516; decide +kernel
    rw [ha]
    exact (canonical22516 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1475 + difference 2 1) (sourceB1475 + difference 1 2) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1475 + difference 2 1) (sourceB1475 + difference 1 2) sourceC1475) = raw22517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22517; decide +kernel
    rw [ha]
    exact (canonical22517 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1475 + difference 2 3) (sourceB1475 + difference 3 2) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1475 + difference 2 3) (sourceB1475 + difference 3 2) sourceC1475) = raw22518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22518; decide +kernel
    rw [ha]
    exact (canonical22518 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1475 + difference 2 4) (sourceB1475 + difference 4 2) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1475 + difference 2 4) (sourceB1475 + difference 4 2) sourceC1475) = raw22519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22519; decide +kernel
    rw [ha]
    exact (canonical22519 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1475 + difference 2 5) (sourceB1475 + difference 5 2) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1475 + difference 2 5) (sourceB1475 + difference 5 2) sourceC1475) = raw22520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22520; decide +kernel
    rw [ha]
    exact (canonical22520 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1475 + difference 3 0) (sourceB1475 + difference 0 3) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1475 + difference 3 0) (sourceB1475 + difference 0 3) sourceC1475) = raw22521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22521; decide +kernel
    rw [ha]
    exact (canonical22521 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1475 + difference 3 1) (sourceB1475 + difference 1 3) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1475 + difference 3 1) (sourceB1475 + difference 1 3) sourceC1475) = raw22522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22522; decide +kernel
    rw [ha]
    exact (canonical22522 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1475 + difference 3 2) (sourceB1475 + difference 2 3) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1475 + difference 3 2) (sourceB1475 + difference 2 3) sourceC1475) = raw22523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22523; decide +kernel
    rw [ha]
    exact (canonical22523 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1475 + difference 3 4) (sourceB1475 + difference 4 3) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1475 + difference 3 4) (sourceB1475 + difference 4 3) sourceC1475) = raw22524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22524; decide +kernel
    rw [ha]
    exact (canonical22524 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1475 + difference 3 5) (sourceB1475 + difference 5 3) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1475 + difference 3 5) (sourceB1475 + difference 5 3) sourceC1475) = raw22525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22525; decide +kernel
    rw [ha]
    exact (canonical22525 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1475 + difference 4 0) (sourceB1475 + difference 0 4) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1475 + difference 4 0) (sourceB1475 + difference 0 4) sourceC1475) = raw22526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22526; decide +kernel
    rw [ha]
    exact (canonical22526 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1475 + difference 4 1) (sourceB1475 + difference 1 4) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1475 + difference 4 1) (sourceB1475 + difference 1 4) sourceC1475) = raw22527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22527; decide +kernel
    rw [ha]
    exact (canonical22527 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1475 + difference 4 2) (sourceB1475 + difference 2 4) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1475 + difference 4 2) (sourceB1475 + difference 2 4) sourceC1475) = raw22528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22528; decide +kernel
    rw [ha]
    exact (canonical22528 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1475 + difference 4 3) (sourceB1475 + difference 3 4) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1475 + difference 4 3) (sourceB1475 + difference 3 4) sourceC1475) = raw22529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22529; decide +kernel
    rw [ha]
    exact (canonical22529 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1475 + difference 4 5) (sourceB1475 + difference 5 4) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4628) := by
    have ha : (tripleCharges (sourceA1475 + difference 4 5) (sourceB1475 + difference 5 4) sourceC1475) = raw22530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22530; decide +kernel
    rw [ha]
    exact (canonical22530 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1475 + difference 5 0) (sourceB1475 + difference 0 5) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA1475 + difference 5 0) (sourceB1475 + difference 0 5) sourceC1475) = raw22531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22531; decide +kernel
    rw [ha]
    exact (canonical22531 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1475 + difference 5 1) (sourceB1475 + difference 1 5) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1475 + difference 5 1) (sourceB1475 + difference 1 5) sourceC1475) = raw22532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22532; decide +kernel
    rw [ha]
    exact (canonical22532 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1475 + difference 5 2) (sourceB1475 + difference 2 5) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1475 + difference 5 2) (sourceB1475 + difference 2 5) sourceC1475) = raw22533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22533; decide +kernel
    rw [ha]
    exact (canonical22533 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1475 + difference 5 3) (sourceB1475 + difference 3 5) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1475 + difference 5 3) (sourceB1475 + difference 3 5) sourceC1475) = raw22534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22534; decide +kernel
    rw [ha]
    exact (canonical22534 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1475 + difference 5 4) (sourceB1475 + difference 4 5) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4626) := by
    have ha : (tripleCharges (sourceA1475 + difference 5 4) (sourceB1475 + difference 4 5) sourceC1475) = raw22535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22535; decide +kernel
    rw [ha]
    exact (canonical22535 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1475 sourceB1475 sourceC1475
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1475, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1476 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1476 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1476 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1476 : Integer.Sparse Master := [(Sum.inr 1049, 3), (Sum.inr 1094, 1), (Sum.inr 1095, 1), (Sum.inr 1219, 6), (Sum.inr 1245, 3), (Sum.inr 1246, 3), (Sum.inr 1273, 3), (Sum.inr 1274, 3), (Sum.inr 1310, 1), (Sum.inr 1312, 1), (Sum.inr 1419, 3), (Sum.inr 1454, 1), (Sum.inr 1455, 1)]

theorem sourceEq1476 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1476 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1476 + difference 0 1) (sourceB1476 + difference 1 0) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1476 + difference 0 1) (sourceB1476 + difference 1 0) sourceC1476) = raw22536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22536; decide +kernel
    rw [ha]
    exact (canonical22536 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1476 + difference 0 2) (sourceB1476 + difference 2 0) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1476 + difference 0 2) (sourceB1476 + difference 2 0) sourceC1476) = raw22537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22537; decide +kernel
    rw [ha]
    exact (canonical22537 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1476 + difference 0 3) (sourceB1476 + difference 3 0) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1476 + difference 0 3) (sourceB1476 + difference 3 0) sourceC1476) = raw22538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22538; decide +kernel
    rw [ha]
    exact (canonical22538 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1476 + difference 0 4) (sourceB1476 + difference 4 0) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1454) := by
    have ha : (tripleCharges (sourceA1476 + difference 0 4) (sourceB1476 + difference 4 0) sourceC1476) = raw22539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22539; decide +kernel
    rw [ha]
    exact (canonical22539 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1476 + difference 0 5) (sourceB1476 + difference 5 0) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1455) := by
    have ha : (tripleCharges (sourceA1476 + difference 0 5) (sourceB1476 + difference 5 0) sourceC1476) = raw22540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22540; decide +kernel
    rw [ha]
    exact (canonical22540 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1476 + difference 1 0) (sourceB1476 + difference 0 1) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1476 + difference 1 0) (sourceB1476 + difference 0 1) sourceC1476) = raw22541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22541; decide +kernel
    rw [ha]
    exact (canonical22541 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1476 + difference 1 2) (sourceB1476 + difference 2 1) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1476 + difference 1 2) (sourceB1476 + difference 2 1) sourceC1476) = raw22542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22542; decide +kernel
    rw [ha]
    exact (canonical22542 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1476 + difference 1 3) (sourceB1476 + difference 3 1) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1476 + difference 1 3) (sourceB1476 + difference 3 1) sourceC1476) = raw22543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22543; decide +kernel
    rw [ha]
    exact (canonical22543 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1476 + difference 1 4) (sourceB1476 + difference 4 1) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA1476 + difference 1 4) (sourceB1476 + difference 4 1) sourceC1476) = raw22544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22544; decide +kernel
    rw [ha]
    exact (canonical22544 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1476 + difference 1 5) (sourceB1476 + difference 5 1) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1476 + difference 1 5) (sourceB1476 + difference 5 1) sourceC1476) = raw22545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22545; decide +kernel
    rw [ha]
    exact (canonical22545 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1476 + difference 2 0) (sourceB1476 + difference 0 2) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1476 + difference 2 0) (sourceB1476 + difference 0 2) sourceC1476) = raw22546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22546; decide +kernel
    rw [ha]
    exact (canonical22546 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1476 + difference 2 1) (sourceB1476 + difference 1 2) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1476 + difference 2 1) (sourceB1476 + difference 1 2) sourceC1476) = raw22547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22547; decide +kernel
    rw [ha]
    exact (canonical22547 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1476 + difference 2 3) (sourceB1476 + difference 3 2) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1476 + difference 2 3) (sourceB1476 + difference 3 2) sourceC1476) = raw22548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22548; decide +kernel
    rw [ha]
    exact (canonical22548 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1476 + difference 2 4) (sourceB1476 + difference 4 2) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA1476 + difference 2 4) (sourceB1476 + difference 4 2) sourceC1476) = raw22549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22549; decide +kernel
    rw [ha]
    exact (canonical22549 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1476 + difference 2 5) (sourceB1476 + difference 5 2) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1476 + difference 2 5) (sourceB1476 + difference 5 2) sourceC1476) = raw22550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22550; decide +kernel
    rw [ha]
    exact (canonical22550 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1476 + difference 3 0) (sourceB1476 + difference 0 3) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1476 + difference 3 0) (sourceB1476 + difference 0 3) sourceC1476) = raw22551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22551; decide +kernel
    rw [ha]
    exact (canonical22551 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1476 + difference 3 1) (sourceB1476 + difference 1 3) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1476 + difference 3 1) (sourceB1476 + difference 1 3) sourceC1476) = raw22552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22552; decide +kernel
    rw [ha]
    exact (canonical22552 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1476 + difference 3 2) (sourceB1476 + difference 2 3) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1476 + difference 3 2) (sourceB1476 + difference 2 3) sourceC1476) = raw22553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22553; decide +kernel
    rw [ha]
    exact (canonical22553 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1476 + difference 3 4) (sourceB1476 + difference 4 3) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA1476 + difference 3 4) (sourceB1476 + difference 4 3) sourceC1476) = raw22554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22554; decide +kernel
    rw [ha]
    exact (canonical22554 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1476 + difference 3 5) (sourceB1476 + difference 5 3) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1476 + difference 3 5) (sourceB1476 + difference 5 3) sourceC1476) = raw22555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22555; decide +kernel
    rw [ha]
    exact (canonical22555 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1476 + difference 4 0) (sourceB1476 + difference 0 4) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1095) := by
    have ha : (tripleCharges (sourceA1476 + difference 4 0) (sourceB1476 + difference 0 4) sourceC1476) = raw22556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22556; decide +kernel
    rw [ha]
    exact (canonical22556 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1476 + difference 4 1) (sourceB1476 + difference 1 4) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1476 + difference 4 1) (sourceB1476 + difference 1 4) sourceC1476) = raw22557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22557; decide +kernel
    rw [ha]
    exact (canonical22557 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1476 + difference 4 2) (sourceB1476 + difference 2 4) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1476 + difference 4 2) (sourceB1476 + difference 2 4) sourceC1476) = raw22558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22558; decide +kernel
    rw [ha]
    exact (canonical22558 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1476 + difference 4 3) (sourceB1476 + difference 3 4) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1476 + difference 4 3) (sourceB1476 + difference 3 4) sourceC1476) = raw22559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22559; decide +kernel
    rw [ha]
    exact (canonical22559 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1476 + difference 4 5) (sourceB1476 + difference 5 4) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1312) := by
    have ha : (tripleCharges (sourceA1476 + difference 4 5) (sourceB1476 + difference 5 4) sourceC1476) = raw22560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22560; decide +kernel
    rw [ha]
    exact (canonical22560 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1476 + difference 5 0) (sourceB1476 + difference 0 5) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1094) := by
    have ha : (tripleCharges (sourceA1476 + difference 5 0) (sourceB1476 + difference 0 5) sourceC1476) = raw22561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22561; decide +kernel
    rw [ha]
    exact (canonical22561 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1476 + difference 5 1) (sourceB1476 + difference 1 5) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA1476 + difference 5 1) (sourceB1476 + difference 1 5) sourceC1476) = raw22562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22562; decide +kernel
    rw [ha]
    exact (canonical22562 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1476 + difference 5 2) (sourceB1476 + difference 2 5) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA1476 + difference 5 2) (sourceB1476 + difference 2 5) sourceC1476) = raw22563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22563; decide +kernel
    rw [ha]
    exact (canonical22563 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1476 + difference 5 3) (sourceB1476 + difference 3 5) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA1476 + difference 5 3) (sourceB1476 + difference 3 5) sourceC1476) = raw22564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22564; decide +kernel
    rw [ha]
    exact (canonical22564 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1476 + difference 5 4) (sourceB1476 + difference 4 5) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1310) := by
    have ha : (tripleCharges (sourceA1476 + difference 5 4) (sourceB1476 + difference 4 5) sourceC1476) = raw22565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22565; decide +kernel
    rw [ha]
    exact (canonical22565 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1476 sourceB1476 sourceC1476
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1476, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1477 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1477 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1477 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1477 : Integer.Sparse Master := [(Sum.inr 1755, 1), (Sum.inr 3301, 3), (Sum.inr 3311, 1), (Sum.inr 3312, 1), (Sum.inr 4071, -1)]

theorem sourceEq1477 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1477 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 0) (sourceB1477 + difference 0 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1755) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 0) (sourceB1477 + difference 0 4) sourceC1477) = raw22566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22566; decide +kernel
    rw [ha]
    exact (canonical22566 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 1) (sourceB1477 + difference 1 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 1) (sourceB1477 + difference 1 4) sourceC1477) = raw22421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22421; decide +kernel
    rw [ha]
    exact (canonical22421 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 2) (sourceB1477 + difference 2 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 2) (sourceB1477 + difference 2 4) sourceC1477) = raw22567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22567; decide +kernel
    rw [ha]
    exact (canonical22567 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 3) (sourceB1477 + difference 3 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 3) (sourceB1477 + difference 3 4) sourceC1477) = raw22568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22568; decide +kernel
    rw [ha]
    exact (canonical22568 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 4) (sourceB1477 + difference 4 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3311) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 4) (sourceB1477 + difference 4 4) sourceC1477) = raw22416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22416; decide +kernel
    rw [ha]
    exact (canonical22416 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 5) (sourceB1477 + difference 5 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3312) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 5) (sourceB1477 + difference 5 4) sourceC1477) = raw22455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22455; decide +kernel
    rw [ha]
    exact (canonical22455 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1477 + sourceB1477) sourceC1477) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1477 + sourceB1477) sourceC1477) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1477 sourceB1477 sourceC1477 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1477 sourceB1477 sourceC1477
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1477, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1478 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1478 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1478 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm1478 : Integer.Sparse Master := [(Sum.inr 4186, 3), (Sum.inr 4191, 2), (Sum.inr 4554, 6), (Sum.inr 4558, 6), (Sum.inr 4624, 6), (Sum.inr 4625, 2), (Sum.inr 5177, 3), (Sum.inr 5309, 2)]

theorem sourceEq1478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1478 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1478 + difference 0 1) (sourceB1478 + difference 1 0) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA1478 + difference 0 1) (sourceB1478 + difference 1 0) sourceC1478) = raw10211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw10211; decide +kernel
    rw [ha]
    exact (canonical10211 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1478 + difference 0 2) (sourceB1478 + difference 2 0) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA1478 + difference 0 2) (sourceB1478 + difference 2 0) sourceC1478) = raw10212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw10212; decide +kernel
    rw [ha]
    exact (canonical10212 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1478 + difference 0 3) (sourceB1478 + difference 3 0) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA1478 + difference 0 3) (sourceB1478 + difference 3 0) sourceC1478) = raw10213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw10213; decide +kernel
    rw [ha]
    exact (canonical10213 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1478 + difference 0 4) (sourceB1478 + difference 4 0) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA1478 + difference 0 4) (sourceB1478 + difference 4 0) sourceC1478) = raw4306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw4306; decide +kernel
    rw [ha]
    exact (canonical4306 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1478 + difference 0 5) (sourceB1478 + difference 5 0) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA1478 + difference 0 5) (sourceB1478 + difference 5 0) sourceC1478) = raw10214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw10214; decide +kernel
    rw [ha]
    exact (canonical10214 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1478 + difference 1 0) (sourceB1478 + difference 0 1) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4186) := by
    have ha : (tripleCharges (sourceA1478 + difference 1 0) (sourceB1478 + difference 0 1) sourceC1478) = raw22569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22569; decide +kernel
    rw [ha]
    exact (canonical22569 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1478 + difference 1 2) (sourceB1478 + difference 2 1) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4554) := by
    have ha : (tripleCharges (sourceA1478 + difference 1 2) (sourceB1478 + difference 2 1) sourceC1478) = raw22570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22570; decide +kernel
    rw [ha]
    exact (canonical22570 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1478 + difference 1 3) (sourceB1478 + difference 3 1) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4554) := by
    have ha : (tripleCharges (sourceA1478 + difference 1 3) (sourceB1478 + difference 3 1) sourceC1478) = raw22571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22571; decide +kernel
    rw [ha]
    exact (canonical22571 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1478 + difference 1 4) (sourceB1478 + difference 4 1) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1478 + difference 1 4) (sourceB1478 + difference 4 1) sourceC1478) = raw10198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw10198; decide +kernel
    rw [ha]
    exact (canonical10198 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1478 + difference 1 5) (sourceB1478 + difference 5 1) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1478 + difference 1 5) (sourceB1478 + difference 5 1) sourceC1478) = raw22572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22572; decide +kernel
    rw [ha]
    exact (canonical22572 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1478 + difference 2 0) (sourceB1478 + difference 0 2) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4186) := by
    have ha : (tripleCharges (sourceA1478 + difference 2 0) (sourceB1478 + difference 0 2) sourceC1478) = raw22573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22573; decide +kernel
    rw [ha]
    exact (canonical22573 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1478 + difference 2 1) (sourceB1478 + difference 1 2) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4554) := by
    have ha : (tripleCharges (sourceA1478 + difference 2 1) (sourceB1478 + difference 1 2) sourceC1478) = raw22574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22574; decide +kernel
    rw [ha]
    exact (canonical22574 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1478 + difference 2 3) (sourceB1478 + difference 3 2) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4554) := by
    have ha : (tripleCharges (sourceA1478 + difference 2 3) (sourceB1478 + difference 3 2) sourceC1478) = raw22575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22575; decide +kernel
    rw [ha]
    exact (canonical22575 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1478 + difference 2 4) (sourceB1478 + difference 4 2) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1478 + difference 2 4) (sourceB1478 + difference 4 2) sourceC1478) = raw10202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw10202; decide +kernel
    rw [ha]
    exact (canonical10202 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1478 + difference 2 5) (sourceB1478 + difference 5 2) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1478 + difference 2 5) (sourceB1478 + difference 5 2) sourceC1478) = raw22576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22576; decide +kernel
    rw [ha]
    exact (canonical22576 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1478 + difference 3 0) (sourceB1478 + difference 0 3) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4186) := by
    have ha : (tripleCharges (sourceA1478 + difference 3 0) (sourceB1478 + difference 0 3) sourceC1478) = raw22577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22577; decide +kernel
    rw [ha]
    exact (canonical22577 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1478 + difference 3 1) (sourceB1478 + difference 1 3) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4554) := by
    have ha : (tripleCharges (sourceA1478 + difference 3 1) (sourceB1478 + difference 1 3) sourceC1478) = raw22578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22578; decide +kernel
    rw [ha]
    exact (canonical22578 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1478 + difference 3 2) (sourceB1478 + difference 2 3) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4554) := by
    have ha : (tripleCharges (sourceA1478 + difference 3 2) (sourceB1478 + difference 2 3) sourceC1478) = raw22579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22579; decide +kernel
    rw [ha]
    exact (canonical22579 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1478 + difference 3 4) (sourceB1478 + difference 4 3) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1478 + difference 3 4) (sourceB1478 + difference 4 3) sourceC1478) = raw10206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw10206; decide +kernel
    rw [ha]
    exact (canonical10206 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1478 + difference 3 5) (sourceB1478 + difference 5 3) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1478 + difference 3 5) (sourceB1478 + difference 5 3) sourceC1478) = raw22580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22580; decide +kernel
    rw [ha]
    exact (canonical22580 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1478 + difference 4 0) (sourceB1478 + difference 0 4) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4191) := by
    have ha : (tripleCharges (sourceA1478 + difference 4 0) (sourceB1478 + difference 0 4) sourceC1478) = raw22581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22581; decide +kernel
    rw [ha]
    exact (canonical22581 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1478 + difference 4 1) (sourceB1478 + difference 1 4) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1478 + difference 4 1) (sourceB1478 + difference 1 4) sourceC1478) = raw22582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22582; decide +kernel
    rw [ha]
    exact (canonical22582 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1478 + difference 4 2) (sourceB1478 + difference 2 4) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1478 + difference 4 2) (sourceB1478 + difference 2 4) sourceC1478) = raw22583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22583; decide +kernel
    rw [ha]
    exact (canonical22583 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1478 + difference 4 3) (sourceB1478 + difference 3 4) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1478 + difference 4 3) (sourceB1478 + difference 3 4) sourceC1478) = raw22584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22584; decide +kernel
    rw [ha]
    exact (canonical22584 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1478 + difference 4 5) (sourceB1478 + difference 5 4) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1478 + difference 4 5) (sourceB1478 + difference 5 4) sourceC1478) = raw22585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw22585; decide +kernel
    rw [ha]
    exact (canonical22585 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1478 + difference 5 0) (sourceB1478 + difference 0 5) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4191) := by
    have ha : (tripleCharges (sourceA1478 + difference 5 0) (sourceB1478 + difference 0 5) sourceC1478) = raw20393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw20393; decide +kernel
    rw [ha]
    exact (canonical20393 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1478 + difference 5 1) (sourceB1478 + difference 1 5) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1478 + difference 5 1) (sourceB1478 + difference 1 5) sourceC1478) = raw20394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw20394; decide +kernel
    rw [ha]
    exact (canonical20394 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1478 + difference 5 2) (sourceB1478 + difference 2 5) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1478 + difference 5 2) (sourceB1478 + difference 2 5) sourceC1478) = raw20395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw20395; decide +kernel
    rw [ha]
    exact (canonical20395 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1478 + difference 5 3) (sourceB1478 + difference 3 5) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1478 + difference 5 3) (sourceB1478 + difference 3 5) sourceC1478) = raw20396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw20396; decide +kernel
    rw [ha]
    exact (canonical20396 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1478 + difference 5 4) (sourceB1478 + difference 4 5) sourceC1478) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1478 + difference 5 4) (sourceB1478 + difference 4 5) sourceC1478) = raw4302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1478 sourceB1478 sourceC1478 difference raw4302; decide +kernel
    rw [ha]
    exact (canonical4302 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1478 sourceB1478 sourceC1478
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1478, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1479 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1479 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1479 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm1479 : Integer.Sparse Master := [(Sum.inr 614, 3), (Sum.inr 619, 2), (Sum.inr 1139, 6), (Sum.inr 1144, 6), (Sum.inr 1301, 6), (Sum.inr 1304, 2), (Sum.inr 2969, 3), (Sum.inr 3123, 2)]

theorem sourceEq1479 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1479 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1479 + difference 0 1) (sourceB1479 + difference 1 0) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2969) := by
    have ha : (tripleCharges (sourceA1479 + difference 0 1) (sourceB1479 + difference 1 0) sourceC1479) = raw22586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22586; decide +kernel
    rw [ha]
    exact (canonical22586 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1479 + difference 0 2) (sourceB1479 + difference 2 0) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2969) := by
    have ha : (tripleCharges (sourceA1479 + difference 0 2) (sourceB1479 + difference 2 0) sourceC1479) = raw22587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22587; decide +kernel
    rw [ha]
    exact (canonical22587 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1479 + difference 0 3) (sourceB1479 + difference 3 0) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2969) := by
    have ha : (tripleCharges (sourceA1479 + difference 0 3) (sourceB1479 + difference 3 0) sourceC1479) = raw22588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22588; decide +kernel
    rw [ha]
    exact (canonical22588 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1479 + difference 0 4) (sourceB1479 + difference 4 0) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3123) := by
    have ha : (tripleCharges (sourceA1479 + difference 0 4) (sourceB1479 + difference 4 0) sourceC1479) = raw4336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw4336; decide +kernel
    rw [ha]
    exact (canonical4336 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1479 + difference 0 5) (sourceB1479 + difference 5 0) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3123) := by
    have ha : (tripleCharges (sourceA1479 + difference 0 5) (sourceB1479 + difference 5 0) sourceC1479) = raw22589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22589; decide +kernel
    rw [ha]
    exact (canonical22589 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1479 + difference 1 0) (sourceB1479 + difference 0 1) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 614) := by
    have ha : (tripleCharges (sourceA1479 + difference 1 0) (sourceB1479 + difference 0 1) sourceC1479) = raw22590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22590; decide +kernel
    rw [ha]
    exact (canonical22590 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1479 + difference 1 2) (sourceB1479 + difference 2 1) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1139) := by
    have ha : (tripleCharges (sourceA1479 + difference 1 2) (sourceB1479 + difference 2 1) sourceC1479) = raw22591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22591; decide +kernel
    rw [ha]
    exact (canonical22591 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1479 + difference 1 3) (sourceB1479 + difference 3 1) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1139) := by
    have ha : (tripleCharges (sourceA1479 + difference 1 3) (sourceB1479 + difference 3 1) sourceC1479) = raw22592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22592; decide +kernel
    rw [ha]
    exact (canonical22592 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1479 + difference 1 4) (sourceB1479 + difference 4 1) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1479 + difference 1 4) (sourceB1479 + difference 4 1) sourceC1479) = raw20400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw20400; decide +kernel
    rw [ha]
    exact (canonical20400 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1479 + difference 1 5) (sourceB1479 + difference 5 1) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1479 + difference 1 5) (sourceB1479 + difference 5 1) sourceC1479) = raw22593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22593; decide +kernel
    rw [ha]
    exact (canonical22593 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1479 + difference 2 0) (sourceB1479 + difference 0 2) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 614) := by
    have ha : (tripleCharges (sourceA1479 + difference 2 0) (sourceB1479 + difference 0 2) sourceC1479) = raw22594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22594; decide +kernel
    rw [ha]
    exact (canonical22594 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1479 + difference 2 1) (sourceB1479 + difference 1 2) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1139) := by
    have ha : (tripleCharges (sourceA1479 + difference 2 1) (sourceB1479 + difference 1 2) sourceC1479) = raw22595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22595; decide +kernel
    rw [ha]
    exact (canonical22595 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1479 + difference 2 3) (sourceB1479 + difference 3 2) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1139) := by
    have ha : (tripleCharges (sourceA1479 + difference 2 3) (sourceB1479 + difference 3 2) sourceC1479) = raw22596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22596; decide +kernel
    rw [ha]
    exact (canonical22596 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1479 + difference 2 4) (sourceB1479 + difference 4 2) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1479 + difference 2 4) (sourceB1479 + difference 4 2) sourceC1479) = raw20404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw20404; decide +kernel
    rw [ha]
    exact (canonical20404 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1479 + difference 2 5) (sourceB1479 + difference 5 2) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1479 + difference 2 5) (sourceB1479 + difference 5 2) sourceC1479) = raw22597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22597; decide +kernel
    rw [ha]
    exact (canonical22597 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1479 + difference 3 0) (sourceB1479 + difference 0 3) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 614) := by
    have ha : (tripleCharges (sourceA1479 + difference 3 0) (sourceB1479 + difference 0 3) sourceC1479) = raw22598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22598; decide +kernel
    rw [ha]
    exact (canonical22598 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1479 + difference 3 1) (sourceB1479 + difference 1 3) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1139) := by
    have ha : (tripleCharges (sourceA1479 + difference 3 1) (sourceB1479 + difference 1 3) sourceC1479) = raw22599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22599; decide +kernel
    rw [ha]
    exact (canonical22599 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1479 + difference 3 2) (sourceB1479 + difference 2 3) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1139) := by
    have ha : (tripleCharges (sourceA1479 + difference 3 2) (sourceB1479 + difference 2 3) sourceC1479) = raw22600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22600; decide +kernel
    rw [ha]
    exact (canonical22600 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1479 + difference 3 4) (sourceB1479 + difference 4 3) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1479 + difference 3 4) (sourceB1479 + difference 4 3) sourceC1479) = raw20408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw20408; decide +kernel
    rw [ha]
    exact (canonical20408 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1479 + difference 3 5) (sourceB1479 + difference 5 3) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1479 + difference 3 5) (sourceB1479 + difference 5 3) sourceC1479) = raw22601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22601; decide +kernel
    rw [ha]
    exact (canonical22601 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1479 + difference 4 0) (sourceB1479 + difference 0 4) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 619) := by
    have ha : (tripleCharges (sourceA1479 + difference 4 0) (sourceB1479 + difference 0 4) sourceC1479) = raw22602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22602; decide +kernel
    rw [ha]
    exact (canonical22602 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1479 + difference 4 1) (sourceB1479 + difference 1 4) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1144) := by
    have ha : (tripleCharges (sourceA1479 + difference 4 1) (sourceB1479 + difference 1 4) sourceC1479) = raw22603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22603; decide +kernel
    rw [ha]
    exact (canonical22603 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1479 + difference 4 2) (sourceB1479 + difference 2 4) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1144) := by
    have ha : (tripleCharges (sourceA1479 + difference 4 2) (sourceB1479 + difference 2 4) sourceC1479) = raw22604 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22604; decide +kernel
    rw [ha]
    exact (canonical22604 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1479 + difference 4 3) (sourceB1479 + difference 3 4) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1144) := by
    have ha : (tripleCharges (sourceA1479 + difference 4 3) (sourceB1479 + difference 3 4) sourceC1479) = raw22605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22605; decide +kernel
    rw [ha]
    exact (canonical22605 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1479 + difference 4 5) (sourceB1479 + difference 5 4) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1304) := by
    have ha : (tripleCharges (sourceA1479 + difference 4 5) (sourceB1479 + difference 5 4) sourceC1479) = raw22606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw22606; decide +kernel
    rw [ha]
    exact (canonical22606 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1479 + difference 5 0) (sourceB1479 + difference 0 5) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 619) := by
    have ha : (tripleCharges (sourceA1479 + difference 5 0) (sourceB1479 + difference 0 5) sourceC1479) = raw20409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw20409; decide +kernel
    rw [ha]
    exact (canonical20409 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1479 + difference 5 1) (sourceB1479 + difference 1 5) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1144) := by
    have ha : (tripleCharges (sourceA1479 + difference 5 1) (sourceB1479 + difference 1 5) sourceC1479) = raw20410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw20410; decide +kernel
    rw [ha]
    exact (canonical20410 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1479 + difference 5 2) (sourceB1479 + difference 2 5) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1144) := by
    have ha : (tripleCharges (sourceA1479 + difference 5 2) (sourceB1479 + difference 2 5) sourceC1479) = raw20411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw20411; decide +kernel
    rw [ha]
    exact (canonical20411 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1479 + difference 5 3) (sourceB1479 + difference 3 5) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1144) := by
    have ha : (tripleCharges (sourceA1479 + difference 5 3) (sourceB1479 + difference 3 5) sourceC1479) = raw20412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw20412; decide +kernel
    rw [ha]
    exact (canonical20412 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1479 + difference 5 4) (sourceB1479 + difference 4 5) sourceC1479) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1304) := by
    have ha : (tripleCharges (sourceA1479 + difference 5 4) (sourceB1479 + difference 4 5) sourceC1479) = raw4332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1479 sourceB1479 sourceC1479 difference raw4332; decide +kernel
    rw [ha]
    exact (canonical4332 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1479 sourceB1479 sourceC1479
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1479, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1480 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1480 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1480 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1480 : Integer.Sparse Master := [(Sum.inr 4467, 6), (Sum.inr 4511, 4), (Sum.inr 4593, 6), (Sum.inr 4612, 12), (Sum.inr 4627, 2)]

theorem sourceEq1480 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1480 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1480 + difference 0 1) (sourceB1480 + difference 1 0) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1480 + difference 0 1) (sourceB1480 + difference 1 0) sourceC1480) = raw22607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22607; decide +kernel
    rw [ha]
    exact (canonical22607 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1480 + difference 0 2) (sourceB1480 + difference 2 0) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1480 + difference 0 2) (sourceB1480 + difference 2 0) sourceC1480) = raw22608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22608; decide +kernel
    rw [ha]
    exact (canonical22608 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1480 + difference 0 3) (sourceB1480 + difference 3 0) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1480 + difference 0 3) (sourceB1480 + difference 3 0) sourceC1480) = raw22609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22609; decide +kernel
    rw [ha]
    exact (canonical22609 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1480 + difference 0 4) (sourceB1480 + difference 4 0) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1480 + difference 0 4) (sourceB1480 + difference 4 0) sourceC1480) = raw22510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22510; decide +kernel
    rw [ha]
    exact (canonical22510 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1480 + difference 0 5) (sourceB1480 + difference 5 0) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1480 + difference 0 5) (sourceB1480 + difference 5 0) sourceC1480) = raw22610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22610; decide +kernel
    rw [ha]
    exact (canonical22610 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1480 + difference 1 0) (sourceB1480 + difference 0 1) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1480 + difference 1 0) (sourceB1480 + difference 0 1) sourceC1480) = raw22611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22611; decide +kernel
    rw [ha]
    exact (canonical22611 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1480 + difference 1 2) (sourceB1480 + difference 2 1) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1480 + difference 1 2) (sourceB1480 + difference 2 1) sourceC1480) = raw22612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22612; decide +kernel
    rw [ha]
    exact (canonical22612 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1480 + difference 1 3) (sourceB1480 + difference 3 1) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1480 + difference 1 3) (sourceB1480 + difference 3 1) sourceC1480) = raw22613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22613; decide +kernel
    rw [ha]
    exact (canonical22613 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1480 + difference 1 4) (sourceB1480 + difference 4 1) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 1 4) (sourceB1480 + difference 4 1) sourceC1480) = raw22515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22515; decide +kernel
    rw [ha]
    exact (canonical22515 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1480 + difference 1 5) (sourceB1480 + difference 5 1) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 1 5) (sourceB1480 + difference 5 1) sourceC1480) = raw22614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22614; decide +kernel
    rw [ha]
    exact (canonical22614 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1480 + difference 2 0) (sourceB1480 + difference 0 2) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1480 + difference 2 0) (sourceB1480 + difference 0 2) sourceC1480) = raw22615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22615; decide +kernel
    rw [ha]
    exact (canonical22615 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1480 + difference 2 1) (sourceB1480 + difference 1 2) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1480 + difference 2 1) (sourceB1480 + difference 1 2) sourceC1480) = raw22616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22616; decide +kernel
    rw [ha]
    exact (canonical22616 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1480 + difference 2 3) (sourceB1480 + difference 3 2) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1480 + difference 2 3) (sourceB1480 + difference 3 2) sourceC1480) = raw22617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22617; decide +kernel
    rw [ha]
    exact (canonical22617 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1480 + difference 2 4) (sourceB1480 + difference 4 2) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 2 4) (sourceB1480 + difference 4 2) sourceC1480) = raw22520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22520; decide +kernel
    rw [ha]
    exact (canonical22520 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1480 + difference 2 5) (sourceB1480 + difference 5 2) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 2 5) (sourceB1480 + difference 5 2) sourceC1480) = raw22618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22618; decide +kernel
    rw [ha]
    exact (canonical22618 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1480 + difference 3 0) (sourceB1480 + difference 0 3) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1480 + difference 3 0) (sourceB1480 + difference 0 3) sourceC1480) = raw22619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22619; decide +kernel
    rw [ha]
    exact (canonical22619 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1480 + difference 3 1) (sourceB1480 + difference 1 3) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1480 + difference 3 1) (sourceB1480 + difference 1 3) sourceC1480) = raw22620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22620; decide +kernel
    rw [ha]
    exact (canonical22620 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1480 + difference 3 2) (sourceB1480 + difference 2 3) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1480 + difference 3 2) (sourceB1480 + difference 2 3) sourceC1480) = raw22621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22621; decide +kernel
    rw [ha]
    exact (canonical22621 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1480 + difference 3 4) (sourceB1480 + difference 4 3) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 3 4) (sourceB1480 + difference 4 3) sourceC1480) = raw22525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22525; decide +kernel
    rw [ha]
    exact (canonical22525 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1480 + difference 3 5) (sourceB1480 + difference 5 3) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 3 5) (sourceB1480 + difference 5 3) sourceC1480) = raw22622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22622; decide +kernel
    rw [ha]
    exact (canonical22622 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1480 + difference 4 0) (sourceB1480 + difference 0 4) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1480 + difference 4 0) (sourceB1480 + difference 0 4) sourceC1480) = raw22623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22623; decide +kernel
    rw [ha]
    exact (canonical22623 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1480 + difference 4 1) (sourceB1480 + difference 1 4) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 4 1) (sourceB1480 + difference 1 4) sourceC1480) = raw22624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22624; decide +kernel
    rw [ha]
    exact (canonical22624 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1480 + difference 4 2) (sourceB1480 + difference 2 4) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 4 2) (sourceB1480 + difference 2 4) sourceC1480) = raw22625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22625; decide +kernel
    rw [ha]
    exact (canonical22625 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1480 + difference 4 3) (sourceB1480 + difference 3 4) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 4 3) (sourceB1480 + difference 3 4) sourceC1480) = raw22626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22626; decide +kernel
    rw [ha]
    exact (canonical22626 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1480 + difference 4 5) (sourceB1480 + difference 5 4) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA1480 + difference 4 5) (sourceB1480 + difference 5 4) sourceC1480) = raw22627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22627; decide +kernel
    rw [ha]
    exact (canonical22627 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1480 + difference 5 0) (sourceB1480 + difference 0 5) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1480 + difference 5 0) (sourceB1480 + difference 0 5) sourceC1480) = raw22526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22526; decide +kernel
    rw [ha]
    exact (canonical22526 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1480 + difference 5 1) (sourceB1480 + difference 1 5) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 5 1) (sourceB1480 + difference 1 5) sourceC1480) = raw22527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22527; decide +kernel
    rw [ha]
    exact (canonical22527 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1480 + difference 5 2) (sourceB1480 + difference 2 5) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 5 2) (sourceB1480 + difference 2 5) sourceC1480) = raw22528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22528; decide +kernel
    rw [ha]
    exact (canonical22528 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1480 + difference 5 3) (sourceB1480 + difference 3 5) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 5 3) (sourceB1480 + difference 3 5) sourceC1480) = raw22529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22529; decide +kernel
    rw [ha]
    exact (canonical22529 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1480 + difference 5 4) (sourceB1480 + difference 4 5) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA1480 + difference 5 4) (sourceB1480 + difference 4 5) sourceC1480) = raw22628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22628; decide +kernel
    rw [ha]
    exact (canonical22628 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1480 sourceB1480 sourceC1480
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1480, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1481 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1481 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1481 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1481 : Integer.Sparse Master := [(Sum.inr 1050, 3), (Sum.inr 1095, 2), (Sum.inr 1220, 6), (Sum.inr 1246, 6), (Sum.inr 1274, 6), (Sum.inr 1311, 2), (Sum.inr 1420, 3), (Sum.inr 1455, 2)]

theorem sourceEq1481 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1481 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1481 + difference 0 1) (sourceB1481 + difference 1 0) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1420) := by
    have ha : (tripleCharges (sourceA1481 + difference 0 1) (sourceB1481 + difference 1 0) sourceC1481) = raw22629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22629; decide +kernel
    rw [ha]
    exact (canonical22629 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1481 + difference 0 2) (sourceB1481 + difference 2 0) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1420) := by
    have ha : (tripleCharges (sourceA1481 + difference 0 2) (sourceB1481 + difference 2 0) sourceC1481) = raw22630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22630; decide +kernel
    rw [ha]
    exact (canonical22630 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1481 + difference 0 3) (sourceB1481 + difference 3 0) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1420) := by
    have ha : (tripleCharges (sourceA1481 + difference 0 3) (sourceB1481 + difference 3 0) sourceC1481) = raw22631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22631; decide +kernel
    rw [ha]
    exact (canonical22631 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1481 + difference 0 4) (sourceB1481 + difference 4 0) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1455) := by
    have ha : (tripleCharges (sourceA1481 + difference 0 4) (sourceB1481 + difference 4 0) sourceC1481) = raw22540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22540; decide +kernel
    rw [ha]
    exact (canonical22540 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1481 + difference 0 5) (sourceB1481 + difference 5 0) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1455) := by
    have ha : (tripleCharges (sourceA1481 + difference 0 5) (sourceB1481 + difference 5 0) sourceC1481) = raw22632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22632; decide +kernel
    rw [ha]
    exact (canonical22632 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1481 + difference 1 0) (sourceB1481 + difference 0 1) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1481 + difference 1 0) (sourceB1481 + difference 0 1) sourceC1481) = raw22633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22633; decide +kernel
    rw [ha]
    exact (canonical22633 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1481 + difference 1 2) (sourceB1481 + difference 2 1) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1481 + difference 1 2) (sourceB1481 + difference 2 1) sourceC1481) = raw22634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22634; decide +kernel
    rw [ha]
    exact (canonical22634 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1481 + difference 1 3) (sourceB1481 + difference 3 1) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1481 + difference 1 3) (sourceB1481 + difference 3 1) sourceC1481) = raw22635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22635; decide +kernel
    rw [ha]
    exact (canonical22635 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1481 + difference 1 4) (sourceB1481 + difference 4 1) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1481 + difference 1 4) (sourceB1481 + difference 4 1) sourceC1481) = raw22545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22545; decide +kernel
    rw [ha]
    exact (canonical22545 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1481 + difference 1 5) (sourceB1481 + difference 5 1) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1481 + difference 1 5) (sourceB1481 + difference 5 1) sourceC1481) = raw22636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22636; decide +kernel
    rw [ha]
    exact (canonical22636 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1481 + difference 2 0) (sourceB1481 + difference 0 2) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1481 + difference 2 0) (sourceB1481 + difference 0 2) sourceC1481) = raw22637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22637; decide +kernel
    rw [ha]
    exact (canonical22637 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1481 + difference 2 1) (sourceB1481 + difference 1 2) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1481 + difference 2 1) (sourceB1481 + difference 1 2) sourceC1481) = raw22638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22638; decide +kernel
    rw [ha]
    exact (canonical22638 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1481 + difference 2 3) (sourceB1481 + difference 3 2) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1481 + difference 2 3) (sourceB1481 + difference 3 2) sourceC1481) = raw22639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22639; decide +kernel
    rw [ha]
    exact (canonical22639 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1481 + difference 2 4) (sourceB1481 + difference 4 2) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1481 + difference 2 4) (sourceB1481 + difference 4 2) sourceC1481) = raw22550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22550; decide +kernel
    rw [ha]
    exact (canonical22550 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1481 + difference 2 5) (sourceB1481 + difference 5 2) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1481 + difference 2 5) (sourceB1481 + difference 5 2) sourceC1481) = raw22640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22640; decide +kernel
    rw [ha]
    exact (canonical22640 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1481 + difference 3 0) (sourceB1481 + difference 0 3) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1481 + difference 3 0) (sourceB1481 + difference 0 3) sourceC1481) = raw22641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22641; decide +kernel
    rw [ha]
    exact (canonical22641 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1481 + difference 3 1) (sourceB1481 + difference 1 3) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1481 + difference 3 1) (sourceB1481 + difference 1 3) sourceC1481) = raw22642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22642; decide +kernel
    rw [ha]
    exact (canonical22642 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1481 + difference 3 2) (sourceB1481 + difference 2 3) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1481 + difference 3 2) (sourceB1481 + difference 2 3) sourceC1481) = raw22643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22643; decide +kernel
    rw [ha]
    exact (canonical22643 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1481 + difference 3 4) (sourceB1481 + difference 4 3) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1481 + difference 3 4) (sourceB1481 + difference 4 3) sourceC1481) = raw22555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22555; decide +kernel
    rw [ha]
    exact (canonical22555 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1481 + difference 3 5) (sourceB1481 + difference 5 3) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1481 + difference 3 5) (sourceB1481 + difference 5 3) sourceC1481) = raw22644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22644; decide +kernel
    rw [ha]
    exact (canonical22644 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1481 + difference 4 0) (sourceB1481 + difference 0 4) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1095) := by
    have ha : (tripleCharges (sourceA1481 + difference 4 0) (sourceB1481 + difference 0 4) sourceC1481) = raw22645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22645; decide +kernel
    rw [ha]
    exact (canonical22645 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1481 + difference 4 1) (sourceB1481 + difference 1 4) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1481 + difference 4 1) (sourceB1481 + difference 1 4) sourceC1481) = raw22646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22646; decide +kernel
    rw [ha]
    exact (canonical22646 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1481 + difference 4 2) (sourceB1481 + difference 2 4) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1481 + difference 4 2) (sourceB1481 + difference 2 4) sourceC1481) = raw22647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22647; decide +kernel
    rw [ha]
    exact (canonical22647 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1481 + difference 4 3) (sourceB1481 + difference 3 4) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1481 + difference 4 3) (sourceB1481 + difference 3 4) sourceC1481) = raw22648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22648; decide +kernel
    rw [ha]
    exact (canonical22648 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1481 + difference 4 5) (sourceB1481 + difference 5 4) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1311) := by
    have ha : (tripleCharges (sourceA1481 + difference 4 5) (sourceB1481 + difference 5 4) sourceC1481) = raw22649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22649; decide +kernel
    rw [ha]
    exact (canonical22649 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1481 + difference 5 0) (sourceB1481 + difference 0 5) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1095) := by
    have ha : (tripleCharges (sourceA1481 + difference 5 0) (sourceB1481 + difference 0 5) sourceC1481) = raw22556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22556; decide +kernel
    rw [ha]
    exact (canonical22556 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1481 + difference 5 1) (sourceB1481 + difference 1 5) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1481 + difference 5 1) (sourceB1481 + difference 1 5) sourceC1481) = raw22557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22557; decide +kernel
    rw [ha]
    exact (canonical22557 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1481 + difference 5 2) (sourceB1481 + difference 2 5) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1481 + difference 5 2) (sourceB1481 + difference 2 5) sourceC1481) = raw22558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22558; decide +kernel
    rw [ha]
    exact (canonical22558 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1481 + difference 5 3) (sourceB1481 + difference 3 5) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1481 + difference 5 3) (sourceB1481 + difference 3 5) sourceC1481) = raw22559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22559; decide +kernel
    rw [ha]
    exact (canonical22559 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1481 + difference 5 4) (sourceB1481 + difference 4 5) sourceC1481) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1311) := by
    have ha : (tripleCharges (sourceA1481 + difference 5 4) (sourceB1481 + difference 4 5) sourceC1481) = raw22650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1481 sourceB1481 sourceC1481 difference raw22650; decide +kernel
    rw [ha]
    exact (canonical22650 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1481 sourceB1481 sourceC1481
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1481, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1482 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1482 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1482 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1482 : Integer.Sparse Master := [(Sum.inr 1751, 3), (Sum.inr 1755, 2), (Sum.inr 3312, 1), (Sum.inr 4071, -1)]

theorem sourceEq1482 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1482 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1482 + difference 0 0) (sourceB1482 + difference 0 0) sourceC1482) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3312) := by
    have ha : (tripleCharges (sourceA1482 + difference 0 0) (sourceB1482 + difference 0 0) sourceC1482) = raw22455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1482 sourceB1482 sourceC1482 difference raw22455; decide +kernel
    rw [ha]
    exact (canonical22455 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1482 + difference 0 1) (sourceB1482 + difference 1 0) sourceC1482) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1482 + difference 0 1) (sourceB1482 + difference 1 0) sourceC1482) = raw22452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1482 sourceB1482 sourceC1482 difference raw22452; decide +kernel
    rw [ha]
    exact (canonical22452 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1482 + difference 0 2) (sourceB1482 + difference 2 0) sourceC1482) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1482 + difference 0 2) (sourceB1482 + difference 2 0) sourceC1482) = raw22651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1482 sourceB1482 sourceC1482 difference raw22651; decide +kernel
    rw [ha]
    exact (canonical22651 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1482 + difference 0 3) (sourceB1482 + difference 3 0) sourceC1482) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1482 + difference 0 3) (sourceB1482 + difference 3 0) sourceC1482) = raw22652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1482 sourceB1482 sourceC1482 difference raw22652; decide +kernel
    rw [ha]
    exact (canonical22652 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1482 + difference 0 4) (sourceB1482 + difference 4 0) sourceC1482) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1755) := by
    have ha : (tripleCharges (sourceA1482 + difference 0 4) (sourceB1482 + difference 4 0) sourceC1482) = raw22653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1482 sourceB1482 sourceC1482 difference raw22653; decide +kernel
    rw [ha]
    exact (canonical22653 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1482 + difference 0 5) (sourceB1482 + difference 5 0) sourceC1482) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1755) := by
    have ha : (tripleCharges (sourceA1482 + difference 0 5) (sourceB1482 + difference 5 0) sourceC1482) = raw22654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1482 sourceB1482 sourceC1482 difference raw22654; decide +kernel
    rw [ha]
    exact (canonical22654 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1482 + sourceB1482) sourceC1482) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1482 + sourceB1482) sourceC1482) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1482 sourceB1482 sourceC1482 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1482 sourceB1482 sourceC1482
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1482, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1483 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1483 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1483 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm1483 : Integer.Sparse Master := [(Sum.inr 4158, 2), (Sum.inr 4160, 1), (Sum.inr 4161, 1), (Sum.inr 4188, 1), (Sum.inr 4533, 2), (Sum.inr 4534, 2), (Sum.inr 4535, 2), (Sum.inr 4549, 2), (Sum.inr 4556, 2), (Sum.inr 4558, 1), (Sum.inr 4559, 1), (Sum.inr 4602, 2), (Sum.inr 4603, 2), (Sum.inr 4608, 1), (Sum.inr 4609, 1), (Sum.inr 4619, 1), (Sum.inr 4620, 1), (Sum.inr 5111, 1), (Sum.inr 5141, 2), (Sum.inr 5274, 1), (Sum.inr 5275, 1)]

theorem sourceEq1483 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1483 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1483 + difference 0 1) (sourceB1483 + difference 1 0) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA1483 + difference 0 1) (sourceB1483 + difference 1 0) sourceC1483) = raw10363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10363; decide +kernel
    rw [ha]
    exact (canonical10363 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1483 + difference 0 2) (sourceB1483 + difference 2 0) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA1483 + difference 0 2) (sourceB1483 + difference 2 0) sourceC1483) = raw10364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10364; decide +kernel
    rw [ha]
    exact (canonical10364 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1483 + difference 0 3) (sourceB1483 + difference 3 0) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA1483 + difference 0 3) (sourceB1483 + difference 3 0) sourceC1483) = raw10365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10365; decide +kernel
    rw [ha]
    exact (canonical10365 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1483 + difference 0 4) (sourceB1483 + difference 4 0) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA1483 + difference 0 4) (sourceB1483 + difference 4 0) sourceC1483) = raw22655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22655; decide +kernel
    rw [ha]
    exact (canonical22655 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1483 + difference 0 5) (sourceB1483 + difference 5 0) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA1483 + difference 0 5) (sourceB1483 + difference 5 0) sourceC1483) = raw10366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10366; decide +kernel
    rw [ha]
    exact (canonical10366 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1483 + difference 1 0) (sourceB1483 + difference 0 1) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4158) := by
    have ha : (tripleCharges (sourceA1483 + difference 1 0) (sourceB1483 + difference 0 1) sourceC1483) = raw22656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22656; decide +kernel
    rw [ha]
    exact (canonical22656 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1483 + difference 1 2) (sourceB1483 + difference 2 1) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4533) := by
    have ha : (tripleCharges (sourceA1483 + difference 1 2) (sourceB1483 + difference 2 1) sourceC1483) = raw22657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22657; decide +kernel
    rw [ha]
    exact (canonical22657 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1483 + difference 1 3) (sourceB1483 + difference 3 1) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA1483 + difference 1 3) (sourceB1483 + difference 3 1) sourceC1483) = raw22658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22658; decide +kernel
    rw [ha]
    exact (canonical22658 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1483 + difference 1 4) (sourceB1483 + difference 4 1) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1483 + difference 1 4) (sourceB1483 + difference 4 1) sourceC1483) = raw10347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10347; decide +kernel
    rw [ha]
    exact (canonical10347 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1483 + difference 1 5) (sourceB1483 + difference 5 1) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1483 + difference 1 5) (sourceB1483 + difference 5 1) sourceC1483) = raw22659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22659; decide +kernel
    rw [ha]
    exact (canonical22659 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1483 + difference 2 0) (sourceB1483 + difference 0 2) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4158) := by
    have ha : (tripleCharges (sourceA1483 + difference 2 0) (sourceB1483 + difference 0 2) sourceC1483) = raw22660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22660; decide +kernel
    rw [ha]
    exact (canonical22660 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1483 + difference 2 1) (sourceB1483 + difference 1 2) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4533) := by
    have ha : (tripleCharges (sourceA1483 + difference 2 1) (sourceB1483 + difference 1 2) sourceC1483) = raw22661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22661; decide +kernel
    rw [ha]
    exact (canonical22661 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1483 + difference 2 3) (sourceB1483 + difference 3 2) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA1483 + difference 2 3) (sourceB1483 + difference 3 2) sourceC1483) = raw22662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22662; decide +kernel
    rw [ha]
    exact (canonical22662 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1483 + difference 2 4) (sourceB1483 + difference 4 2) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1483 + difference 2 4) (sourceB1483 + difference 4 2) sourceC1483) = raw10352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10352; decide +kernel
    rw [ha]
    exact (canonical10352 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1483 + difference 2 5) (sourceB1483 + difference 5 2) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1483 + difference 2 5) (sourceB1483 + difference 5 2) sourceC1483) = raw22663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22663; decide +kernel
    rw [ha]
    exact (canonical22663 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1483 + difference 3 0) (sourceB1483 + difference 0 3) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4188) := by
    have ha : (tripleCharges (sourceA1483 + difference 3 0) (sourceB1483 + difference 0 3) sourceC1483) = raw22664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22664; decide +kernel
    rw [ha]
    exact (canonical22664 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1483 + difference 3 1) (sourceB1483 + difference 1 3) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4556) := by
    have ha : (tripleCharges (sourceA1483 + difference 3 1) (sourceB1483 + difference 1 3) sourceC1483) = raw22665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22665; decide +kernel
    rw [ha]
    exact (canonical22665 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1483 + difference 3 2) (sourceB1483 + difference 2 3) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4556) := by
    have ha : (tripleCharges (sourceA1483 + difference 3 2) (sourceB1483 + difference 2 3) sourceC1483) = raw22666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22666; decide +kernel
    rw [ha]
    exact (canonical22666 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1483 + difference 3 4) (sourceB1483 + difference 4 3) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4620) := by
    have ha : (tripleCharges (sourceA1483 + difference 3 4) (sourceB1483 + difference 4 3) sourceC1483) = raw10357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10357; decide +kernel
    rw [ha]
    exact (canonical10357 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1483 + difference 3 5) (sourceB1483 + difference 5 3) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1483 + difference 3 5) (sourceB1483 + difference 5 3) sourceC1483) = raw22667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22667; decide +kernel
    rw [ha]
    exact (canonical22667 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1483 + difference 4 0) (sourceB1483 + difference 0 4) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4161) := by
    have ha : (tripleCharges (sourceA1483 + difference 4 0) (sourceB1483 + difference 0 4) sourceC1483) = raw22668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22668; decide +kernel
    rw [ha]
    exact (canonical22668 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1483 + difference 4 1) (sourceB1483 + difference 1 4) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA1483 + difference 4 1) (sourceB1483 + difference 1 4) sourceC1483) = raw22669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22669; decide +kernel
    rw [ha]
    exact (canonical22669 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1483 + difference 4 2) (sourceB1483 + difference 2 4) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA1483 + difference 4 2) (sourceB1483 + difference 2 4) sourceC1483) = raw22670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22670; decide +kernel
    rw [ha]
    exact (canonical22670 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1483 + difference 4 3) (sourceB1483 + difference 3 4) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1483 + difference 4 3) (sourceB1483 + difference 3 4) sourceC1483) = raw22671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22671; decide +kernel
    rw [ha]
    exact (canonical22671 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1483 + difference 4 5) (sourceB1483 + difference 5 4) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1483 + difference 4 5) (sourceB1483 + difference 5 4) sourceC1483) = raw22672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22672; decide +kernel
    rw [ha]
    exact (canonical22672 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1483 + difference 5 0) (sourceB1483 + difference 0 5) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4160) := by
    have ha : (tripleCharges (sourceA1483 + difference 5 0) (sourceB1483 + difference 0 5) sourceC1483) = raw22673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22673; decide +kernel
    rw [ha]
    exact (canonical22673 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1483 + difference 5 1) (sourceB1483 + difference 1 5) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4534) := by
    have ha : (tripleCharges (sourceA1483 + difference 5 1) (sourceB1483 + difference 1 5) sourceC1483) = raw22674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22674; decide +kernel
    rw [ha]
    exact (canonical22674 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1483 + difference 5 2) (sourceB1483 + difference 2 5) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4534) := by
    have ha : (tripleCharges (sourceA1483 + difference 5 2) (sourceB1483 + difference 2 5) sourceC1483) = raw22675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22675; decide +kernel
    rw [ha]
    exact (canonical22675 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1483 + difference 5 3) (sourceB1483 + difference 3 5) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4559) := by
    have ha : (tripleCharges (sourceA1483 + difference 5 3) (sourceB1483 + difference 3 5) sourceC1483) = raw22676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22676; decide +kernel
    rw [ha]
    exact (canonical22676 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1483 + difference 5 4) (sourceB1483 + difference 4 5) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1483 + difference 5 4) (sourceB1483 + difference 4 5) sourceC1483) = raw10367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10367; decide +kernel
    rw [ha]
    exact (canonical10367 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1483 sourceB1483 sourceC1483
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1483, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1484 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1484 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1484 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm1484 : Integer.Sparse Master := [(Sum.inr 586, 2), (Sum.inr 588, 1), (Sum.inr 589, 1), (Sum.inr 616, 1), (Sum.inr 1117, 2), (Sum.inr 1119, 2), (Sum.inr 1120, 2), (Sum.inr 1141, 2), (Sum.inr 1172, 2), (Sum.inr 1175, 1), (Sum.inr 1176, 1), (Sum.inr 1262, 2), (Sum.inr 1264, 1), (Sum.inr 1267, 2), (Sum.inr 1269, 1), (Sum.inr 1295, 1), (Sum.inr 1302, 1), (Sum.inr 2943, 2), (Sum.inr 3006, 1), (Sum.inr 3110, 1), (Sum.inr 3112, 1)]

theorem sourceEq1484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1484 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1484 + difference 0 1) (sourceB1484 + difference 1 0) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2943) := by
    have ha : (tripleCharges (sourceA1484 + difference 0 1) (sourceB1484 + difference 1 0) sourceC1484) = raw10393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw10393; decide +kernel
    rw [ha]
    exact (canonical10393 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1484 + difference 0 2) (sourceB1484 + difference 2 0) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2943) := by
    have ha : (tripleCharges (sourceA1484 + difference 0 2) (sourceB1484 + difference 2 0) sourceC1484) = raw10394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw10394; decide +kernel
    rw [ha]
    exact (canonical10394 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1484 + difference 0 3) (sourceB1484 + difference 3 0) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3006) := by
    have ha : (tripleCharges (sourceA1484 + difference 0 3) (sourceB1484 + difference 3 0) sourceC1484) = raw10395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw10395; decide +kernel
    rw [ha]
    exact (canonical10395 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1484 + difference 0 4) (sourceB1484 + difference 4 0) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA1484 + difference 0 4) (sourceB1484 + difference 4 0) sourceC1484) = raw22677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22677; decide +kernel
    rw [ha]
    exact (canonical22677 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1484 + difference 0 5) (sourceB1484 + difference 5 0) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA1484 + difference 0 5) (sourceB1484 + difference 5 0) sourceC1484) = raw10396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw10396; decide +kernel
    rw [ha]
    exact (canonical10396 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1484 + difference 1 0) (sourceB1484 + difference 0 1) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 586) := by
    have ha : (tripleCharges (sourceA1484 + difference 1 0) (sourceB1484 + difference 0 1) sourceC1484) = raw22678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22678; decide +kernel
    rw [ha]
    exact (canonical22678 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1484 + difference 1 2) (sourceB1484 + difference 2 1) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1117) := by
    have ha : (tripleCharges (sourceA1484 + difference 1 2) (sourceB1484 + difference 2 1) sourceC1484) = raw22679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22679; decide +kernel
    rw [ha]
    exact (canonical22679 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1484 + difference 1 3) (sourceB1484 + difference 3 1) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1172) := by
    have ha : (tripleCharges (sourceA1484 + difference 1 3) (sourceB1484 + difference 3 1) sourceC1484) = raw22680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22680; decide +kernel
    rw [ha]
    exact (canonical22680 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1484 + difference 1 4) (sourceB1484 + difference 4 1) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA1484 + difference 1 4) (sourceB1484 + difference 4 1) sourceC1484) = raw10377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw10377; decide +kernel
    rw [ha]
    exact (canonical10377 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1484 + difference 1 5) (sourceB1484 + difference 5 1) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1267) := by
    have ha : (tripleCharges (sourceA1484 + difference 1 5) (sourceB1484 + difference 5 1) sourceC1484) = raw22681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22681; decide +kernel
    rw [ha]
    exact (canonical22681 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1484 + difference 2 0) (sourceB1484 + difference 0 2) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 586) := by
    have ha : (tripleCharges (sourceA1484 + difference 2 0) (sourceB1484 + difference 0 2) sourceC1484) = raw22682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22682; decide +kernel
    rw [ha]
    exact (canonical22682 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1484 + difference 2 1) (sourceB1484 + difference 1 2) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1117) := by
    have ha : (tripleCharges (sourceA1484 + difference 2 1) (sourceB1484 + difference 1 2) sourceC1484) = raw22683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22683; decide +kernel
    rw [ha]
    exact (canonical22683 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1484 + difference 2 3) (sourceB1484 + difference 3 2) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1172) := by
    have ha : (tripleCharges (sourceA1484 + difference 2 3) (sourceB1484 + difference 3 2) sourceC1484) = raw22684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22684; decide +kernel
    rw [ha]
    exact (canonical22684 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1484 + difference 2 4) (sourceB1484 + difference 4 2) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA1484 + difference 2 4) (sourceB1484 + difference 4 2) sourceC1484) = raw10382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw10382; decide +kernel
    rw [ha]
    exact (canonical10382 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1484 + difference 2 5) (sourceB1484 + difference 5 2) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1267) := by
    have ha : (tripleCharges (sourceA1484 + difference 2 5) (sourceB1484 + difference 5 2) sourceC1484) = raw22685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22685; decide +kernel
    rw [ha]
    exact (canonical22685 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1484 + difference 3 0) (sourceB1484 + difference 0 3) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 616) := by
    have ha : (tripleCharges (sourceA1484 + difference 3 0) (sourceB1484 + difference 0 3) sourceC1484) = raw22686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22686; decide +kernel
    rw [ha]
    exact (canonical22686 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1484 + difference 3 1) (sourceB1484 + difference 1 3) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1141) := by
    have ha : (tripleCharges (sourceA1484 + difference 3 1) (sourceB1484 + difference 1 3) sourceC1484) = raw22687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22687; decide +kernel
    rw [ha]
    exact (canonical22687 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1484 + difference 3 2) (sourceB1484 + difference 2 3) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1141) := by
    have ha : (tripleCharges (sourceA1484 + difference 3 2) (sourceB1484 + difference 2 3) sourceC1484) = raw22688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22688; decide +kernel
    rw [ha]
    exact (canonical22688 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1484 + difference 3 4) (sourceB1484 + difference 4 3) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1295) := by
    have ha : (tripleCharges (sourceA1484 + difference 3 4) (sourceB1484 + difference 4 3) sourceC1484) = raw10387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw10387; decide +kernel
    rw [ha]
    exact (canonical10387 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1484 + difference 3 5) (sourceB1484 + difference 5 3) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1302) := by
    have ha : (tripleCharges (sourceA1484 + difference 3 5) (sourceB1484 + difference 5 3) sourceC1484) = raw22689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22689; decide +kernel
    rw [ha]
    exact (canonical22689 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1484 + difference 4 0) (sourceB1484 + difference 0 4) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 589) := by
    have ha : (tripleCharges (sourceA1484 + difference 4 0) (sourceB1484 + difference 0 4) sourceC1484) = raw22690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22690; decide +kernel
    rw [ha]
    exact (canonical22690 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1484 + difference 4 1) (sourceB1484 + difference 1 4) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1120) := by
    have ha : (tripleCharges (sourceA1484 + difference 4 1) (sourceB1484 + difference 1 4) sourceC1484) = raw22691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22691; decide +kernel
    rw [ha]
    exact (canonical22691 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1484 + difference 4 2) (sourceB1484 + difference 2 4) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1120) := by
    have ha : (tripleCharges (sourceA1484 + difference 4 2) (sourceB1484 + difference 2 4) sourceC1484) = raw22692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22692; decide +kernel
    rw [ha]
    exact (canonical22692 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1484 + difference 4 3) (sourceB1484 + difference 3 4) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1176) := by
    have ha : (tripleCharges (sourceA1484 + difference 4 3) (sourceB1484 + difference 3 4) sourceC1484) = raw22693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22693; decide +kernel
    rw [ha]
    exact (canonical22693 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1484 + difference 4 5) (sourceB1484 + difference 5 4) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1269) := by
    have ha : (tripleCharges (sourceA1484 + difference 4 5) (sourceB1484 + difference 5 4) sourceC1484) = raw22694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22694; decide +kernel
    rw [ha]
    exact (canonical22694 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1484 + difference 5 0) (sourceB1484 + difference 0 5) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 588) := by
    have ha : (tripleCharges (sourceA1484 + difference 5 0) (sourceB1484 + difference 0 5) sourceC1484) = raw22695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22695; decide +kernel
    rw [ha]
    exact (canonical22695 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1484 + difference 5 1) (sourceB1484 + difference 1 5) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1119) := by
    have ha : (tripleCharges (sourceA1484 + difference 5 1) (sourceB1484 + difference 1 5) sourceC1484) = raw22696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22696; decide +kernel
    rw [ha]
    exact (canonical22696 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1484 + difference 5 2) (sourceB1484 + difference 2 5) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1119) := by
    have ha : (tripleCharges (sourceA1484 + difference 5 2) (sourceB1484 + difference 2 5) sourceC1484) = raw22697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22697; decide +kernel
    rw [ha]
    exact (canonical22697 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1484 + difference 5 3) (sourceB1484 + difference 3 5) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1175) := by
    have ha : (tripleCharges (sourceA1484 + difference 5 3) (sourceB1484 + difference 3 5) sourceC1484) = raw22698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw22698; decide +kernel
    rw [ha]
    exact (canonical22698 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1484 + difference 5 4) (sourceB1484 + difference 4 5) sourceC1484) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1264) := by
    have ha : (tripleCharges (sourceA1484 + difference 5 4) (sourceB1484 + difference 4 5) sourceC1484) = raw10397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1484 sourceB1484 sourceC1484 difference raw10397; decide +kernel
    rw [ha]
    exact (canonical10397 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1484 sourceB1484 sourceC1484
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1484, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1485 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1485 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1485 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm1485 : Integer.Sparse Master := [(Sum.inr 1522, 2), (Sum.inr 1523, 1), (Sum.inr 1526, 1), (Sum.inr 1533, 1), (Sum.inr 3265, 2), (Sum.inr 3267, 2), (Sum.inr 3268, 2), (Sum.inr 3271, 2), (Sum.inr 3272, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 3293, 2), (Sum.inr 3294, 2), (Sum.inr 3300, 1), (Sum.inr 3302, 1), (Sum.inr 3305, 1), (Sum.inr 3306, 1), (Sum.inr 3485, 1), (Sum.inr 3522, 2), (Sum.inr 3547, 1), (Sum.inr 3548, 1)]

theorem sourceEq1485 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1485 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1485 + difference 0 1) (sourceB1485 + difference 1 0) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA1485 + difference 0 1) (sourceB1485 + difference 1 0) sourceC1485) = raw10423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10423; decide +kernel
    rw [ha]
    exact (canonical10423 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1485 + difference 0 2) (sourceB1485 + difference 2 0) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA1485 + difference 0 2) (sourceB1485 + difference 2 0) sourceC1485) = raw10424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10424; decide +kernel
    rw [ha]
    exact (canonical10424 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1485 + difference 0 3) (sourceB1485 + difference 3 0) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA1485 + difference 0 3) (sourceB1485 + difference 3 0) sourceC1485) = raw10425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10425; decide +kernel
    rw [ha]
    exact (canonical10425 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1485 + difference 0 4) (sourceB1485 + difference 4 0) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA1485 + difference 0 4) (sourceB1485 + difference 4 0) sourceC1485) = raw22699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22699; decide +kernel
    rw [ha]
    exact (canonical22699 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1485 + difference 0 5) (sourceB1485 + difference 5 0) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA1485 + difference 0 5) (sourceB1485 + difference 5 0) sourceC1485) = raw10426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10426; decide +kernel
    rw [ha]
    exact (canonical10426 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1485 + difference 1 0) (sourceB1485 + difference 0 1) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA1485 + difference 1 0) (sourceB1485 + difference 0 1) sourceC1485) = raw22700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22700; decide +kernel
    rw [ha]
    exact (canonical22700 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1485 + difference 1 2) (sourceB1485 + difference 2 1) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3267) := by
    have ha : (tripleCharges (sourceA1485 + difference 1 2) (sourceB1485 + difference 2 1) sourceC1485) = raw22701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22701; decide +kernel
    rw [ha]
    exact (canonical22701 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1485 + difference 1 3) (sourceB1485 + difference 3 1) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA1485 + difference 1 3) (sourceB1485 + difference 3 1) sourceC1485) = raw22702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22702; decide +kernel
    rw [ha]
    exact (canonical22702 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1485 + difference 1 4) (sourceB1485 + difference 4 1) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1485 + difference 1 4) (sourceB1485 + difference 4 1) sourceC1485) = raw10407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10407; decide +kernel
    rw [ha]
    exact (canonical10407 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1485 + difference 1 5) (sourceB1485 + difference 5 1) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1485 + difference 1 5) (sourceB1485 + difference 5 1) sourceC1485) = raw22703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22703; decide +kernel
    rw [ha]
    exact (canonical22703 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1485 + difference 2 0) (sourceB1485 + difference 0 2) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA1485 + difference 2 0) (sourceB1485 + difference 0 2) sourceC1485) = raw22704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22704; decide +kernel
    rw [ha]
    exact (canonical22704 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1485 + difference 2 1) (sourceB1485 + difference 1 2) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3267) := by
    have ha : (tripleCharges (sourceA1485 + difference 2 1) (sourceB1485 + difference 1 2) sourceC1485) = raw22705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22705; decide +kernel
    rw [ha]
    exact (canonical22705 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1485 + difference 2 3) (sourceB1485 + difference 3 2) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA1485 + difference 2 3) (sourceB1485 + difference 3 2) sourceC1485) = raw22706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22706; decide +kernel
    rw [ha]
    exact (canonical22706 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1485 + difference 2 4) (sourceB1485 + difference 4 2) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1485 + difference 2 4) (sourceB1485 + difference 4 2) sourceC1485) = raw10412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10412; decide +kernel
    rw [ha]
    exact (canonical10412 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1485 + difference 2 5) (sourceB1485 + difference 5 2) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1485 + difference 2 5) (sourceB1485 + difference 5 2) sourceC1485) = raw22707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22707; decide +kernel
    rw [ha]
    exact (canonical22707 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1485 + difference 3 0) (sourceB1485 + difference 0 3) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1526) := by
    have ha : (tripleCharges (sourceA1485 + difference 3 0) (sourceB1485 + difference 0 3) sourceC1485) = raw22708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22708; decide +kernel
    rw [ha]
    exact (canonical22708 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1485 + difference 3 1) (sourceB1485 + difference 1 3) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3271) := by
    have ha : (tripleCharges (sourceA1485 + difference 3 1) (sourceB1485 + difference 1 3) sourceC1485) = raw22709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22709; decide +kernel
    rw [ha]
    exact (canonical22709 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1485 + difference 3 2) (sourceB1485 + difference 2 3) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3271) := by
    have ha : (tripleCharges (sourceA1485 + difference 3 2) (sourceB1485 + difference 2 3) sourceC1485) = raw22710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22710; decide +kernel
    rw [ha]
    exact (canonical22710 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1485 + difference 3 4) (sourceB1485 + difference 4 3) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3306) := by
    have ha : (tripleCharges (sourceA1485 + difference 3 4) (sourceB1485 + difference 4 3) sourceC1485) = raw10417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10417; decide +kernel
    rw [ha]
    exact (canonical10417 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1485 + difference 3 5) (sourceB1485 + difference 5 3) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1485 + difference 3 5) (sourceB1485 + difference 5 3) sourceC1485) = raw22711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22711; decide +kernel
    rw [ha]
    exact (canonical22711 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1485 + difference 4 0) (sourceB1485 + difference 0 4) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA1485 + difference 4 0) (sourceB1485 + difference 0 4) sourceC1485) = raw22712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22712; decide +kernel
    rw [ha]
    exact (canonical22712 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1485 + difference 4 1) (sourceB1485 + difference 1 4) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA1485 + difference 4 1) (sourceB1485 + difference 1 4) sourceC1485) = raw22713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22713; decide +kernel
    rw [ha]
    exact (canonical22713 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1485 + difference 4 2) (sourceB1485 + difference 2 4) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA1485 + difference 4 2) (sourceB1485 + difference 2 4) sourceC1485) = raw22714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22714; decide +kernel
    rw [ha]
    exact (canonical22714 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1485 + difference 4 3) (sourceB1485 + difference 3 4) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA1485 + difference 4 3) (sourceB1485 + difference 3 4) sourceC1485) = raw22715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22715; decide +kernel
    rw [ha]
    exact (canonical22715 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1485 + difference 4 5) (sourceB1485 + difference 5 4) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1485 + difference 4 5) (sourceB1485 + difference 5 4) sourceC1485) = raw22716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22716; decide +kernel
    rw [ha]
    exact (canonical22716 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1485 + difference 5 0) (sourceB1485 + difference 0 5) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1523) := by
    have ha : (tripleCharges (sourceA1485 + difference 5 0) (sourceB1485 + difference 0 5) sourceC1485) = raw22717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22717; decide +kernel
    rw [ha]
    exact (canonical22717 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1485 + difference 5 1) (sourceB1485 + difference 1 5) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3268) := by
    have ha : (tripleCharges (sourceA1485 + difference 5 1) (sourceB1485 + difference 1 5) sourceC1485) = raw22718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22718; decide +kernel
    rw [ha]
    exact (canonical22718 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1485 + difference 5 2) (sourceB1485 + difference 2 5) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3268) := by
    have ha : (tripleCharges (sourceA1485 + difference 5 2) (sourceB1485 + difference 2 5) sourceC1485) = raw22719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22719; decide +kernel
    rw [ha]
    exact (canonical22719 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1485 + difference 5 3) (sourceB1485 + difference 3 5) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA1485 + difference 5 3) (sourceB1485 + difference 3 5) sourceC1485) = raw22720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22720; decide +kernel
    rw [ha]
    exact (canonical22720 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1485 + difference 5 4) (sourceB1485 + difference 4 5) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1485 + difference 5 4) (sourceB1485 + difference 4 5) sourceC1485) = raw10427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10427; decide +kernel
    rw [ha]
    exact (canonical10427 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1485 sourceB1485 sourceC1485
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1485, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1486 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1486 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1486 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm1486 : Integer.Sparse Master := [(Sum.inr 627, 2), (Sum.inr 635, 1), (Sum.inr 636, 1), (Sum.inr 642, 1), (Sum.inr 1246, 1), (Sum.inr 4092, -1)]

theorem sourceEq1486 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1486 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1486 + difference 0 0) (sourceB1486 + difference 0 0) sourceC1486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1486 + difference 0 0) (sourceB1486 + difference 0 0) sourceC1486) = raw10447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1486 sourceB1486 sourceC1486 difference raw10447; decide +kernel
    rw [ha]
    exact (canonical10447 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1486 + difference 1 0) (sourceB1486 + difference 0 1) sourceC1486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 627) := by
    have ha : (tripleCharges (sourceA1486 + difference 1 0) (sourceB1486 + difference 0 1) sourceC1486) = raw22721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1486 sourceB1486 sourceC1486 difference raw22721; decide +kernel
    rw [ha]
    exact (canonical22721 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1486 + difference 2 0) (sourceB1486 + difference 0 2) sourceC1486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 627) := by
    have ha : (tripleCharges (sourceA1486 + difference 2 0) (sourceB1486 + difference 0 2) sourceC1486) = raw22722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1486 sourceB1486 sourceC1486 difference raw22722; decide +kernel
    rw [ha]
    exact (canonical22722 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1486 + difference 3 0) (sourceB1486 + difference 0 3) sourceC1486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 642) := by
    have ha : (tripleCharges (sourceA1486 + difference 3 0) (sourceB1486 + difference 0 3) sourceC1486) = raw22723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1486 sourceB1486 sourceC1486 difference raw22723; decide +kernel
    rw [ha]
    exact (canonical22723 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1486 + difference 4 0) (sourceB1486 + difference 0 4) sourceC1486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 635) := by
    have ha : (tripleCharges (sourceA1486 + difference 4 0) (sourceB1486 + difference 0 4) sourceC1486) = raw22724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1486 sourceB1486 sourceC1486 difference raw22724; decide +kernel
    rw [ha]
    exact (canonical22724 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1486 + difference 5 0) (sourceB1486 + difference 0 5) sourceC1486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 636) := by
    have ha : (tripleCharges (sourceA1486 + difference 5 0) (sourceB1486 + difference 0 5) sourceC1486) = raw22725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1486 sourceB1486 sourceC1486 difference raw22725; decide +kernel
    rw [ha]
    exact (canonical22725 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1486 + sourceB1486) sourceC1486) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1486 + sourceB1486) sourceC1486) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA1486 sourceB1486 sourceC1486 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1486 sourceB1486 sourceC1486
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1486, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1487 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1487 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1487 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm1487 : Integer.Sparse Master := [(Sum.inr 627, 1), (Sum.inr 1134, 1), (Sum.inr 1149, 1), (Sum.inr 1236, 1), (Sum.inr 1237, 1), (Sum.inr 1246, 1), (Sum.inr 4092, -1)]

theorem sourceEq1487 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1487 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1487 + difference 1 0) (sourceB1487 + difference 0 1) sourceC1487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 627) := by
    have ha : (tripleCharges (sourceA1487 + difference 1 0) (sourceB1487 + difference 0 1) sourceC1487) = raw22721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1487 sourceB1487 sourceC1487 difference raw22721; decide +kernel
    rw [ha]
    exact (canonical22721 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1487 + difference 1 1) (sourceB1487 + difference 1 1) sourceC1487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1487 + difference 1 1) (sourceB1487 + difference 1 1) sourceC1487) = raw10447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1487 sourceB1487 sourceC1487 difference raw10447; decide +kernel
    rw [ha]
    exact (canonical10447 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1487 + difference 1 2) (sourceB1487 + difference 2 1) sourceC1487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1149) := by
    have ha : (tripleCharges (sourceA1487 + difference 1 2) (sourceB1487 + difference 2 1) sourceC1487) = raw22726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1487 sourceB1487 sourceC1487 difference raw22726; decide +kernel
    rw [ha]
    exact (canonical22726 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1487 + difference 1 3) (sourceB1487 + difference 3 1) sourceC1487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA1487 + difference 1 3) (sourceB1487 + difference 3 1) sourceC1487) = raw22727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1487 sourceB1487 sourceC1487 difference raw22727; decide +kernel
    rw [ha]
    exact (canonical22727 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1487 + difference 1 4) (sourceB1487 + difference 4 1) sourceC1487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA1487 + difference 1 4) (sourceB1487 + difference 4 1) sourceC1487) = raw22728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1487 sourceB1487 sourceC1487 difference raw22728; decide +kernel
    rw [ha]
    exact (canonical22728 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1487 + difference 1 5) (sourceB1487 + difference 5 1) sourceC1487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1487 + difference 1 5) (sourceB1487 + difference 5 1) sourceC1487) = raw22729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1487 sourceB1487 sourceC1487 difference raw22729; decide +kernel
    rw [ha]
    exact (canonical22729 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1487 + sourceB1487) sourceC1487) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1487 + sourceB1487) sourceC1487) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA1487 sourceB1487 sourceC1487 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1487 sourceB1487 sourceC1487
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1487, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1488 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1488 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1488 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm1488 : Integer.Sparse Master := [(Sum.inr 1149, 1), (Sum.inr 1154, 1), (Sum.inr 1155, 1), (Sum.inr 1160, 1), (Sum.inr 1246, 1), (Sum.inr 2561, 1), (Sum.inr 4092, -1)]

theorem sourceEq1488 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1488 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1488 + difference 0 1) (sourceB1488 + difference 1 0) sourceC1488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA1488 + difference 0 1) (sourceB1488 + difference 1 0) sourceC1488) = raw10441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1488 sourceB1488 sourceC1488 difference raw10441; decide +kernel
    rw [ha]
    exact (canonical10441 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1488 + difference 1 1) (sourceB1488 + difference 1 1) sourceC1488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1488 + difference 1 1) (sourceB1488 + difference 1 1) sourceC1488) = raw10447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1488 sourceB1488 sourceC1488 difference raw10447; decide +kernel
    rw [ha]
    exact (canonical10447 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1488 + difference 2 1) (sourceB1488 + difference 1 2) sourceC1488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1149) := by
    have ha : (tripleCharges (sourceA1488 + difference 2 1) (sourceB1488 + difference 1 2) sourceC1488) = raw22730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1488 sourceB1488 sourceC1488 difference raw22730; decide +kernel
    rw [ha]
    exact (canonical22730 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1488 + difference 3 1) (sourceB1488 + difference 1 3) sourceC1488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1160) := by
    have ha : (tripleCharges (sourceA1488 + difference 3 1) (sourceB1488 + difference 1 3) sourceC1488) = raw22731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1488 sourceB1488 sourceC1488 difference raw22731; decide +kernel
    rw [ha]
    exact (canonical22731 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1488 + difference 4 1) (sourceB1488 + difference 1 4) sourceC1488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1154) := by
    have ha : (tripleCharges (sourceA1488 + difference 4 1) (sourceB1488 + difference 1 4) sourceC1488) = raw22732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1488 sourceB1488 sourceC1488 difference raw22732; decide +kernel
    rw [ha]
    exact (canonical22732 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1488 + difference 5 1) (sourceB1488 + difference 1 5) sourceC1488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1155) := by
    have ha : (tripleCharges (sourceA1488 + difference 5 1) (sourceB1488 + difference 1 5) sourceC1488) = raw22733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1488 sourceB1488 sourceC1488 difference raw22733; decide +kernel
    rw [ha]
    exact (canonical22733 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1488 + sourceB1488) sourceC1488) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1488 + sourceB1488) sourceC1488) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA1488 sourceB1488 sourceC1488 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1488 sourceB1488 sourceC1488
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1488, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1489 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1489 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1489 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm1489 : Integer.Sparse Master := [(Sum.inr 642, 1), (Sum.inr 1160, 2), (Sum.inr 1246, 1), (Sum.inr 1294, 1), (Sum.inr 1295, 1), (Sum.inr 4092, -1)]

theorem sourceEq1489 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1489 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1489 + difference 3 0) (sourceB1489 + difference 0 3) sourceC1489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 642) := by
    have ha : (tripleCharges (sourceA1489 + difference 3 0) (sourceB1489 + difference 0 3) sourceC1489) = raw22723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1489 sourceB1489 sourceC1489 difference raw22723; decide +kernel
    rw [ha]
    exact (canonical22723 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1489 + difference 3 1) (sourceB1489 + difference 1 3) sourceC1489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1160) := by
    have ha : (tripleCharges (sourceA1489 + difference 3 1) (sourceB1489 + difference 1 3) sourceC1489) = raw22731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1489 sourceB1489 sourceC1489 difference raw22731; decide +kernel
    rw [ha]
    exact (canonical22731 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1489 + difference 3 2) (sourceB1489 + difference 2 3) sourceC1489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1160) := by
    have ha : (tripleCharges (sourceA1489 + difference 3 2) (sourceB1489 + difference 2 3) sourceC1489) = raw22734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1489 sourceB1489 sourceC1489 difference raw22734; decide +kernel
    rw [ha]
    exact (canonical22734 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1489 + difference 3 3) (sourceB1489 + difference 3 3) sourceC1489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1489 + difference 3 3) (sourceB1489 + difference 3 3) sourceC1489) = raw10447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1489 sourceB1489 sourceC1489 difference raw10447; decide +kernel
    rw [ha]
    exact (canonical10447 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1489 + difference 3 4) (sourceB1489 + difference 4 3) sourceC1489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1295) := by
    have ha : (tripleCharges (sourceA1489 + difference 3 4) (sourceB1489 + difference 4 3) sourceC1489) = raw22735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1489 sourceB1489 sourceC1489 difference raw22735; decide +kernel
    rw [ha]
    exact (canonical22735 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1489 + difference 3 5) (sourceB1489 + difference 5 3) sourceC1489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1489 + difference 3 5) (sourceB1489 + difference 5 3) sourceC1489) = raw22736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1489 sourceB1489 sourceC1489 difference raw22736; decide +kernel
    rw [ha]
    exact (canonical22736 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1489 + sourceB1489) sourceC1489) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1489 + sourceB1489) sourceC1489) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA1489 sourceB1489 sourceC1489 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1489 sourceB1489 sourceC1489
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1489, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1490 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1490 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC1490 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceForm1490 : Integer.Sparse Master := [(Sum.inr 4145, 2), (Sum.inr 4147, 1), (Sum.inr 4148, 1), (Sum.inr 4180, 1), (Sum.inr 4518, 2), (Sum.inr 4519, 1), (Sum.inr 4520, 1), (Sum.inr 4524, 2), (Sum.inr 4525, 2), (Sum.inr 4526, 2), (Sum.inr 4549, 2), (Sum.inr 4602, 2), (Sum.inr 4605, 1), (Sum.inr 4606, 2), (Sum.inr 4608, 1), (Sum.inr 4623, 1), (Sum.inr 4624, 1), (Sum.inr 5152, 2), (Sum.inr 5207, 1), (Sum.inr 5293, 1), (Sum.inr 5294, 1)]

theorem sourceEq1490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1490 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1490 + difference 0 1) (sourceB1490 + difference 1 0) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA1490 + difference 0 1) (sourceB1490 + difference 1 0) sourceC1490) = raw7827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw7827; decide +kernel
    rw [ha]
    exact (canonical7827 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1490 + difference 0 2) (sourceB1490 + difference 2 0) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA1490 + difference 0 2) (sourceB1490 + difference 2 0) sourceC1490) = raw7828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw7828; decide +kernel
    rw [ha]
    exact (canonical7828 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1490 + difference 0 3) (sourceB1490 + difference 3 0) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA1490 + difference 0 3) (sourceB1490 + difference 3 0) sourceC1490) = raw7829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw7829; decide +kernel
    rw [ha]
    exact (canonical7829 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1490 + difference 0 4) (sourceB1490 + difference 4 0) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1490 + difference 0 4) (sourceB1490 + difference 4 0) sourceC1490) = raw15022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw15022; decide +kernel
    rw [ha]
    exact (canonical15022 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1490 + difference 0 5) (sourceB1490 + difference 5 0) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1490 + difference 0 5) (sourceB1490 + difference 5 0) sourceC1490) = raw7830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw7830; decide +kernel
    rw [ha]
    exact (canonical7830 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1490 + difference 1 0) (sourceB1490 + difference 0 1) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4145) := by
    have ha : (tripleCharges (sourceA1490 + difference 1 0) (sourceB1490 + difference 0 1) sourceC1490) = raw22737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22737; decide +kernel
    rw [ha]
    exact (canonical22737 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1490 + difference 1 2) (sourceB1490 + difference 2 1) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4524) := by
    have ha : (tripleCharges (sourceA1490 + difference 1 2) (sourceB1490 + difference 2 1) sourceC1490) = raw22738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22738; decide +kernel
    rw [ha]
    exact (canonical22738 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1490 + difference 1 3) (sourceB1490 + difference 3 1) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4518) := by
    have ha : (tripleCharges (sourceA1490 + difference 1 3) (sourceB1490 + difference 3 1) sourceC1490) = raw22739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22739; decide +kernel
    rw [ha]
    exact (canonical22739 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1490 + difference 1 4) (sourceB1490 + difference 4 1) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1490 + difference 1 4) (sourceB1490 + difference 4 1) sourceC1490) = raw7811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw7811; decide +kernel
    rw [ha]
    exact (canonical7811 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1490 + difference 1 5) (sourceB1490 + difference 5 1) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1490 + difference 1 5) (sourceB1490 + difference 5 1) sourceC1490) = raw22740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22740; decide +kernel
    rw [ha]
    exact (canonical22740 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1490 + difference 2 0) (sourceB1490 + difference 0 2) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4145) := by
    have ha : (tripleCharges (sourceA1490 + difference 2 0) (sourceB1490 + difference 0 2) sourceC1490) = raw22741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22741; decide +kernel
    rw [ha]
    exact (canonical22741 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1490 + difference 2 1) (sourceB1490 + difference 1 2) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4524) := by
    have ha : (tripleCharges (sourceA1490 + difference 2 1) (sourceB1490 + difference 1 2) sourceC1490) = raw22742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22742; decide +kernel
    rw [ha]
    exact (canonical22742 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1490 + difference 2 3) (sourceB1490 + difference 3 2) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4518) := by
    have ha : (tripleCharges (sourceA1490 + difference 2 3) (sourceB1490 + difference 3 2) sourceC1490) = raw22743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22743; decide +kernel
    rw [ha]
    exact (canonical22743 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1490 + difference 2 4) (sourceB1490 + difference 4 2) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1490 + difference 2 4) (sourceB1490 + difference 4 2) sourceC1490) = raw7816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw7816; decide +kernel
    rw [ha]
    exact (canonical7816 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1490 + difference 2 5) (sourceB1490 + difference 5 2) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1490 + difference 2 5) (sourceB1490 + difference 5 2) sourceC1490) = raw22744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22744; decide +kernel
    rw [ha]
    exact (canonical22744 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1490 + difference 3 0) (sourceB1490 + difference 0 3) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4180) := by
    have ha : (tripleCharges (sourceA1490 + difference 3 0) (sourceB1490 + difference 0 3) sourceC1490) = raw22745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22745; decide +kernel
    rw [ha]
    exact (canonical22745 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1490 + difference 3 1) (sourceB1490 + difference 1 3) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA1490 + difference 3 1) (sourceB1490 + difference 1 3) sourceC1490) = raw22746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22746; decide +kernel
    rw [ha]
    exact (canonical22746 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1490 + difference 3 2) (sourceB1490 + difference 2 3) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA1490 + difference 3 2) (sourceB1490 + difference 2 3) sourceC1490) = raw22747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22747; decide +kernel
    rw [ha]
    exact (canonical22747 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1490 + difference 3 4) (sourceB1490 + difference 4 3) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1490 + difference 3 4) (sourceB1490 + difference 4 3) sourceC1490) = raw7821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw7821; decide +kernel
    rw [ha]
    exact (canonical7821 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1490 + difference 3 5) (sourceB1490 + difference 5 3) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1490 + difference 3 5) (sourceB1490 + difference 5 3) sourceC1490) = raw22748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22748; decide +kernel
    rw [ha]
    exact (canonical22748 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1490 + difference 4 0) (sourceB1490 + difference 0 4) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4147) := by
    have ha : (tripleCharges (sourceA1490 + difference 4 0) (sourceB1490 + difference 0 4) sourceC1490) = raw22749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22749; decide +kernel
    rw [ha]
    exact (canonical22749 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1490 + difference 4 1) (sourceB1490 + difference 1 4) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4525) := by
    have ha : (tripleCharges (sourceA1490 + difference 4 1) (sourceB1490 + difference 1 4) sourceC1490) = raw22750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22750; decide +kernel
    rw [ha]
    exact (canonical22750 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1490 + difference 4 2) (sourceB1490 + difference 2 4) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4525) := by
    have ha : (tripleCharges (sourceA1490 + difference 4 2) (sourceB1490 + difference 2 4) sourceC1490) = raw22751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22751; decide +kernel
    rw [ha]
    exact (canonical22751 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1490 + difference 4 3) (sourceB1490 + difference 3 4) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4519) := by
    have ha : (tripleCharges (sourceA1490 + difference 4 3) (sourceB1490 + difference 3 4) sourceC1490) = raw22752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22752; decide +kernel
    rw [ha]
    exact (canonical22752 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1490 + difference 4 5) (sourceB1490 + difference 5 4) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1490 + difference 4 5) (sourceB1490 + difference 5 4) sourceC1490) = raw22753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw22753; decide +kernel
    rw [ha]
    exact (canonical22753 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1490 + difference 5 0) (sourceB1490 + difference 0 5) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4148) := by
    have ha : (tripleCharges (sourceA1490 + difference 5 0) (sourceB1490 + difference 0 5) sourceC1490) = raw20761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw20761; decide +kernel
    rw [ha]
    exact (canonical20761 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1490 + difference 5 1) (sourceB1490 + difference 1 5) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4526) := by
    have ha : (tripleCharges (sourceA1490 + difference 5 1) (sourceB1490 + difference 1 5) sourceC1490) = raw20762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw20762; decide +kernel
    rw [ha]
    exact (canonical20762 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1490 + difference 5 2) (sourceB1490 + difference 2 5) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4526) := by
    have ha : (tripleCharges (sourceA1490 + difference 5 2) (sourceB1490 + difference 2 5) sourceC1490) = raw20763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw20763; decide +kernel
    rw [ha]
    exact (canonical20763 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1490 + difference 5 3) (sourceB1490 + difference 3 5) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4520) := by
    have ha : (tripleCharges (sourceA1490 + difference 5 3) (sourceB1490 + difference 3 5) sourceC1490) = raw20764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw20764; decide +kernel
    rw [ha]
    exact (canonical20764 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1490 + difference 5 4) (sourceB1490 + difference 4 5) sourceC1490) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1490 + difference 5 4) (sourceB1490 + difference 4 5) sourceC1490) = raw7831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1490 sourceB1490 sourceC1490 difference raw7831; decide +kernel
    rw [ha]
    exact (canonical7831 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1490 sourceB1490 sourceC1490
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1490, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1491 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1491 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC1491 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceForm1491 : Integer.Sparse Master := [(Sum.inr 573, 2), (Sum.inr 575, 1), (Sum.inr 576, 1), (Sum.inr 608, 1), (Sum.inr 1102, 2), (Sum.inr 1103, 1), (Sum.inr 1104, 1), (Sum.inr 1108, 2), (Sum.inr 1109, 2), (Sum.inr 1110, 2), (Sum.inr 1134, 2), (Sum.inr 1236, 2), (Sum.inr 1239, 1), (Sum.inr 1240, 2), (Sum.inr 1242, 1), (Sum.inr 1300, 1), (Sum.inr 1301, 1), (Sum.inr 2889, 1), (Sum.inr 2931, 2), (Sum.inr 3101, 1), (Sum.inr 3102, 1)]

theorem sourceEq1491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1491 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1491 + difference 0 1) (sourceB1491 + difference 1 0) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA1491 + difference 0 1) (sourceB1491 + difference 1 0) sourceC1491) = raw7857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw7857; decide +kernel
    rw [ha]
    exact (canonical7857 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1491 + difference 0 2) (sourceB1491 + difference 2 0) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA1491 + difference 0 2) (sourceB1491 + difference 2 0) sourceC1491) = raw7858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw7858; decide +kernel
    rw [ha]
    exact (canonical7858 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1491 + difference 0 3) (sourceB1491 + difference 3 0) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA1491 + difference 0 3) (sourceB1491 + difference 3 0) sourceC1491) = raw7859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw7859; decide +kernel
    rw [ha]
    exact (canonical7859 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1491 + difference 0 4) (sourceB1491 + difference 4 0) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA1491 + difference 0 4) (sourceB1491 + difference 4 0) sourceC1491) = raw15044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw15044; decide +kernel
    rw [ha]
    exact (canonical15044 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1491 + difference 0 5) (sourceB1491 + difference 5 0) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA1491 + difference 0 5) (sourceB1491 + difference 5 0) sourceC1491) = raw7860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw7860; decide +kernel
    rw [ha]
    exact (canonical7860 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1491 + difference 1 0) (sourceB1491 + difference 0 1) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 573) := by
    have ha : (tripleCharges (sourceA1491 + difference 1 0) (sourceB1491 + difference 0 1) sourceC1491) = raw22754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22754; decide +kernel
    rw [ha]
    exact (canonical22754 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1491 + difference 1 2) (sourceB1491 + difference 2 1) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1108) := by
    have ha : (tripleCharges (sourceA1491 + difference 1 2) (sourceB1491 + difference 2 1) sourceC1491) = raw22755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22755; decide +kernel
    rw [ha]
    exact (canonical22755 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1491 + difference 1 3) (sourceB1491 + difference 3 1) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1102) := by
    have ha : (tripleCharges (sourceA1491 + difference 1 3) (sourceB1491 + difference 3 1) sourceC1491) = raw22756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22756; decide +kernel
    rw [ha]
    exact (canonical22756 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1491 + difference 1 4) (sourceB1491 + difference 4 1) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1491 + difference 1 4) (sourceB1491 + difference 4 1) sourceC1491) = raw7841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw7841; decide +kernel
    rw [ha]
    exact (canonical7841 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1491 + difference 1 5) (sourceB1491 + difference 5 1) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1491 + difference 1 5) (sourceB1491 + difference 5 1) sourceC1491) = raw22757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22757; decide +kernel
    rw [ha]
    exact (canonical22757 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1491 + difference 2 0) (sourceB1491 + difference 0 2) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 573) := by
    have ha : (tripleCharges (sourceA1491 + difference 2 0) (sourceB1491 + difference 0 2) sourceC1491) = raw22758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22758; decide +kernel
    rw [ha]
    exact (canonical22758 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1491 + difference 2 1) (sourceB1491 + difference 1 2) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1108) := by
    have ha : (tripleCharges (sourceA1491 + difference 2 1) (sourceB1491 + difference 1 2) sourceC1491) = raw22759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22759; decide +kernel
    rw [ha]
    exact (canonical22759 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1491 + difference 2 3) (sourceB1491 + difference 3 2) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1102) := by
    have ha : (tripleCharges (sourceA1491 + difference 2 3) (sourceB1491 + difference 3 2) sourceC1491) = raw22760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22760; decide +kernel
    rw [ha]
    exact (canonical22760 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1491 + difference 2 4) (sourceB1491 + difference 4 2) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1491 + difference 2 4) (sourceB1491 + difference 4 2) sourceC1491) = raw7846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw7846; decide +kernel
    rw [ha]
    exact (canonical7846 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1491 + difference 2 5) (sourceB1491 + difference 5 2) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1491 + difference 2 5) (sourceB1491 + difference 5 2) sourceC1491) = raw22761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22761; decide +kernel
    rw [ha]
    exact (canonical22761 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1491 + difference 3 0) (sourceB1491 + difference 0 3) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 608) := by
    have ha : (tripleCharges (sourceA1491 + difference 3 0) (sourceB1491 + difference 0 3) sourceC1491) = raw22762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22762; decide +kernel
    rw [ha]
    exact (canonical22762 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1491 + difference 3 1) (sourceB1491 + difference 1 3) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA1491 + difference 3 1) (sourceB1491 + difference 1 3) sourceC1491) = raw22763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22763; decide +kernel
    rw [ha]
    exact (canonical22763 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1491 + difference 3 2) (sourceB1491 + difference 2 3) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA1491 + difference 3 2) (sourceB1491 + difference 2 3) sourceC1491) = raw22764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22764; decide +kernel
    rw [ha]
    exact (canonical22764 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1491 + difference 3 4) (sourceB1491 + difference 4 3) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1491 + difference 3 4) (sourceB1491 + difference 4 3) sourceC1491) = raw7851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw7851; decide +kernel
    rw [ha]
    exact (canonical7851 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1491 + difference 3 5) (sourceB1491 + difference 5 3) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1300) := by
    have ha : (tripleCharges (sourceA1491 + difference 3 5) (sourceB1491 + difference 5 3) sourceC1491) = raw22765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22765; decide +kernel
    rw [ha]
    exact (canonical22765 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1491 + difference 4 0) (sourceB1491 + difference 0 4) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 575) := by
    have ha : (tripleCharges (sourceA1491 + difference 4 0) (sourceB1491 + difference 0 4) sourceC1491) = raw22766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22766; decide +kernel
    rw [ha]
    exact (canonical22766 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1491 + difference 4 1) (sourceB1491 + difference 1 4) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1109) := by
    have ha : (tripleCharges (sourceA1491 + difference 4 1) (sourceB1491 + difference 1 4) sourceC1491) = raw22767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22767; decide +kernel
    rw [ha]
    exact (canonical22767 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1491 + difference 4 2) (sourceB1491 + difference 2 4) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1109) := by
    have ha : (tripleCharges (sourceA1491 + difference 4 2) (sourceB1491 + difference 2 4) sourceC1491) = raw22768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22768; decide +kernel
    rw [ha]
    exact (canonical22768 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1491 + difference 4 3) (sourceB1491 + difference 3 4) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1103) := by
    have ha : (tripleCharges (sourceA1491 + difference 4 3) (sourceB1491 + difference 3 4) sourceC1491) = raw22769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22769; decide +kernel
    rw [ha]
    exact (canonical22769 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1491 + difference 4 5) (sourceB1491 + difference 5 4) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1491 + difference 4 5) (sourceB1491 + difference 5 4) sourceC1491) = raw22770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw22770; decide +kernel
    rw [ha]
    exact (canonical22770 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1491 + difference 5 0) (sourceB1491 + difference 0 5) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 576) := by
    have ha : (tripleCharges (sourceA1491 + difference 5 0) (sourceB1491 + difference 0 5) sourceC1491) = raw20782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw20782; decide +kernel
    rw [ha]
    exact (canonical20782 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1491 + difference 5 1) (sourceB1491 + difference 1 5) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1110) := by
    have ha : (tripleCharges (sourceA1491 + difference 5 1) (sourceB1491 + difference 1 5) sourceC1491) = raw20783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw20783; decide +kernel
    rw [ha]
    exact (canonical20783 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1491 + difference 5 2) (sourceB1491 + difference 2 5) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1110) := by
    have ha : (tripleCharges (sourceA1491 + difference 5 2) (sourceB1491 + difference 2 5) sourceC1491) = raw20784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw20784; decide +kernel
    rw [ha]
    exact (canonical20784 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1491 + difference 5 3) (sourceB1491 + difference 3 5) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1104) := by
    have ha : (tripleCharges (sourceA1491 + difference 5 3) (sourceB1491 + difference 3 5) sourceC1491) = raw20785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw20785; decide +kernel
    rw [ha]
    exact (canonical20785 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1491 + difference 5 4) (sourceB1491 + difference 4 5) sourceC1491) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1491 + difference 5 4) (sourceB1491 + difference 4 5) sourceC1491) = raw7861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1491 sourceB1491 sourceC1491 difference raw7861; decide +kernel
    rw [ha]
    exact (canonical7861 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1491 sourceB1491 sourceC1491
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1491, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1492 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceB1492 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC1492 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1492 : Integer.Sparse Master := [(Sum.inr 4404, 2), (Sum.inr 4431, 1), (Sum.inr 4432, 1), (Sum.inr 4444, 2), (Sum.inr 4466, 1), (Sum.inr 4467, 1), (Sum.inr 4480, 1), (Sum.inr 4511, 1), (Sum.inr 4565, 2), (Sum.inr 4574, 1), (Sum.inr 4575, 1), (Sum.inr 4578, 2), (Sum.inr 4585, 2), (Sum.inr 4586, 2), (Sum.inr 4592, 2), (Sum.inr 4593, 2), (Sum.inr 4611, 1), (Sum.inr 4612, 3), (Sum.inr 4627, 1), (Sum.inr 4628, 1)]

theorem sourceEq1492 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1492 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1492 + difference 0 1) (sourceB1492 + difference 1 0) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA1492 + difference 0 1) (sourceB1492 + difference 1 0) sourceC1492) = raw22771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22771; decide +kernel
    rw [ha]
    exact (canonical22771 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1492 + difference 0 2) (sourceB1492 + difference 2 0) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA1492 + difference 0 2) (sourceB1492 + difference 2 0) sourceC1492) = raw22772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22772; decide +kernel
    rw [ha]
    exact (canonical22772 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1492 + difference 0 3) (sourceB1492 + difference 3 0) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4480) := by
    have ha : (tripleCharges (sourceA1492 + difference 0 3) (sourceB1492 + difference 3 0) sourceC1492) = raw22773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22773; decide +kernel
    rw [ha]
    exact (canonical22773 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1492 + difference 0 4) (sourceB1492 + difference 4 0) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1492 + difference 0 4) (sourceB1492 + difference 4 0) sourceC1492) = raw22609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22609; decide +kernel
    rw [ha]
    exact (canonical22609 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1492 + difference 0 5) (sourceB1492 + difference 5 0) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1492 + difference 0 5) (sourceB1492 + difference 5 0) sourceC1492) = raw22774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22774; decide +kernel
    rw [ha]
    exact (canonical22774 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1492 + difference 1 0) (sourceB1492 + difference 0 1) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1492 + difference 1 0) (sourceB1492 + difference 0 1) sourceC1492) = raw22775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22775; decide +kernel
    rw [ha]
    exact (canonical22775 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1492 + difference 1 2) (sourceB1492 + difference 2 1) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4578) := by
    have ha : (tripleCharges (sourceA1492 + difference 1 2) (sourceB1492 + difference 2 1) sourceC1492) = raw22776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22776; decide +kernel
    rw [ha]
    exact (canonical22776 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1492 + difference 1 3) (sourceB1492 + difference 3 1) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4565) := by
    have ha : (tripleCharges (sourceA1492 + difference 1 3) (sourceB1492 + difference 3 1) sourceC1492) = raw22777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22777; decide +kernel
    rw [ha]
    exact (canonical22777 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1492 + difference 1 4) (sourceB1492 + difference 4 1) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1492 + difference 1 4) (sourceB1492 + difference 4 1) sourceC1492) = raw22613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22613; decide +kernel
    rw [ha]
    exact (canonical22613 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1492 + difference 1 5) (sourceB1492 + difference 5 1) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1492 + difference 1 5) (sourceB1492 + difference 5 1) sourceC1492) = raw22778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22778; decide +kernel
    rw [ha]
    exact (canonical22778 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1492 + difference 2 0) (sourceB1492 + difference 0 2) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1492 + difference 2 0) (sourceB1492 + difference 0 2) sourceC1492) = raw22779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22779; decide +kernel
    rw [ha]
    exact (canonical22779 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1492 + difference 2 1) (sourceB1492 + difference 1 2) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4578) := by
    have ha : (tripleCharges (sourceA1492 + difference 2 1) (sourceB1492 + difference 1 2) sourceC1492) = raw22780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22780; decide +kernel
    rw [ha]
    exact (canonical22780 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1492 + difference 2 3) (sourceB1492 + difference 3 2) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4565) := by
    have ha : (tripleCharges (sourceA1492 + difference 2 3) (sourceB1492 + difference 3 2) sourceC1492) = raw22781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22781; decide +kernel
    rw [ha]
    exact (canonical22781 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1492 + difference 2 4) (sourceB1492 + difference 4 2) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1492 + difference 2 4) (sourceB1492 + difference 4 2) sourceC1492) = raw22617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22617; decide +kernel
    rw [ha]
    exact (canonical22617 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1492 + difference 2 5) (sourceB1492 + difference 5 2) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1492 + difference 2 5) (sourceB1492 + difference 5 2) sourceC1492) = raw22782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22782; decide +kernel
    rw [ha]
    exact (canonical22782 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1492 + difference 3 0) (sourceB1492 + difference 0 3) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1492 + difference 3 0) (sourceB1492 + difference 0 3) sourceC1492) = raw22623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22623; decide +kernel
    rw [ha]
    exact (canonical22623 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1492 + difference 3 1) (sourceB1492 + difference 1 3) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1492 + difference 3 1) (sourceB1492 + difference 1 3) sourceC1492) = raw22624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22624; decide +kernel
    rw [ha]
    exact (canonical22624 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1492 + difference 3 2) (sourceB1492 + difference 2 3) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1492 + difference 3 2) (sourceB1492 + difference 2 3) sourceC1492) = raw22625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22625; decide +kernel
    rw [ha]
    exact (canonical22625 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1492 + difference 3 4) (sourceB1492 + difference 4 3) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4628) := by
    have ha : (tripleCharges (sourceA1492 + difference 3 4) (sourceB1492 + difference 4 3) sourceC1492) = raw22530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22530; decide +kernel
    rw [ha]
    exact (canonical22530 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1492 + difference 3 5) (sourceB1492 + difference 5 3) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA1492 + difference 3 5) (sourceB1492 + difference 5 3) sourceC1492) = raw22627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22627; decide +kernel
    rw [ha]
    exact (canonical22627 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1492 + difference 4 0) (sourceB1492 + difference 0 4) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1492 + difference 4 0) (sourceB1492 + difference 0 4) sourceC1492) = raw22783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22783; decide +kernel
    rw [ha]
    exact (canonical22783 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1492 + difference 4 1) (sourceB1492 + difference 1 4) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4585) := by
    have ha : (tripleCharges (sourceA1492 + difference 4 1) (sourceB1492 + difference 1 4) sourceC1492) = raw22784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22784; decide +kernel
    rw [ha]
    exact (canonical22784 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1492 + difference 4 2) (sourceB1492 + difference 2 4) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4585) := by
    have ha : (tripleCharges (sourceA1492 + difference 4 2) (sourceB1492 + difference 2 4) sourceC1492) = raw22785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22785; decide +kernel
    rw [ha]
    exact (canonical22785 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1492 + difference 4 3) (sourceB1492 + difference 3 4) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4574) := by
    have ha : (tripleCharges (sourceA1492 + difference 4 3) (sourceB1492 + difference 3 4) sourceC1492) = raw22786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22786; decide +kernel
    rw [ha]
    exact (canonical22786 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1492 + difference 4 5) (sourceB1492 + difference 5 4) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1492 + difference 4 5) (sourceB1492 + difference 5 4) sourceC1492) = raw22787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22787; decide +kernel
    rw [ha]
    exact (canonical22787 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1492 + difference 5 0) (sourceB1492 + difference 0 5) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4432) := by
    have ha : (tripleCharges (sourceA1492 + difference 5 0) (sourceB1492 + difference 0 5) sourceC1492) = raw22788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22788; decide +kernel
    rw [ha]
    exact (canonical22788 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1492 + difference 5 1) (sourceB1492 + difference 1 5) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4586) := by
    have ha : (tripleCharges (sourceA1492 + difference 5 1) (sourceB1492 + difference 1 5) sourceC1492) = raw22789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22789; decide +kernel
    rw [ha]
    exact (canonical22789 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1492 + difference 5 2) (sourceB1492 + difference 2 5) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4586) := by
    have ha : (tripleCharges (sourceA1492 + difference 5 2) (sourceB1492 + difference 2 5) sourceC1492) = raw22790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22790; decide +kernel
    rw [ha]
    exact (canonical22790 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1492 + difference 5 3) (sourceB1492 + difference 3 5) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4575) := by
    have ha : (tripleCharges (sourceA1492 + difference 5 3) (sourceB1492 + difference 3 5) sourceC1492) = raw22791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22791; decide +kernel
    rw [ha]
    exact (canonical22791 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1492 + difference 5 4) (sourceB1492 + difference 4 5) sourceC1492) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1492 + difference 5 4) (sourceB1492 + difference 4 5) sourceC1492) = raw22529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1492 sourceB1492 sourceC1492 difference raw22529; decide +kernel
    rw [ha]
    exact (canonical22529 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1492 sourceB1492 sourceC1492
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1492, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1493 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceB1493 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC1493 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1493 : Integer.Sparse Master := [(Sum.inr 985, 2), (Sum.inr 1012, 1), (Sum.inr 1013, 1), (Sum.inr 1095, 1), (Sum.inr 1182, 2), (Sum.inr 1192, 1), (Sum.inr 1193, 1), (Sum.inr 1196, 2), (Sum.inr 1204, 2), (Sum.inr 1205, 2), (Sum.inr 1219, 2), (Sum.inr 1220, 2), (Sum.inr 1245, 1), (Sum.inr 1246, 3), (Sum.inr 1311, 1), (Sum.inr 1312, 1), (Sum.inr 1375, 1), (Sum.inr 1391, 2), (Sum.inr 1419, 1), (Sum.inr 1420, 1)]

theorem sourceEq1493 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1493 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1493 + difference 0 1) (sourceB1493 + difference 1 0) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA1493 + difference 0 1) (sourceB1493 + difference 1 0) sourceC1493) = raw22792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22792; decide +kernel
    rw [ha]
    exact (canonical22792 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1493 + difference 0 2) (sourceB1493 + difference 2 0) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA1493 + difference 0 2) (sourceB1493 + difference 2 0) sourceC1493) = raw22793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22793; decide +kernel
    rw [ha]
    exact (canonical22793 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1493 + difference 0 3) (sourceB1493 + difference 3 0) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1375) := by
    have ha : (tripleCharges (sourceA1493 + difference 0 3) (sourceB1493 + difference 3 0) sourceC1493) = raw22794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22794; decide +kernel
    rw [ha]
    exact (canonical22794 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1493 + difference 0 4) (sourceB1493 + difference 4 0) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1420) := by
    have ha : (tripleCharges (sourceA1493 + difference 0 4) (sourceB1493 + difference 4 0) sourceC1493) = raw22631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22631; decide +kernel
    rw [ha]
    exact (canonical22631 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1493 + difference 0 5) (sourceB1493 + difference 5 0) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1493 + difference 0 5) (sourceB1493 + difference 5 0) sourceC1493) = raw22795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22795; decide +kernel
    rw [ha]
    exact (canonical22795 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1493 + difference 1 0) (sourceB1493 + difference 0 1) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1493 + difference 1 0) (sourceB1493 + difference 0 1) sourceC1493) = raw22796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22796; decide +kernel
    rw [ha]
    exact (canonical22796 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1493 + difference 1 2) (sourceB1493 + difference 2 1) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1196) := by
    have ha : (tripleCharges (sourceA1493 + difference 1 2) (sourceB1493 + difference 2 1) sourceC1493) = raw22797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22797; decide +kernel
    rw [ha]
    exact (canonical22797 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1493 + difference 1 3) (sourceB1493 + difference 3 1) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1182) := by
    have ha : (tripleCharges (sourceA1493 + difference 1 3) (sourceB1493 + difference 3 1) sourceC1493) = raw22798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22798; decide +kernel
    rw [ha]
    exact (canonical22798 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1493 + difference 1 4) (sourceB1493 + difference 4 1) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1493 + difference 1 4) (sourceB1493 + difference 4 1) sourceC1493) = raw22635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22635; decide +kernel
    rw [ha]
    exact (canonical22635 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1493 + difference 1 5) (sourceB1493 + difference 5 1) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1493 + difference 1 5) (sourceB1493 + difference 5 1) sourceC1493) = raw22799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22799; decide +kernel
    rw [ha]
    exact (canonical22799 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1493 + difference 2 0) (sourceB1493 + difference 0 2) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1493 + difference 2 0) (sourceB1493 + difference 0 2) sourceC1493) = raw22800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22800; decide +kernel
    rw [ha]
    exact (canonical22800 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1493 + difference 2 1) (sourceB1493 + difference 1 2) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1196) := by
    have ha : (tripleCharges (sourceA1493 + difference 2 1) (sourceB1493 + difference 1 2) sourceC1493) = raw22801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22801; decide +kernel
    rw [ha]
    exact (canonical22801 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1493 + difference 2 3) (sourceB1493 + difference 3 2) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1182) := by
    have ha : (tripleCharges (sourceA1493 + difference 2 3) (sourceB1493 + difference 3 2) sourceC1493) = raw22802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22802; decide +kernel
    rw [ha]
    exact (canonical22802 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1493 + difference 2 4) (sourceB1493 + difference 4 2) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1493 + difference 2 4) (sourceB1493 + difference 4 2) sourceC1493) = raw22639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22639; decide +kernel
    rw [ha]
    exact (canonical22639 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1493 + difference 2 5) (sourceB1493 + difference 5 2) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1493 + difference 2 5) (sourceB1493 + difference 5 2) sourceC1493) = raw22803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22803; decide +kernel
    rw [ha]
    exact (canonical22803 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1493 + difference 3 0) (sourceB1493 + difference 0 3) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1095) := by
    have ha : (tripleCharges (sourceA1493 + difference 3 0) (sourceB1493 + difference 0 3) sourceC1493) = raw22645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22645; decide +kernel
    rw [ha]
    exact (canonical22645 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1493 + difference 3 1) (sourceB1493 + difference 1 3) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1493 + difference 3 1) (sourceB1493 + difference 1 3) sourceC1493) = raw22646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22646; decide +kernel
    rw [ha]
    exact (canonical22646 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1493 + difference 3 2) (sourceB1493 + difference 2 3) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1493 + difference 3 2) (sourceB1493 + difference 2 3) sourceC1493) = raw22647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22647; decide +kernel
    rw [ha]
    exact (canonical22647 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1493 + difference 3 4) (sourceB1493 + difference 4 3) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1312) := by
    have ha : (tripleCharges (sourceA1493 + difference 3 4) (sourceB1493 + difference 4 3) sourceC1493) = raw22560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22560; decide +kernel
    rw [ha]
    exact (canonical22560 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1493 + difference 3 5) (sourceB1493 + difference 5 3) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1311) := by
    have ha : (tripleCharges (sourceA1493 + difference 3 5) (sourceB1493 + difference 5 3) sourceC1493) = raw22649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22649; decide +kernel
    rw [ha]
    exact (canonical22649 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1493 + difference 4 0) (sourceB1493 + difference 0 4) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1012) := by
    have ha : (tripleCharges (sourceA1493 + difference 4 0) (sourceB1493 + difference 0 4) sourceC1493) = raw22804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22804; decide +kernel
    rw [ha]
    exact (canonical22804 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1493 + difference 4 1) (sourceB1493 + difference 1 4) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1204) := by
    have ha : (tripleCharges (sourceA1493 + difference 4 1) (sourceB1493 + difference 1 4) sourceC1493) = raw22805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22805; decide +kernel
    rw [ha]
    exact (canonical22805 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1493 + difference 4 2) (sourceB1493 + difference 2 4) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1204) := by
    have ha : (tripleCharges (sourceA1493 + difference 4 2) (sourceB1493 + difference 2 4) sourceC1493) = raw22806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22806; decide +kernel
    rw [ha]
    exact (canonical22806 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1493 + difference 4 3) (sourceB1493 + difference 3 4) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1192) := by
    have ha : (tripleCharges (sourceA1493 + difference 4 3) (sourceB1493 + difference 3 4) sourceC1493) = raw22807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22807; decide +kernel
    rw [ha]
    exact (canonical22807 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1493 + difference 4 5) (sourceB1493 + difference 5 4) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA1493 + difference 4 5) (sourceB1493 + difference 5 4) sourceC1493) = raw22808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22808; decide +kernel
    rw [ha]
    exact (canonical22808 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1493 + difference 5 0) (sourceB1493 + difference 0 5) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1013) := by
    have ha : (tripleCharges (sourceA1493 + difference 5 0) (sourceB1493 + difference 0 5) sourceC1493) = raw22809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22809; decide +kernel
    rw [ha]
    exact (canonical22809 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1493 + difference 5 1) (sourceB1493 + difference 1 5) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1205) := by
    have ha : (tripleCharges (sourceA1493 + difference 5 1) (sourceB1493 + difference 1 5) sourceC1493) = raw22810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22810; decide +kernel
    rw [ha]
    exact (canonical22810 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1493 + difference 5 2) (sourceB1493 + difference 2 5) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1205) := by
    have ha : (tripleCharges (sourceA1493 + difference 5 2) (sourceB1493 + difference 2 5) sourceC1493) = raw22811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22811; decide +kernel
    rw [ha]
    exact (canonical22811 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1493 + difference 5 3) (sourceB1493 + difference 3 5) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1193) := by
    have ha : (tripleCharges (sourceA1493 + difference 5 3) (sourceB1493 + difference 3 5) sourceC1493) = raw22812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22812; decide +kernel
    rw [ha]
    exact (canonical22812 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1493 + difference 5 4) (sourceB1493 + difference 4 5) sourceC1493) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1493 + difference 5 4) (sourceB1493 + difference 4 5) sourceC1493) = raw22559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1493 sourceB1493 sourceC1493 difference raw22559; decide +kernel
    rw [ha]
    exact (canonical22559 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1493 sourceB1493 sourceC1493
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1493, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1494 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceB1494 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC1494 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1494 : Integer.Sparse Master := [(Sum.inr 1026, 2), (Sum.inr 1049, 1), (Sum.inr 1050, 1), (Sum.inr 1063, 1), (Sum.inr 1208, 2), (Sum.inr 1219, 2), (Sum.inr 1220, 2), (Sum.inr 1226, 2), (Sum.inr 1253, 2), (Sum.inr 1254, 2), (Sum.inr 1273, 1), (Sum.inr 1274, 3), (Sum.inr 1283, 1), (Sum.inr 1284, 1), (Sum.inr 1311, 1), (Sum.inr 1312, 1), (Sum.inr 1401, 2), (Sum.inr 1430, 1), (Sum.inr 1431, 1), (Sum.inr 1455, 1)]

theorem sourceEq1494 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1494 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1494 + difference 0 1) (sourceB1494 + difference 1 0) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA1494 + difference 0 1) (sourceB1494 + difference 1 0) sourceC1494) = raw22813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22813; decide +kernel
    rw [ha]
    exact (canonical22813 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1494 + difference 0 2) (sourceB1494 + difference 2 0) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA1494 + difference 0 2) (sourceB1494 + difference 2 0) sourceC1494) = raw22814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22814; decide +kernel
    rw [ha]
    exact (canonical22814 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1494 + difference 0 3) (sourceB1494 + difference 3 0) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1063) := by
    have ha : (tripleCharges (sourceA1494 + difference 0 3) (sourceB1494 + difference 3 0) sourceC1494) = raw22815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22815; decide +kernel
    rw [ha]
    exact (canonical22815 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1494 + difference 0 4) (sourceB1494 + difference 4 0) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1494 + difference 0 4) (sourceB1494 + difference 4 0) sourceC1494) = raw22816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22816; decide +kernel
    rw [ha]
    exact (canonical22816 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1494 + difference 0 5) (sourceB1494 + difference 5 0) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1494 + difference 0 5) (sourceB1494 + difference 5 0) sourceC1494) = raw22817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22817; decide +kernel
    rw [ha]
    exact (canonical22817 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1494 + difference 1 0) (sourceB1494 + difference 0 1) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1401) := by
    have ha : (tripleCharges (sourceA1494 + difference 1 0) (sourceB1494 + difference 0 1) sourceC1494) = raw22818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22818; decide +kernel
    rw [ha]
    exact (canonical22818 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1494 + difference 1 2) (sourceB1494 + difference 2 1) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1208) := by
    have ha : (tripleCharges (sourceA1494 + difference 1 2) (sourceB1494 + difference 2 1) sourceC1494) = raw22819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22819; decide +kernel
    rw [ha]
    exact (canonical22819 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1494 + difference 1 3) (sourceB1494 + difference 3 1) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1226) := by
    have ha : (tripleCharges (sourceA1494 + difference 1 3) (sourceB1494 + difference 3 1) sourceC1494) = raw22820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22820; decide +kernel
    rw [ha]
    exact (canonical22820 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1494 + difference 1 4) (sourceB1494 + difference 4 1) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1494 + difference 1 4) (sourceB1494 + difference 4 1) sourceC1494) = raw22821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22821; decide +kernel
    rw [ha]
    exact (canonical22821 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1494 + difference 1 5) (sourceB1494 + difference 5 1) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1494 + difference 1 5) (sourceB1494 + difference 5 1) sourceC1494) = raw22822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22822; decide +kernel
    rw [ha]
    exact (canonical22822 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1494 + difference 2 0) (sourceB1494 + difference 0 2) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1401) := by
    have ha : (tripleCharges (sourceA1494 + difference 2 0) (sourceB1494 + difference 0 2) sourceC1494) = raw22823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22823; decide +kernel
    rw [ha]
    exact (canonical22823 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1494 + difference 2 1) (sourceB1494 + difference 1 2) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1208) := by
    have ha : (tripleCharges (sourceA1494 + difference 2 1) (sourceB1494 + difference 1 2) sourceC1494) = raw22824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22824; decide +kernel
    rw [ha]
    exact (canonical22824 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1494 + difference 2 3) (sourceB1494 + difference 3 2) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1226) := by
    have ha : (tripleCharges (sourceA1494 + difference 2 3) (sourceB1494 + difference 3 2) sourceC1494) = raw22825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22825; decide +kernel
    rw [ha]
    exact (canonical22825 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1494 + difference 2 4) (sourceB1494 + difference 4 2) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1494 + difference 2 4) (sourceB1494 + difference 4 2) sourceC1494) = raw22826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22826; decide +kernel
    rw [ha]
    exact (canonical22826 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1494 + difference 2 5) (sourceB1494 + difference 5 2) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1494 + difference 2 5) (sourceB1494 + difference 5 2) sourceC1494) = raw22827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22827; decide +kernel
    rw [ha]
    exact (canonical22827 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1494 + difference 3 0) (sourceB1494 + difference 0 3) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1455) := by
    have ha : (tripleCharges (sourceA1494 + difference 3 0) (sourceB1494 + difference 0 3) sourceC1494) = raw22828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22828; decide +kernel
    rw [ha]
    exact (canonical22828 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1494 + difference 3 1) (sourceB1494 + difference 1 3) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1494 + difference 3 1) (sourceB1494 + difference 1 3) sourceC1494) = raw22829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22829; decide +kernel
    rw [ha]
    exact (canonical22829 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1494 + difference 3 2) (sourceB1494 + difference 2 3) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1494 + difference 3 2) (sourceB1494 + difference 2 3) sourceC1494) = raw22830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22830; decide +kernel
    rw [ha]
    exact (canonical22830 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1494 + difference 3 4) (sourceB1494 + difference 4 3) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1312) := by
    have ha : (tripleCharges (sourceA1494 + difference 3 4) (sourceB1494 + difference 4 3) sourceC1494) = raw22831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22831; decide +kernel
    rw [ha]
    exact (canonical22831 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1494 + difference 3 5) (sourceB1494 + difference 5 3) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1311) := by
    have ha : (tripleCharges (sourceA1494 + difference 3 5) (sourceB1494 + difference 5 3) sourceC1494) = raw22832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22832; decide +kernel
    rw [ha]
    exact (canonical22832 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1494 + difference 4 0) (sourceB1494 + difference 0 4) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1430) := by
    have ha : (tripleCharges (sourceA1494 + difference 4 0) (sourceB1494 + difference 0 4) sourceC1494) = raw22833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22833; decide +kernel
    rw [ha]
    exact (canonical22833 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1494 + difference 4 1) (sourceB1494 + difference 1 4) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1253) := by
    have ha : (tripleCharges (sourceA1494 + difference 4 1) (sourceB1494 + difference 1 4) sourceC1494) = raw22834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22834; decide +kernel
    rw [ha]
    exact (canonical22834 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1494 + difference 4 2) (sourceB1494 + difference 2 4) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1253) := by
    have ha : (tripleCharges (sourceA1494 + difference 4 2) (sourceB1494 + difference 2 4) sourceC1494) = raw22835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22835; decide +kernel
    rw [ha]
    exact (canonical22835 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1494 + difference 4 3) (sourceB1494 + difference 3 4) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1283) := by
    have ha : (tripleCharges (sourceA1494 + difference 4 3) (sourceB1494 + difference 3 4) sourceC1494) = raw22836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22836; decide +kernel
    rw [ha]
    exact (canonical22836 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1494 + difference 4 5) (sourceB1494 + difference 5 4) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA1494 + difference 4 5) (sourceB1494 + difference 5 4) sourceC1494) = raw22837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22837; decide +kernel
    rw [ha]
    exact (canonical22837 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1494 + difference 5 0) (sourceB1494 + difference 0 5) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1431) := by
    have ha : (tripleCharges (sourceA1494 + difference 5 0) (sourceB1494 + difference 0 5) sourceC1494) = raw22838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22838; decide +kernel
    rw [ha]
    exact (canonical22838 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1494 + difference 5 1) (sourceB1494 + difference 1 5) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1254) := by
    have ha : (tripleCharges (sourceA1494 + difference 5 1) (sourceB1494 + difference 1 5) sourceC1494) = raw22839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22839; decide +kernel
    rw [ha]
    exact (canonical22839 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1494 + difference 5 2) (sourceB1494 + difference 2 5) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1254) := by
    have ha : (tripleCharges (sourceA1494 + difference 5 2) (sourceB1494 + difference 2 5) sourceC1494) = raw22840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22840; decide +kernel
    rw [ha]
    exact (canonical22840 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1494 + difference 5 3) (sourceB1494 + difference 3 5) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1284) := by
    have ha : (tripleCharges (sourceA1494 + difference 5 3) (sourceB1494 + difference 3 5) sourceC1494) = raw22841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22841; decide +kernel
    rw [ha]
    exact (canonical22841 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1494 + difference 5 4) (sourceB1494 + difference 4 5) sourceC1494) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1494 + difference 5 4) (sourceB1494 + difference 4 5) sourceC1494) = raw22842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1494 sourceB1494 sourceC1494 difference raw22842; decide +kernel
    rw [ha]
    exact (canonical22842 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1494 sourceB1494 sourceC1494
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1494, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1495 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1495 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC1495 : Charge := ![2, 0, 0, 2, -3, -1]
def sourceForm1495 : Integer.Sparse Master := [(Sum.inr 1192, 1), (Sum.inr 2410, 1), (Sum.inr 2538, 2), (Sum.inr 2685, 1), (Sum.inr 2687, 1), (Sum.inr 4082, -1)]

theorem sourceEq1495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1495 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1495 + difference 0 0) (sourceB1495 + difference 0 0) sourceC1495) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1192) := by
    have ha : (tripleCharges (sourceA1495 + difference 0 0) (sourceB1495 + difference 0 0) sourceC1495) = raw22843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1495 sourceB1495 sourceC1495 difference raw22843; decide +kernel
    rw [ha]
    exact (canonical22843 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1495 + difference 0 1) (sourceB1495 + difference 1 0) sourceC1495) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2538) := by
    have ha : (tripleCharges (sourceA1495 + difference 0 1) (sourceB1495 + difference 1 0) sourceC1495) = raw22844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1495 sourceB1495 sourceC1495 difference raw22844; decide +kernel
    rw [ha]
    exact (canonical22844 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1495 + difference 0 2) (sourceB1495 + difference 2 0) sourceC1495) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2538) := by
    have ha : (tripleCharges (sourceA1495 + difference 0 2) (sourceB1495 + difference 2 0) sourceC1495) = raw22845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1495 sourceB1495 sourceC1495 difference raw22845; decide +kernel
    rw [ha]
    exact (canonical22845 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1495 + difference 0 3) (sourceB1495 + difference 3 0) sourceC1495) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2410) := by
    have ha : (tripleCharges (sourceA1495 + difference 0 3) (sourceB1495 + difference 3 0) sourceC1495) = raw22846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1495 sourceB1495 sourceC1495 difference raw22846; decide +kernel
    rw [ha]
    exact (canonical22846 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1495 + difference 0 4) (sourceB1495 + difference 4 0) sourceC1495) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA1495 + difference 0 4) (sourceB1495 + difference 4 0) sourceC1495) = raw22847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1495 sourceB1495 sourceC1495 difference raw22847; decide +kernel
    rw [ha]
    exact (canonical22847 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1495 + difference 0 5) (sourceB1495 + difference 5 0) sourceC1495) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA1495 + difference 0 5) (sourceB1495 + difference 5 0) sourceC1495) = raw22848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1495 sourceB1495 sourceC1495 difference raw22848; decide +kernel
    rw [ha]
    exact (canonical22848 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1495 + sourceB1495) sourceC1495) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1495 + sourceB1495) sourceC1495) = raw22849 := by
      apply Matrix.ext; unfold doubleCharges sourceA1495 sourceB1495 sourceC1495 raw22849; decide +kernel
    rw [ha]
    exact (canonical22849 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1495 sourceB1495 sourceC1495
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1495, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1496 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1496 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1496 : Charge := ![2, 0, 0, 2, -2, -2]
def sourceForm1496 : Integer.Sparse Master := [(Sum.inr 1193, 1), (Sum.inr 2411, 1), (Sum.inr 2539, 2), (Sum.inr 2686, 2), (Sum.inr 4089, -1)]

theorem sourceEq1496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1496 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1496 + difference 0 0) (sourceB1496 + difference 0 0) sourceC1496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1193) := by
    have ha : (tripleCharges (sourceA1496 + difference 0 0) (sourceB1496 + difference 0 0) sourceC1496) = raw21012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1496 sourceB1496 sourceC1496 difference raw21012; decide +kernel
    rw [ha]
    exact (canonical21012 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1496 + difference 0 1) (sourceB1496 + difference 1 0) sourceC1496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2539) := by
    have ha : (tripleCharges (sourceA1496 + difference 0 1) (sourceB1496 + difference 1 0) sourceC1496) = raw22850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1496 sourceB1496 sourceC1496 difference raw22850; decide +kernel
    rw [ha]
    exact (canonical22850 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1496 + difference 0 2) (sourceB1496 + difference 2 0) sourceC1496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2539) := by
    have ha : (tripleCharges (sourceA1496 + difference 0 2) (sourceB1496 + difference 2 0) sourceC1496) = raw22851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1496 sourceB1496 sourceC1496 difference raw22851; decide +kernel
    rw [ha]
    exact (canonical22851 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1496 + difference 0 3) (sourceB1496 + difference 3 0) sourceC1496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2411) := by
    have ha : (tripleCharges (sourceA1496 + difference 0 3) (sourceB1496 + difference 3 0) sourceC1496) = raw22852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1496 sourceB1496 sourceC1496 difference raw22852; decide +kernel
    rw [ha]
    exact (canonical22852 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1496 + difference 0 4) (sourceB1496 + difference 4 0) sourceC1496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA1496 + difference 0 4) (sourceB1496 + difference 4 0) sourceC1496) = raw21007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1496 sourceB1496 sourceC1496 difference raw21007; decide +kernel
    rw [ha]
    exact (canonical21007 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1496 + difference 0 5) (sourceB1496 + difference 5 0) sourceC1496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA1496 + difference 0 5) (sourceB1496 + difference 5 0) sourceC1496) = raw22853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1496 sourceB1496 sourceC1496 difference raw22853; decide +kernel
    rw [ha]
    exact (canonical22853 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1496 + sourceB1496) sourceC1496) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA1496 + sourceB1496) sourceC1496) = raw21008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1496 sourceB1496 sourceC1496 raw21008; decide +kernel
    rw [ha]
    exact (canonical21008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1496 sourceB1496 sourceC1496
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1496, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1497 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1497 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1497 : Charge := ![2, 0, 0, 2, -2, -2]
def sourceForm1497 : Integer.Sparse Master := [(Sum.inr 1099, 2), (Sum.inr 1104, 2), (Sum.inr 1193, 1), (Sum.inr 2411, 1), (Sum.inr 4089, -1)]

theorem sourceEq1497 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1497 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1497 + difference 0 3) (sourceB1497 + difference 3 0) sourceC1497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2411) := by
    have ha : (tripleCharges (sourceA1497 + difference 0 3) (sourceB1497 + difference 3 0) sourceC1497) = raw22852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1497 sourceB1497 sourceC1497 difference raw22852; decide +kernel
    rw [ha]
    exact (canonical22852 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1497 + difference 1 3) (sourceB1497 + difference 3 1) sourceC1497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1099) := by
    have ha : (tripleCharges (sourceA1497 + difference 1 3) (sourceB1497 + difference 3 1) sourceC1497) = raw22854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1497 sourceB1497 sourceC1497 difference raw22854; decide +kernel
    rw [ha]
    exact (canonical22854 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1497 + difference 2 3) (sourceB1497 + difference 3 2) sourceC1497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1099) := by
    have ha : (tripleCharges (sourceA1497 + difference 2 3) (sourceB1497 + difference 3 2) sourceC1497) = raw22855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1497 sourceB1497 sourceC1497 difference raw22855; decide +kernel
    rw [ha]
    exact (canonical22855 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1497 + difference 3 3) (sourceB1497 + difference 3 3) sourceC1497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1193) := by
    have ha : (tripleCharges (sourceA1497 + difference 3 3) (sourceB1497 + difference 3 3) sourceC1497) = raw21012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1497 sourceB1497 sourceC1497 difference raw21012; decide +kernel
    rw [ha]
    exact (canonical21012 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1497 + difference 4 3) (sourceB1497 + difference 3 4) sourceC1497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1104) := by
    have ha : (tripleCharges (sourceA1497 + difference 4 3) (sourceB1497 + difference 3 4) sourceC1497) = raw22856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1497 sourceB1497 sourceC1497 difference raw22856; decide +kernel
    rw [ha]
    exact (canonical22856 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1497 + difference 5 3) (sourceB1497 + difference 3 5) sourceC1497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1104) := by
    have ha : (tripleCharges (sourceA1497 + difference 5 3) (sourceB1497 + difference 3 5) sourceC1497) = raw22857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1497 sourceB1497 sourceC1497 difference raw22857; decide +kernel
    rw [ha]
    exact (canonical22857 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1497 + sourceB1497) sourceC1497) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA1497 + sourceB1497) sourceC1497) = raw21008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1497 sourceB1497 sourceC1497 raw21008; decide +kernel
    rw [ha]
    exact (canonical21008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1497 sourceB1497 sourceC1497
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1497, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1498 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceB1498 : Charge := ![2, 0, 0, 2, -2, -2]
def sourceC1498 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1498 : Integer.Sparse Master := [(Sum.inr 1544, 2), (Sum.inr 1549, 2), (Sum.inr 1631, 1), (Sum.inr 3248, 1), (Sum.inr 4071, -1)]

theorem sourceEq1498 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1498 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1498 + difference 0 0) (sourceB1498 + difference 0 0) sourceC1498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3248) := by
    have ha : (tripleCharges (sourceA1498 + difference 0 0) (sourceB1498 + difference 0 0) sourceC1498) = raw22858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1498 sourceB1498 sourceC1498 difference raw22858; decide +kernel
    rw [ha]
    exact (canonical22858 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1498 + difference 1 0) (sourceB1498 + difference 0 1) sourceC1498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1544) := by
    have ha : (tripleCharges (sourceA1498 + difference 1 0) (sourceB1498 + difference 0 1) sourceC1498) = raw22859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1498 sourceB1498 sourceC1498 difference raw22859; decide +kernel
    rw [ha]
    exact (canonical22859 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1498 + difference 2 0) (sourceB1498 + difference 0 2) sourceC1498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1544) := by
    have ha : (tripleCharges (sourceA1498 + difference 2 0) (sourceB1498 + difference 0 2) sourceC1498) = raw22860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1498 sourceB1498 sourceC1498 difference raw22860; decide +kernel
    rw [ha]
    exact (canonical22860 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1498 + difference 3 0) (sourceB1498 + difference 0 3) sourceC1498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1631) := by
    have ha : (tripleCharges (sourceA1498 + difference 3 0) (sourceB1498 + difference 0 3) sourceC1498) = raw22861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1498 sourceB1498 sourceC1498 difference raw22861; decide +kernel
    rw [ha]
    exact (canonical22861 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1498 + difference 4 0) (sourceB1498 + difference 0 4) sourceC1498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1549) := by
    have ha : (tripleCharges (sourceA1498 + difference 4 0) (sourceB1498 + difference 0 4) sourceC1498) = raw22862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1498 sourceB1498 sourceC1498 difference raw22862; decide +kernel
    rw [ha]
    exact (canonical22862 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1498 + difference 5 0) (sourceB1498 + difference 0 5) sourceC1498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1549) := by
    have ha : (tripleCharges (sourceA1498 + difference 5 0) (sourceB1498 + difference 0 5) sourceC1498) = raw22863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1498 sourceB1498 sourceC1498 difference raw22863; decide +kernel
    rw [ha]
    exact (canonical22863 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1498 + sourceB1498) sourceC1498) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1498 + sourceB1498) sourceC1498) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1498 sourceB1498 sourceC1498 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1498 sourceB1498 sourceC1498
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1498, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1499 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1499 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC1499 : Charge := ![2, 0, 1, 1, -3, -1]
def sourceForm1499 : Integer.Sparse Master := [(Sum.inr 1204, 1), (Sum.inr 2467, 2), (Sum.inr 2540, 1), (Sum.inr 2704, 1), (Sum.inr 2706, 1), (Sum.inr 4080, -1)]

theorem sourceEq1499 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1499 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1499 + difference 0 0) (sourceB1499 + difference 0 0) sourceC1499) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1204) := by
    have ha : (tripleCharges (sourceA1499 + difference 0 0) (sourceB1499 + difference 0 0) sourceC1499) = raw22864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1499 sourceB1499 sourceC1499 difference raw22864; decide +kernel
    rw [ha]
    exact (canonical22864 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1499 + difference 0 1) (sourceB1499 + difference 1 0) sourceC1499) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2540) := by
    have ha : (tripleCharges (sourceA1499 + difference 0 1) (sourceB1499 + difference 1 0) sourceC1499) = raw22865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1499 sourceB1499 sourceC1499 difference raw22865; decide +kernel
    rw [ha]
    exact (canonical22865 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1499 + difference 0 2) (sourceB1499 + difference 2 0) sourceC1499) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2467) := by
    have ha : (tripleCharges (sourceA1499 + difference 0 2) (sourceB1499 + difference 2 0) sourceC1499) = raw22866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1499 sourceB1499 sourceC1499 difference raw22866; decide +kernel
    rw [ha]
    exact (canonical22866 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1499 + difference 0 3) (sourceB1499 + difference 3 0) sourceC1499) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2467) := by
    have ha : (tripleCharges (sourceA1499 + difference 0 3) (sourceB1499 + difference 3 0) sourceC1499) = raw22867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1499 sourceB1499 sourceC1499 difference raw22867; decide +kernel
    rw [ha]
    exact (canonical22867 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1499 + difference 0 4) (sourceB1499 + difference 4 0) sourceC1499) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA1499 + difference 0 4) (sourceB1499 + difference 4 0) sourceC1499) = raw22868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1499 sourceB1499 sourceC1499 difference raw22868; decide +kernel
    rw [ha]
    exact (canonical22868 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1499 + difference 0 5) (sourceB1499 + difference 5 0) sourceC1499) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA1499 + difference 0 5) (sourceB1499 + difference 5 0) sourceC1499) = raw22869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1499 sourceB1499 sourceC1499 difference raw22869; decide +kernel
    rw [ha]
    exact (canonical22869 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1499 + sourceB1499) sourceC1499) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1499 + sourceB1499) sourceC1499) = raw22870 := by
      apply Matrix.ext; unfold doubleCharges sourceA1499 sourceB1499 sourceC1499 raw22870; decide +kernel
    rw [ha]
    exact (canonical22870 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1499 sourceB1499 sourceC1499
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1499, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1500 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1500 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1500 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceForm1500 : Integer.Sparse Master := [(Sum.inr 1205, 1), (Sum.inr 2468, 2), (Sum.inr 2541, 1), (Sum.inr 2705, 2), (Sum.inr 4088, -1)]

theorem sourceEq1500 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1500 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1500 + difference 0 0) (sourceB1500 + difference 0 0) sourceC1500) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1205) := by
    have ha : (tripleCharges (sourceA1500 + difference 0 0) (sourceB1500 + difference 0 0) sourceC1500) = raw21050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1500 sourceB1500 sourceC1500 difference raw21050; decide +kernel
    rw [ha]
    exact (canonical21050 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1500 + difference 0 1) (sourceB1500 + difference 1 0) sourceC1500) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2541) := by
    have ha : (tripleCharges (sourceA1500 + difference 0 1) (sourceB1500 + difference 1 0) sourceC1500) = raw22871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1500 sourceB1500 sourceC1500 difference raw22871; decide +kernel
    rw [ha]
    exact (canonical22871 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1500 + difference 0 2) (sourceB1500 + difference 2 0) sourceC1500) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2468) := by
    have ha : (tripleCharges (sourceA1500 + difference 0 2) (sourceB1500 + difference 2 0) sourceC1500) = raw22872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1500 sourceB1500 sourceC1500 difference raw22872; decide +kernel
    rw [ha]
    exact (canonical22872 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1500 + difference 0 3) (sourceB1500 + difference 3 0) sourceC1500) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2468) := by
    have ha : (tripleCharges (sourceA1500 + difference 0 3) (sourceB1500 + difference 3 0) sourceC1500) = raw22873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1500 sourceB1500 sourceC1500 difference raw22873; decide +kernel
    rw [ha]
    exact (canonical22873 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1500 + difference 0 4) (sourceB1500 + difference 4 0) sourceC1500) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA1500 + difference 0 4) (sourceB1500 + difference 4 0) sourceC1500) = raw21045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1500 sourceB1500 sourceC1500 difference raw21045; decide +kernel
    rw [ha]
    exact (canonical21045 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1500 + difference 0 5) (sourceB1500 + difference 5 0) sourceC1500) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA1500 + difference 0 5) (sourceB1500 + difference 5 0) sourceC1500) = raw22874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1500 sourceB1500 sourceC1500 difference raw22874; decide +kernel
    rw [ha]
    exact (canonical22874 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1500 + sourceB1500) sourceC1500) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1500 + sourceB1500) sourceC1500) = raw21046 := by
      apply Matrix.ext; unfold doubleCharges sourceA1500 sourceB1500 sourceC1500 raw21046; decide +kernel
    rw [ha]
    exact (canonical21046 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1500 sourceB1500 sourceC1500
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1500, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1501 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1501 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1501 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceForm1501 : Integer.Sparse Master := [(Sum.inr 1106, 1), (Sum.inr 1110, 2), (Sum.inr 1124, 1), (Sum.inr 1205, 1), (Sum.inr 2468, 1), (Sum.inr 4088, -1)]

theorem sourceEq1501 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1501 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1501 + difference 0 2) (sourceB1501 + difference 2 0) sourceC1501) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2468) := by
    have ha : (tripleCharges (sourceA1501 + difference 0 2) (sourceB1501 + difference 2 0) sourceC1501) = raw22872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1501 sourceB1501 sourceC1501 difference raw22872; decide +kernel
    rw [ha]
    exact (canonical22872 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1501 + difference 1 2) (sourceB1501 + difference 2 1) sourceC1501) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1106) := by
    have ha : (tripleCharges (sourceA1501 + difference 1 2) (sourceB1501 + difference 2 1) sourceC1501) = raw22875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1501 sourceB1501 sourceC1501 difference raw22875; decide +kernel
    rw [ha]
    exact (canonical22875 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1501 + difference 2 2) (sourceB1501 + difference 2 2) sourceC1501) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1205) := by
    have ha : (tripleCharges (sourceA1501 + difference 2 2) (sourceB1501 + difference 2 2) sourceC1501) = raw21050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1501 sourceB1501 sourceC1501 difference raw21050; decide +kernel
    rw [ha]
    exact (canonical21050 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1501 + difference 3 2) (sourceB1501 + difference 2 3) sourceC1501) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1124) := by
    have ha : (tripleCharges (sourceA1501 + difference 3 2) (sourceB1501 + difference 2 3) sourceC1501) = raw22876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1501 sourceB1501 sourceC1501 difference raw22876; decide +kernel
    rw [ha]
    exact (canonical22876 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1501 + difference 4 2) (sourceB1501 + difference 2 4) sourceC1501) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1110) := by
    have ha : (tripleCharges (sourceA1501 + difference 4 2) (sourceB1501 + difference 2 4) sourceC1501) = raw22877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1501 sourceB1501 sourceC1501 difference raw22877; decide +kernel
    rw [ha]
    exact (canonical22877 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1501 + difference 5 2) (sourceB1501 + difference 2 5) sourceC1501) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1110) := by
    have ha : (tripleCharges (sourceA1501 + difference 5 2) (sourceB1501 + difference 2 5) sourceC1501) = raw22878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1501 sourceB1501 sourceC1501 difference raw22878; decide +kernel
    rw [ha]
    exact (canonical22878 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1501 + sourceB1501) sourceC1501) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1501 + sourceB1501) sourceC1501) = raw21046 := by
      apply Matrix.ext; unfold doubleCharges sourceA1501 sourceB1501 sourceC1501 raw21046; decide +kernel
    rw [ha]
    exact (canonical21046 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1501 sourceB1501 sourceC1501
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1501, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1502 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceB1502 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceC1502 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1502 : Integer.Sparse Master := [(Sum.inr 1581, 1), (Sum.inr 1585, 2), (Sum.inr 1631, 2), (Sum.inr 3284, 1), (Sum.inr 4071, -1)]

theorem sourceEq1502 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1502 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1502 + difference 0 0) (sourceB1502 + difference 0 0) sourceC1502) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3284) := by
    have ha : (tripleCharges (sourceA1502 + difference 0 0) (sourceB1502 + difference 0 0) sourceC1502) = raw22879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1502 sourceB1502 sourceC1502 difference raw22879; decide +kernel
    rw [ha]
    exact (canonical22879 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1502 + difference 1 0) (sourceB1502 + difference 0 1) sourceC1502) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1581) := by
    have ha : (tripleCharges (sourceA1502 + difference 1 0) (sourceB1502 + difference 0 1) sourceC1502) = raw22880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1502 sourceB1502 sourceC1502 difference raw22880; decide +kernel
    rw [ha]
    exact (canonical22880 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1502 + difference 2 0) (sourceB1502 + difference 0 2) sourceC1502) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1631) := by
    have ha : (tripleCharges (sourceA1502 + difference 2 0) (sourceB1502 + difference 0 2) sourceC1502) = raw22861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1502 sourceB1502 sourceC1502 difference raw22861; decide +kernel
    rw [ha]
    exact (canonical22861 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1502 + difference 3 0) (sourceB1502 + difference 0 3) sourceC1502) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1631) := by
    have ha : (tripleCharges (sourceA1502 + difference 3 0) (sourceB1502 + difference 0 3) sourceC1502) = raw22881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1502 sourceB1502 sourceC1502 difference raw22881; decide +kernel
    rw [ha]
    exact (canonical22881 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1502 + difference 4 0) (sourceB1502 + difference 0 4) sourceC1502) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1585) := by
    have ha : (tripleCharges (sourceA1502 + difference 4 0) (sourceB1502 + difference 0 4) sourceC1502) = raw22882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1502 sourceB1502 sourceC1502 difference raw22882; decide +kernel
    rw [ha]
    exact (canonical22882 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1502 + difference 5 0) (sourceB1502 + difference 0 5) sourceC1502) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1585) := by
    have ha : (tripleCharges (sourceA1502 + difference 5 0) (sourceB1502 + difference 0 5) sourceC1502) = raw22883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1502 sourceB1502 sourceC1502 difference raw22883; decide +kernel
    rw [ha]
    exact (canonical22883 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1502 + sourceB1502) sourceC1502) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1502 + sourceB1502) sourceC1502) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1502 sourceB1502 sourceC1502 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1502 sourceB1502 sourceC1502
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1502, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1503 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1503 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceC1503 : Charge := ![3, -2, 0, 0, -2, 1]
def sourceForm1503 : Integer.Sparse Master := [(Sum.inr 1062, 1), (Sum.inr 2038, 2), (Sum.inr 2137, 1), (Sum.inr 2276, 1), (Sum.inr 2280, 1), (Sum.inr 4082, -1)]

theorem sourceEq1503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1503 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1503 + difference 0 0) (sourceB1503 + difference 0 0) sourceC1503) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1062) := by
    have ha : (tripleCharges (sourceA1503 + difference 0 0) (sourceB1503 + difference 0 0) sourceC1503) = raw22884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1503 sourceB1503 sourceC1503 difference raw22884; decide +kernel
    rw [ha]
    exact (canonical22884 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1503 + difference 0 1) (sourceB1503 + difference 1 0) sourceC1503) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2137) := by
    have ha : (tripleCharges (sourceA1503 + difference 0 1) (sourceB1503 + difference 1 0) sourceC1503) = raw22885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1503 sourceB1503 sourceC1503 difference raw22885; decide +kernel
    rw [ha]
    exact (canonical22885 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1503 + difference 0 2) (sourceB1503 + difference 2 0) sourceC1503) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2038) := by
    have ha : (tripleCharges (sourceA1503 + difference 0 2) (sourceB1503 + difference 2 0) sourceC1503) = raw22886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1503 sourceB1503 sourceC1503 difference raw22886; decide +kernel
    rw [ha]
    exact (canonical22886 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1503 + difference 0 3) (sourceB1503 + difference 3 0) sourceC1503) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2038) := by
    have ha : (tripleCharges (sourceA1503 + difference 0 3) (sourceB1503 + difference 3 0) sourceC1503) = raw22887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1503 sourceB1503 sourceC1503 difference raw22887; decide +kernel
    rw [ha]
    exact (canonical22887 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1503 + difference 0 4) (sourceB1503 + difference 4 0) sourceC1503) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA1503 + difference 0 4) (sourceB1503 + difference 4 0) sourceC1503) = raw22888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1503 sourceB1503 sourceC1503 difference raw22888; decide +kernel
    rw [ha]
    exact (canonical22888 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1503 + difference 0 5) (sourceB1503 + difference 5 0) sourceC1503) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA1503 + difference 0 5) (sourceB1503 + difference 5 0) sourceC1503) = raw22889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1503 sourceB1503 sourceC1503 difference raw22889; decide +kernel
    rw [ha]
    exact (canonical22889 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1503 + sourceB1503) sourceC1503) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1503 + sourceB1503) sourceC1503) = raw22890 := by
      apply Matrix.ext; unfold doubleCharges sourceA1503 sourceB1503 sourceC1503 raw22890; decide +kernel
    rw [ha]
    exact (canonical22890 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1503 sourceB1503 sourceC1503
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1503, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
