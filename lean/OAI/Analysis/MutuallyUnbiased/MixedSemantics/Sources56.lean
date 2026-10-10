import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical112
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical172
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical174
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical186
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical188
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical192
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical193
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical194
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical199
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical200
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical203
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical204
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical205
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical206

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1792 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceB1792 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC1792 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1792 : Integer.Sparse Master := [(Sum.inr 1252, 2), (Sum.inr 1255, 1), (Sum.inr 1270, 2), (Sum.inr 1272, 2), (Sum.inr 1305, 1), (Sum.inr 1306, 2), (Sum.inr 1398, 2), (Sum.inr 1414, 2), (Sum.inr 1415, 4), (Sum.inr 1427, 4), (Sum.inr 1448, 2), (Sum.inr 1449, 2), (Sum.inr 1478, 2), (Sum.inr 1484, 2)]

theorem sourceEq1792 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1792 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1792 + difference 0 1) (sourceB1792 + difference 1 0) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA1792 + difference 0 1) (sourceB1792 + difference 1 0) sourceC1792) = raw24208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw24208; decide +kernel
    rw [ha]
    exact (canonical24208 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1792 + difference 0 2) (sourceB1792 + difference 2 0) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA1792 + difference 0 2) (sourceB1792 + difference 2 0) sourceC1792) = raw24209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw24209; decide +kernel
    rw [ha]
    exact (canonical24209 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1792 + difference 0 3) (sourceB1792 + difference 3 0) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA1792 + difference 0 3) (sourceB1792 + difference 3 0) sourceC1792) = raw24210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw24210; decide +kernel
    rw [ha]
    exact (canonical24210 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1792 + difference 0 4) (sourceB1792 + difference 4 0) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA1792 + difference 0 4) (sourceB1792 + difference 4 0) sourceC1792) = raw24211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw24211; decide +kernel
    rw [ha]
    exact (canonical24211 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1792 + difference 0 5) (sourceB1792 + difference 5 0) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1792 + difference 0 5) (sourceB1792 + difference 5 0) sourceC1792) = raw25485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw25485; decide +kernel
    rw [ha]
    exact (canonical25485 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1792 + difference 1 0) (sourceB1792 + difference 0 1) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1478) := by
    have ha : (tripleCharges (sourceA1792 + difference 1 0) (sourceB1792 + difference 0 1) sourceC1792) = raw25497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw25497; decide +kernel
    rw [ha]
    exact (canonical25497 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1792 + difference 1 2) (sourceB1792 + difference 2 1) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1398) := by
    have ha : (tripleCharges (sourceA1792 + difference 1 2) (sourceB1792 + difference 2 1) sourceC1792) = raw25498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw25498; decide +kernel
    rw [ha]
    exact (canonical25498 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1792 + difference 1 3) (sourceB1792 + difference 3 1) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1415) := by
    have ha : (tripleCharges (sourceA1792 + difference 1 3) (sourceB1792 + difference 3 1) sourceC1792) = raw25499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw25499; decide +kernel
    rw [ha]
    exact (canonical25499 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1792 + difference 1 4) (sourceB1792 + difference 4 1) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1415) := by
    have ha : (tripleCharges (sourceA1792 + difference 1 4) (sourceB1792 + difference 4 1) sourceC1792) = raw25500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw25500; decide +kernel
    rw [ha]
    exact (canonical25500 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1792 + difference 1 5) (sourceB1792 + difference 5 1) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA1792 + difference 1 5) (sourceB1792 + difference 5 1) sourceC1792) = raw24187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw24187; decide +kernel
    rw [ha]
    exact (canonical24187 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1792 + difference 2 0) (sourceB1792 + difference 0 2) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1478) := by
    have ha : (tripleCharges (sourceA1792 + difference 2 0) (sourceB1792 + difference 0 2) sourceC1792) = raw26057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26057; decide +kernel
    rw [ha]
    exact (canonical26057 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1792 + difference 2 1) (sourceB1792 + difference 1 2) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1398) := by
    have ha : (tripleCharges (sourceA1792 + difference 2 1) (sourceB1792 + difference 1 2) sourceC1792) = raw26058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26058; decide +kernel
    rw [ha]
    exact (canonical26058 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1792 + difference 2 3) (sourceB1792 + difference 3 2) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1415) := by
    have ha : (tripleCharges (sourceA1792 + difference 2 3) (sourceB1792 + difference 3 2) sourceC1792) = raw26059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26059; decide +kernel
    rw [ha]
    exact (canonical26059 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1792 + difference 2 4) (sourceB1792 + difference 4 2) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1415) := by
    have ha : (tripleCharges (sourceA1792 + difference 2 4) (sourceB1792 + difference 4 2) sourceC1792) = raw26060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26060; decide +kernel
    rw [ha]
    exact (canonical26060 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1792 + difference 2 5) (sourceB1792 + difference 5 2) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA1792 + difference 2 5) (sourceB1792 + difference 5 2) sourceC1792) = raw24192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw24192; decide +kernel
    rw [ha]
    exact (canonical24192 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1792 + difference 3 0) (sourceB1792 + difference 0 3) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1484) := by
    have ha : (tripleCharges (sourceA1792 + difference 3 0) (sourceB1792 + difference 0 3) sourceC1792) = raw26061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26061; decide +kernel
    rw [ha]
    exact (canonical26061 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1792 + difference 3 1) (sourceB1792 + difference 1 3) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1427) := by
    have ha : (tripleCharges (sourceA1792 + difference 3 1) (sourceB1792 + difference 1 3) sourceC1792) = raw26062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26062; decide +kernel
    rw [ha]
    exact (canonical26062 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1792 + difference 3 2) (sourceB1792 + difference 2 3) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1427) := by
    have ha : (tripleCharges (sourceA1792 + difference 3 2) (sourceB1792 + difference 2 3) sourceC1792) = raw26063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26063; decide +kernel
    rw [ha]
    exact (canonical26063 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1792 + difference 3 4) (sourceB1792 + difference 4 3) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1449) := by
    have ha : (tripleCharges (sourceA1792 + difference 3 4) (sourceB1792 + difference 4 3) sourceC1792) = raw26064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26064; decide +kernel
    rw [ha]
    exact (canonical26064 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1792 + difference 3 5) (sourceB1792 + difference 5 3) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1448) := by
    have ha : (tripleCharges (sourceA1792 + difference 3 5) (sourceB1792 + difference 5 3) sourceC1792) = raw24197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw24197; decide +kernel
    rw [ha]
    exact (canonical24197 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1792 + difference 4 0) (sourceB1792 + difference 0 4) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1484) := by
    have ha : (tripleCharges (sourceA1792 + difference 4 0) (sourceB1792 + difference 0 4) sourceC1792) = raw26065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26065; decide +kernel
    rw [ha]
    exact (canonical26065 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1792 + difference 4 1) (sourceB1792 + difference 1 4) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1427) := by
    have ha : (tripleCharges (sourceA1792 + difference 4 1) (sourceB1792 + difference 1 4) sourceC1792) = raw26066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26066; decide +kernel
    rw [ha]
    exact (canonical26066 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1792 + difference 4 2) (sourceB1792 + difference 2 4) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1427) := by
    have ha : (tripleCharges (sourceA1792 + difference 4 2) (sourceB1792 + difference 2 4) sourceC1792) = raw26067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26067; decide +kernel
    rw [ha]
    exact (canonical26067 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1792 + difference 4 3) (sourceB1792 + difference 3 4) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1449) := by
    have ha : (tripleCharges (sourceA1792 + difference 4 3) (sourceB1792 + difference 3 4) sourceC1792) = raw26068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26068; decide +kernel
    rw [ha]
    exact (canonical26068 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1792 + difference 4 5) (sourceB1792 + difference 5 4) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1448) := by
    have ha : (tripleCharges (sourceA1792 + difference 4 5) (sourceB1792 + difference 5 4) sourceC1792) = raw24202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw24202; decide +kernel
    rw [ha]
    exact (canonical24202 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1792 + difference 5 0) (sourceB1792 + difference 0 5) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1255) := by
    have ha : (tripleCharges (sourceA1792 + difference 5 0) (sourceB1792 + difference 0 5) sourceC1792) = raw26069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26069; decide +kernel
    rw [ha]
    exact (canonical26069 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1792 + difference 5 1) (sourceB1792 + difference 1 5) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1252) := by
    have ha : (tripleCharges (sourceA1792 + difference 5 1) (sourceB1792 + difference 1 5) sourceC1792) = raw26070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26070; decide +kernel
    rw [ha]
    exact (canonical26070 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1792 + difference 5 2) (sourceB1792 + difference 2 5) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1252) := by
    have ha : (tripleCharges (sourceA1792 + difference 5 2) (sourceB1792 + difference 2 5) sourceC1792) = raw26071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26071; decide +kernel
    rw [ha]
    exact (canonical26071 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1792 + difference 5 3) (sourceB1792 + difference 3 5) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1272) := by
    have ha : (tripleCharges (sourceA1792 + difference 5 3) (sourceB1792 + difference 3 5) sourceC1792) = raw26072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26072; decide +kernel
    rw [ha]
    exact (canonical26072 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1792 + difference 5 4) (sourceB1792 + difference 4 5) sourceC1792) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1272) := by
    have ha : (tripleCharges (sourceA1792 + difference 5 4) (sourceB1792 + difference 4 5) sourceC1792) = raw26073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1792 sourceB1792 sourceC1792 difference raw26073; decide +kernel
    rw [ha]
    exact (canonical26073 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1792 sourceB1792 sourceC1792
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1792, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1793 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1793 : Charge := ![1, 0, -1, 2, 0, -2]
def sourceC1793 : Charge := ![3, 0, 1, -3, -1, 0]
def sourceForm1793 : Integer.Sparse Master := [(Sum.inr 1006, 1), (Sum.inr 1948, 1), (Sum.inr 2001, 1), (Sum.inr 2207, 1), (Sum.inr 2221, 1), (Sum.inr 2224, 1), (Sum.inr 4081, -1)]

theorem sourceEq1793 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1793 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1793 + difference 0 0) (sourceB1793 + difference 0 0) sourceC1793) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1006) := by
    have ha : (tripleCharges (sourceA1793 + difference 0 0) (sourceB1793 + difference 0 0) sourceC1793) = raw26074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1793 sourceB1793 sourceC1793 difference raw26074; decide +kernel
    rw [ha]
    exact (canonical26074 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1793 + difference 0 1) (sourceB1793 + difference 1 0) sourceC1793) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2001) := by
    have ha : (tripleCharges (sourceA1793 + difference 0 1) (sourceB1793 + difference 1 0) sourceC1793) = raw26075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1793 sourceB1793 sourceC1793 difference raw26075; decide +kernel
    rw [ha]
    exact (canonical26075 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1793 + difference 0 2) (sourceB1793 + difference 2 0) sourceC1793) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1948) := by
    have ha : (tripleCharges (sourceA1793 + difference 0 2) (sourceB1793 + difference 2 0) sourceC1793) = raw26076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1793 sourceB1793 sourceC1793 difference raw26076; decide +kernel
    rw [ha]
    exact (canonical26076 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1793 + difference 0 3) (sourceB1793 + difference 3 0) sourceC1793) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2221) := by
    have ha : (tripleCharges (sourceA1793 + difference 0 3) (sourceB1793 + difference 3 0) sourceC1793) = raw26077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1793 sourceB1793 sourceC1793 difference raw26077; decide +kernel
    rw [ha]
    exact (canonical26077 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1793 + difference 0 4) (sourceB1793 + difference 4 0) sourceC1793) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA1793 + difference 0 4) (sourceB1793 + difference 4 0) sourceC1793) = raw26078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1793 sourceB1793 sourceC1793 difference raw26078; decide +kernel
    rw [ha]
    exact (canonical26078 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1793 + difference 0 5) (sourceB1793 + difference 5 0) sourceC1793) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1793 + difference 0 5) (sourceB1793 + difference 5 0) sourceC1793) = raw26079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1793 sourceB1793 sourceC1793 difference raw26079; decide +kernel
    rw [ha]
    exact (canonical26079 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1793 + sourceB1793) sourceC1793) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1793 + sourceB1793) sourceC1793) = raw26080 := by
      apply Matrix.ext; unfold doubleCharges sourceA1793 sourceB1793 sourceC1793 raw26080; decide +kernel
    rw [ha]
    exact (canonical26080 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1793 sourceB1793 sourceC1793
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1793, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1794 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1794 : Charge := ![1, 0, -1, 2, 0, -2]
def sourceC1794 : Charge := ![3, 0, 1, -3, -1, 0]
def sourceForm1794 : Integer.Sparse Master := [(Sum.inr 995, 1), (Sum.inr 999, 1), (Sum.inr 1001, 1), (Sum.inr 1006, 1), (Sum.inr 1070, 1), (Sum.inr 2224, 1), (Sum.inr 4081, -1)]

theorem sourceEq1794 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1794 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1794 + difference 0 5) (sourceB1794 + difference 5 0) sourceC1794) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1794 + difference 0 5) (sourceB1794 + difference 5 0) sourceC1794) = raw26079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1794 sourceB1794 sourceC1794 difference raw26079; decide +kernel
    rw [ha]
    exact (canonical26079 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1794 + difference 1 5) (sourceB1794 + difference 5 1) sourceC1794) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 995) := by
    have ha : (tripleCharges (sourceA1794 + difference 1 5) (sourceB1794 + difference 5 1) sourceC1794) = raw26081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1794 sourceB1794 sourceC1794 difference raw26081; decide +kernel
    rw [ha]
    exact (canonical26081 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1794 + difference 2 5) (sourceB1794 + difference 5 2) sourceC1794) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1070) := by
    have ha : (tripleCharges (sourceA1794 + difference 2 5) (sourceB1794 + difference 5 2) sourceC1794) = raw26082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1794 sourceB1794 sourceC1794 difference raw26082; decide +kernel
    rw [ha]
    exact (canonical26082 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1794 + difference 3 5) (sourceB1794 + difference 5 3) sourceC1794) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 999) := by
    have ha : (tripleCharges (sourceA1794 + difference 3 5) (sourceB1794 + difference 5 3) sourceC1794) = raw26083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1794 sourceB1794 sourceC1794 difference raw26083; decide +kernel
    rw [ha]
    exact (canonical26083 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1794 + difference 4 5) (sourceB1794 + difference 5 4) sourceC1794) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1001) := by
    have ha : (tripleCharges (sourceA1794 + difference 4 5) (sourceB1794 + difference 5 4) sourceC1794) = raw26084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1794 sourceB1794 sourceC1794 difference raw26084; decide +kernel
    rw [ha]
    exact (canonical26084 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1794 + difference 5 5) (sourceB1794 + difference 5 5) sourceC1794) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1006) := by
    have ha : (tripleCharges (sourceA1794 + difference 5 5) (sourceB1794 + difference 5 5) sourceC1794) = raw26074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1794 sourceB1794 sourceC1794 difference raw26074; decide +kernel
    rw [ha]
    exact (canonical26074 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1794 + sourceB1794) sourceC1794) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1794 + sourceB1794) sourceC1794) = raw26080 := by
      apply Matrix.ext; unfold doubleCharges sourceA1794 sourceB1794 sourceC1794 raw26080; decide +kernel
    rw [ha]
    exact (canonical26080 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1794 sourceB1794 sourceC1794
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1794, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1795 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1795 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceC1795 : Charge := ![3, 0, 1, -3, 0, -1]
def sourceForm1795 : Integer.Sparse Master := [(Sum.inr 1001, 1), (Sum.inr 1946, 1), (Sum.inr 1998, 1), (Sum.inr 2220, 1), (Sum.inr 2224, 1), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

theorem sourceEq1795 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1795 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1795 + difference 0 0) (sourceB1795 + difference 0 0) sourceC1795) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1001) := by
    have ha : (tripleCharges (sourceA1795 + difference 0 0) (sourceB1795 + difference 0 0) sourceC1795) = raw26085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1795 sourceB1795 sourceC1795 difference raw26085; decide +kernel
    rw [ha]
    exact (canonical26085 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1795 + difference 0 1) (sourceB1795 + difference 1 0) sourceC1795) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1998) := by
    have ha : (tripleCharges (sourceA1795 + difference 0 1) (sourceB1795 + difference 1 0) sourceC1795) = raw26086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1795 sourceB1795 sourceC1795 difference raw26086; decide +kernel
    rw [ha]
    exact (canonical26086 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1795 + difference 0 2) (sourceB1795 + difference 2 0) sourceC1795) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1946) := by
    have ha : (tripleCharges (sourceA1795 + difference 0 2) (sourceB1795 + difference 2 0) sourceC1795) = raw26087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1795 sourceB1795 sourceC1795 difference raw26087; decide +kernel
    rw [ha]
    exact (canonical26087 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1795 + difference 0 3) (sourceB1795 + difference 3 0) sourceC1795) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA1795 + difference 0 3) (sourceB1795 + difference 3 0) sourceC1795) = raw26088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1795 sourceB1795 sourceC1795 difference raw26088; decide +kernel
    rw [ha]
    exact (canonical26088 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1795 + difference 0 4) (sourceB1795 + difference 4 0) sourceC1795) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1795 + difference 0 4) (sourceB1795 + difference 4 0) sourceC1795) = raw26089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1795 sourceB1795 sourceC1795 difference raw26089; decide +kernel
    rw [ha]
    exact (canonical26089 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1795 + difference 0 5) (sourceB1795 + difference 5 0) sourceC1795) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1795 + difference 0 5) (sourceB1795 + difference 5 0) sourceC1795) = raw26090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1795 sourceB1795 sourceC1795 difference raw26090; decide +kernel
    rw [ha]
    exact (canonical26090 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1795 + sourceB1795) sourceC1795) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1795 + sourceB1795) sourceC1795) = raw26091 := by
      apply Matrix.ext; unfold doubleCharges sourceA1795 sourceB1795 sourceC1795 raw26091; decide +kernel
    rw [ha]
    exact (canonical26091 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1795 sourceB1795 sourceC1795
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1795, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1796 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1796 : Charge := ![1, 0, -1, 1, 1, -2]
def sourceC1796 : Charge := ![3, 0, 1, -2, -2, 0]
def sourceForm1796 : Integer.Sparse Master := [(Sum.inr 1008, 1), (Sum.inr 1949, 1), (Sum.inr 2002, 1), (Sum.inr 2217, 2), (Sum.inr 2225, 1), (Sum.inr 4082, -1)]

theorem sourceEq1796 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1796 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1796 + difference 0 0) (sourceB1796 + difference 0 0) sourceC1796) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1008) := by
    have ha : (tripleCharges (sourceA1796 + difference 0 0) (sourceB1796 + difference 0 0) sourceC1796) = raw26092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1796 sourceB1796 sourceC1796 difference raw26092; decide +kernel
    rw [ha]
    exact (canonical26092 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1796 + difference 0 1) (sourceB1796 + difference 1 0) sourceC1796) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2002) := by
    have ha : (tripleCharges (sourceA1796 + difference 0 1) (sourceB1796 + difference 1 0) sourceC1796) = raw26093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1796 sourceB1796 sourceC1796 difference raw26093; decide +kernel
    rw [ha]
    exact (canonical26093 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1796 + difference 0 2) (sourceB1796 + difference 2 0) sourceC1796) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1949) := by
    have ha : (tripleCharges (sourceA1796 + difference 0 2) (sourceB1796 + difference 2 0) sourceC1796) = raw26094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1796 sourceB1796 sourceC1796 difference raw26094; decide +kernel
    rw [ha]
    exact (canonical26094 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1796 + difference 0 3) (sourceB1796 + difference 3 0) sourceC1796) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA1796 + difference 0 3) (sourceB1796 + difference 3 0) sourceC1796) = raw26095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1796 sourceB1796 sourceC1796 difference raw26095; decide +kernel
    rw [ha]
    exact (canonical26095 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1796 + difference 0 4) (sourceB1796 + difference 4 0) sourceC1796) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA1796 + difference 0 4) (sourceB1796 + difference 4 0) sourceC1796) = raw26096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1796 sourceB1796 sourceC1796 difference raw26096; decide +kernel
    rw [ha]
    exact (canonical26096 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1796 + difference 0 5) (sourceB1796 + difference 5 0) sourceC1796) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1796 + difference 0 5) (sourceB1796 + difference 5 0) sourceC1796) = raw26097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1796 sourceB1796 sourceC1796 difference raw26097; decide +kernel
    rw [ha]
    exact (canonical26097 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1796 + sourceB1796) sourceC1796) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1796 + sourceB1796) sourceC1796) = raw26098 := by
      apply Matrix.ext; unfold doubleCharges sourceA1796 sourceB1796 sourceC1796 raw26098; decide +kernel
    rw [ha]
    exact (canonical26098 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1796 sourceB1796 sourceC1796
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1796, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1797 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1797 : Charge := ![1, 0, -1, 1, 1, -2]
def sourceC1797 : Charge := ![3, 0, 1, -2, -2, 0]
def sourceForm1797 : Integer.Sparse Master := [(Sum.inr 996, 1), (Sum.inr 1000, 2), (Sum.inr 1008, 1), (Sum.inr 1071, 1), (Sum.inr 2225, 1), (Sum.inr 4082, -1)]

theorem sourceEq1797 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1797 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1797 + difference 0 5) (sourceB1797 + difference 5 0) sourceC1797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1797 + difference 0 5) (sourceB1797 + difference 5 0) sourceC1797) = raw26097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1797 sourceB1797 sourceC1797 difference raw26097; decide +kernel
    rw [ha]
    exact (canonical26097 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1797 + difference 1 5) (sourceB1797 + difference 5 1) sourceC1797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 996) := by
    have ha : (tripleCharges (sourceA1797 + difference 1 5) (sourceB1797 + difference 5 1) sourceC1797) = raw26099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1797 sourceB1797 sourceC1797 difference raw26099; decide +kernel
    rw [ha]
    exact (canonical26099 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1797 + difference 2 5) (sourceB1797 + difference 5 2) sourceC1797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1071) := by
    have ha : (tripleCharges (sourceA1797 + difference 2 5) (sourceB1797 + difference 5 2) sourceC1797) = raw26100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1797 sourceB1797 sourceC1797 difference raw26100; decide +kernel
    rw [ha]
    exact (canonical26100 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1797 + difference 3 5) (sourceB1797 + difference 5 3) sourceC1797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1797 + difference 3 5) (sourceB1797 + difference 5 3) sourceC1797) = raw26101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1797 sourceB1797 sourceC1797 difference raw26101; decide +kernel
    rw [ha]
    exact (canonical26101 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1797 + difference 4 5) (sourceB1797 + difference 5 4) sourceC1797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1797 + difference 4 5) (sourceB1797 + difference 5 4) sourceC1797) = raw26102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1797 sourceB1797 sourceC1797 difference raw26102; decide +kernel
    rw [ha]
    exact (canonical26102 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1797 + difference 5 5) (sourceB1797 + difference 5 5) sourceC1797) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1008) := by
    have ha : (tripleCharges (sourceA1797 + difference 5 5) (sourceB1797 + difference 5 5) sourceC1797) = raw26092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1797 sourceB1797 sourceC1797 difference raw26092; decide +kernel
    rw [ha]
    exact (canonical26092 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1797 + sourceB1797) sourceC1797) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1797 + sourceB1797) sourceC1797) = raw26098 := by
      apply Matrix.ext; unfold doubleCharges sourceA1797 sourceB1797 sourceC1797 raw26098; decide +kernel
    rw [ha]
    exact (canonical26098 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1797 sourceB1797 sourceC1797
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1797, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1798 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1798 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceC1798 : Charge := ![3, 0, 1, -2, -1, -1]
def sourceForm1798 : Integer.Sparse Master := [(Sum.inr 1005, 1), (Sum.inr 1947, 1), (Sum.inr 2000, 1), (Sum.inr 2206, 1), (Sum.inr 2216, 1), (Sum.inr 2227, 1), (Sum.inr 4080, -1)]

theorem sourceEq1798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1798 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1798 + difference 0 0) (sourceB1798 + difference 0 0) sourceC1798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1798 + difference 0 0) (sourceB1798 + difference 0 0) sourceC1798) = raw26103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1798 sourceB1798 sourceC1798 difference raw26103; decide +kernel
    rw [ha]
    exact (canonical26103 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1798 + difference 0 1) (sourceB1798 + difference 1 0) sourceC1798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2000) := by
    have ha : (tripleCharges (sourceA1798 + difference 0 1) (sourceB1798 + difference 1 0) sourceC1798) = raw26104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1798 sourceB1798 sourceC1798 difference raw26104; decide +kernel
    rw [ha]
    exact (canonical26104 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1798 + difference 0 2) (sourceB1798 + difference 2 0) sourceC1798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1947) := by
    have ha : (tripleCharges (sourceA1798 + difference 0 2) (sourceB1798 + difference 2 0) sourceC1798) = raw26105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1798 sourceB1798 sourceC1798 difference raw26105; decide +kernel
    rw [ha]
    exact (canonical26105 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1798 + difference 0 3) (sourceB1798 + difference 3 0) sourceC1798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1798 + difference 0 3) (sourceB1798 + difference 3 0) sourceC1798) = raw26106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1798 sourceB1798 sourceC1798 difference raw26106; decide +kernel
    rw [ha]
    exact (canonical26106 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1798 + difference 0 4) (sourceB1798 + difference 4 0) sourceC1798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1798 + difference 0 4) (sourceB1798 + difference 4 0) sourceC1798) = raw26107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1798 sourceB1798 sourceC1798 difference raw26107; decide +kernel
    rw [ha]
    exact (canonical26107 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1798 + difference 0 5) (sourceB1798 + difference 5 0) sourceC1798) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA1798 + difference 0 5) (sourceB1798 + difference 5 0) sourceC1798) = raw26108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1798 sourceB1798 sourceC1798 difference raw26108; decide +kernel
    rw [ha]
    exact (canonical26108 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1798 + sourceB1798) sourceC1798) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1798 + sourceB1798) sourceC1798) = raw26109 := by
      apply Matrix.ext; unfold doubleCharges sourceA1798 sourceB1798 sourceC1798 raw26109; decide +kernel
    rw [ha]
    exact (canonical26109 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1798 sourceB1798 sourceC1798
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1798, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1799 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1799 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceC1799 : Charge := ![3, 0, 1, -2, -1, -1]
def sourceForm1799 : Integer.Sparse Master := [(Sum.inr 879, 1), (Sum.inr 887, 1), (Sum.inr 889, 1), (Sum.inr 892, 1), (Sum.inr 1005, 1), (Sum.inr 1947, 1), (Sum.inr 4080, -1)]

theorem sourceEq1799 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1799 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1799 + difference 0 2) (sourceB1799 + difference 2 0) sourceC1799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1947) := by
    have ha : (tripleCharges (sourceA1799 + difference 0 2) (sourceB1799 + difference 2 0) sourceC1799) = raw26105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1799 sourceB1799 sourceC1799 difference raw26105; decide +kernel
    rw [ha]
    exact (canonical26105 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1799 + difference 1 2) (sourceB1799 + difference 2 1) sourceC1799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 879) := by
    have ha : (tripleCharges (sourceA1799 + difference 1 2) (sourceB1799 + difference 2 1) sourceC1799) = raw26110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1799 sourceB1799 sourceC1799 difference raw26110; decide +kernel
    rw [ha]
    exact (canonical26110 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1799 + difference 2 2) (sourceB1799 + difference 2 2) sourceC1799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1799 + difference 2 2) (sourceB1799 + difference 2 2) sourceC1799) = raw26103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1799 sourceB1799 sourceC1799 difference raw26103; decide +kernel
    rw [ha]
    exact (canonical26103 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1799 + difference 3 2) (sourceB1799 + difference 2 3) sourceC1799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 889) := by
    have ha : (tripleCharges (sourceA1799 + difference 3 2) (sourceB1799 + difference 2 3) sourceC1799) = raw26111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1799 sourceB1799 sourceC1799 difference raw26111; decide +kernel
    rw [ha]
    exact (canonical26111 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1799 + difference 4 2) (sourceB1799 + difference 2 4) sourceC1799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 892) := by
    have ha : (tripleCharges (sourceA1799 + difference 4 2) (sourceB1799 + difference 2 4) sourceC1799) = raw26112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1799 sourceB1799 sourceC1799 difference raw26112; decide +kernel
    rw [ha]
    exact (canonical26112 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1799 + difference 5 2) (sourceB1799 + difference 2 5) sourceC1799) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA1799 + difference 5 2) (sourceB1799 + difference 2 5) sourceC1799) = raw26113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1799 sourceB1799 sourceC1799 difference raw26113; decide +kernel
    rw [ha]
    exact (canonical26113 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1799 + sourceB1799) sourceC1799) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1799 + sourceB1799) sourceC1799) = raw26109 := by
      apply Matrix.ext; unfold doubleCharges sourceA1799 sourceB1799 sourceC1799 raw26109; decide +kernel
    rw [ha]
    exact (canonical26109 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1799 sourceB1799 sourceC1799
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1799, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1800 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1800 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceC1800 : Charge := ![3, 0, 1, -2, -1, -1]
def sourceForm1800 : Integer.Sparse Master := [(Sum.inr 998, 1), (Sum.inr 1004, 1), (Sum.inr 1005, 2), (Sum.inr 1073, 1), (Sum.inr 2227, 1), (Sum.inr 4080, -1)]

theorem sourceEq1800 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1800 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1800 + difference 0 5) (sourceB1800 + difference 5 0) sourceC1800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA1800 + difference 0 5) (sourceB1800 + difference 5 0) sourceC1800) = raw26108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1800 sourceB1800 sourceC1800 difference raw26108; decide +kernel
    rw [ha]
    exact (canonical26108 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1800 + difference 1 5) (sourceB1800 + difference 5 1) sourceC1800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 998) := by
    have ha : (tripleCharges (sourceA1800 + difference 1 5) (sourceB1800 + difference 5 1) sourceC1800) = raw26114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1800 sourceB1800 sourceC1800 difference raw26114; decide +kernel
    rw [ha]
    exact (canonical26114 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1800 + difference 2 5) (sourceB1800 + difference 5 2) sourceC1800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1800 + difference 2 5) (sourceB1800 + difference 5 2) sourceC1800) = raw26115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1800 sourceB1800 sourceC1800 difference raw26115; decide +kernel
    rw [ha]
    exact (canonical26115 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1800 + difference 3 5) (sourceB1800 + difference 5 3) sourceC1800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1004) := by
    have ha : (tripleCharges (sourceA1800 + difference 3 5) (sourceB1800 + difference 5 3) sourceC1800) = raw26116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1800 sourceB1800 sourceC1800 difference raw26116; decide +kernel
    rw [ha]
    exact (canonical26116 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1800 + difference 4 5) (sourceB1800 + difference 5 4) sourceC1800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1800 + difference 4 5) (sourceB1800 + difference 5 4) sourceC1800) = raw26117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1800 sourceB1800 sourceC1800 difference raw26117; decide +kernel
    rw [ha]
    exact (canonical26117 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1800 + difference 5 5) (sourceB1800 + difference 5 5) sourceC1800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1800 + difference 5 5) (sourceB1800 + difference 5 5) sourceC1800) = raw26103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1800 sourceB1800 sourceC1800 difference raw26103; decide +kernel
    rw [ha]
    exact (canonical26103 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1800 + sourceB1800) sourceC1800) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1800 + sourceB1800) sourceC1800) = raw26109 := by
      apply Matrix.ext; unfold doubleCharges sourceA1800 sourceB1800 sourceC1800 raw26109; decide +kernel
    rw [ha]
    exact (canonical26109 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1800 sourceB1800 sourceC1800
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1800, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1801 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceB1801 : Charge := ![3, 0, 1, -2, -1, -1]
def sourceC1801 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1801 : Integer.Sparse Master := [(Sum.inr 713, 1), (Sum.inr 720, 1), (Sum.inr 722, 1), (Sum.inr 725, 1), (Sum.inr 856, 1), (Sum.inr 1623, 1), (Sum.inr 4069, -1)]

theorem sourceEq1801 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1801 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1801 + difference 0 0) (sourceB1801 + difference 0 0) sourceC1801) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1623) := by
    have ha : (tripleCharges (sourceA1801 + difference 0 0) (sourceB1801 + difference 0 0) sourceC1801) = raw26118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1801 sourceB1801 sourceC1801 difference raw26118; decide +kernel
    rw [ha]
    exact (canonical26118 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1801 + difference 1 0) (sourceB1801 + difference 0 1) sourceC1801) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 713) := by
    have ha : (tripleCharges (sourceA1801 + difference 1 0) (sourceB1801 + difference 0 1) sourceC1801) = raw25544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1801 sourceB1801 sourceC1801 difference raw25544; decide +kernel
    rw [ha]
    exact (canonical25544 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1801 + difference 2 0) (sourceB1801 + difference 0 2) sourceC1801) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 856) := by
    have ha : (tripleCharges (sourceA1801 + difference 2 0) (sourceB1801 + difference 0 2) sourceC1801) = raw26119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1801 sourceB1801 sourceC1801 difference raw26119; decide +kernel
    rw [ha]
    exact (canonical26119 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1801 + difference 3 0) (sourceB1801 + difference 0 3) sourceC1801) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 720) := by
    have ha : (tripleCharges (sourceA1801 + difference 3 0) (sourceB1801 + difference 0 3) sourceC1801) = raw26120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1801 sourceB1801 sourceC1801 difference raw26120; decide +kernel
    rw [ha]
    exact (canonical26120 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1801 + difference 4 0) (sourceB1801 + difference 0 4) sourceC1801) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 725) := by
    have ha : (tripleCharges (sourceA1801 + difference 4 0) (sourceB1801 + difference 0 4) sourceC1801) = raw26121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1801 sourceB1801 sourceC1801 difference raw26121; decide +kernel
    rw [ha]
    exact (canonical26121 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1801 + difference 5 0) (sourceB1801 + difference 0 5) sourceC1801) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 722) := by
    have ha : (tripleCharges (sourceA1801 + difference 5 0) (sourceB1801 + difference 0 5) sourceC1801) = raw26122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1801 sourceB1801 sourceC1801 difference raw26122; decide +kernel
    rw [ha]
    exact (canonical26122 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1801 + sourceB1801) sourceC1801) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1801 + sourceB1801) sourceC1801) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1801 sourceB1801 sourceC1801 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1801 sourceB1801 sourceC1801
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1801, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1802 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceB1802 : Charge := ![3, 0, 1, -2, -1, -1]
def sourceC1802 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1802 : Integer.Sparse Master := [(Sum.inr 722, 1), (Sum.inr 1547, 1), (Sum.inr 1583, 1), (Sum.inr 1605, 1), (Sum.inr 1622, 1), (Sum.inr 1623, 1), (Sum.inr 4069, -1)]

theorem sourceEq1802 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1802 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1802 + difference 5 0) (sourceB1802 + difference 0 5) sourceC1802) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 722) := by
    have ha : (tripleCharges (sourceA1802 + difference 5 0) (sourceB1802 + difference 0 5) sourceC1802) = raw26122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1802 sourceB1802 sourceC1802 difference raw26122; decide +kernel
    rw [ha]
    exact (canonical26122 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1802 + difference 5 1) (sourceB1802 + difference 1 5) sourceC1802) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1583) := by
    have ha : (tripleCharges (sourceA1802 + difference 5 1) (sourceB1802 + difference 1 5) sourceC1802) = raw24906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1802 sourceB1802 sourceC1802 difference raw24906; decide +kernel
    rw [ha]
    exact (canonical24906 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1802 + difference 5 2) (sourceB1802 + difference 2 5) sourceC1802) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1547) := by
    have ha : (tripleCharges (sourceA1802 + difference 5 2) (sourceB1802 + difference 2 5) sourceC1802) = raw24865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1802 sourceB1802 sourceC1802 difference raw24865; decide +kernel
    rw [ha]
    exact (canonical24865 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1802 + difference 5 3) (sourceB1802 + difference 3 5) sourceC1802) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1622) := by
    have ha : (tripleCharges (sourceA1802 + difference 5 3) (sourceB1802 + difference 3 5) sourceC1802) = raw24864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1802 sourceB1802 sourceC1802 difference raw24864; decide +kernel
    rw [ha]
    exact (canonical24864 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1802 + difference 5 4) (sourceB1802 + difference 4 5) sourceC1802) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1605) := by
    have ha : (tripleCharges (sourceA1802 + difference 5 4) (sourceB1802 + difference 4 5) sourceC1802) = raw26123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1802 sourceB1802 sourceC1802 difference raw26123; decide +kernel
    rw [ha]
    exact (canonical26123 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1802 + difference 5 5) (sourceB1802 + difference 5 5) sourceC1802) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1623) := by
    have ha : (tripleCharges (sourceA1802 + difference 5 5) (sourceB1802 + difference 5 5) sourceC1802) = raw26118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1802 sourceB1802 sourceC1802 difference raw26118; decide +kernel
    rw [ha]
    exact (canonical26118 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1802 + sourceB1802) sourceC1802) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1802 + sourceB1802) sourceC1802) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1802 sourceB1802 sourceC1802 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1802 sourceB1802 sourceC1802
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1802, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1803 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1803 : Charge := ![1, 0, -1, 1, -1, 0]
def sourceC1803 : Charge := ![3, 0, 1, -2, 0, -2]
def sourceForm1803 : Integer.Sparse Master := [(Sum.inr 1000, 1), (Sum.inr 1945, 1), (Sum.inr 1997, 1), (Sum.inr 2215, 1), (Sum.inr 2225, 1), (Sum.inr 2229, 1), (Sum.inr 4082, -1)]

theorem sourceEq1803 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1803 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1803 + difference 0 0) (sourceB1803 + difference 0 0) sourceC1803) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1803 + difference 0 0) (sourceB1803 + difference 0 0) sourceC1803) = raw26124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1803 sourceB1803 sourceC1803 difference raw26124; decide +kernel
    rw [ha]
    exact (canonical26124 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1803 + difference 0 1) (sourceB1803 + difference 1 0) sourceC1803) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1997) := by
    have ha : (tripleCharges (sourceA1803 + difference 0 1) (sourceB1803 + difference 1 0) sourceC1803) = raw26125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1803 sourceB1803 sourceC1803 difference raw26125; decide +kernel
    rw [ha]
    exact (canonical26125 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1803 + difference 0 2) (sourceB1803 + difference 2 0) sourceC1803) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1945) := by
    have ha : (tripleCharges (sourceA1803 + difference 0 2) (sourceB1803 + difference 2 0) sourceC1803) = raw26126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1803 sourceB1803 sourceC1803 difference raw26126; decide +kernel
    rw [ha]
    exact (canonical26126 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1803 + difference 0 3) (sourceB1803 + difference 3 0) sourceC1803) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1803 + difference 0 3) (sourceB1803 + difference 3 0) sourceC1803) = raw26127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1803 sourceB1803 sourceC1803 difference raw26127; decide +kernel
    rw [ha]
    exact (canonical26127 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1803 + difference 0 4) (sourceB1803 + difference 4 0) sourceC1803) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA1803 + difference 0 4) (sourceB1803 + difference 4 0) sourceC1803) = raw26128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1803 sourceB1803 sourceC1803 difference raw26128; decide +kernel
    rw [ha]
    exact (canonical26128 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1803 + difference 0 5) (sourceB1803 + difference 5 0) sourceC1803) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1803 + difference 0 5) (sourceB1803 + difference 5 0) sourceC1803) = raw26129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1803 sourceB1803 sourceC1803 difference raw26129; decide +kernel
    rw [ha]
    exact (canonical26129 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1803 + sourceB1803) sourceC1803) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1803 + sourceB1803) sourceC1803) = raw26130 := by
      apply Matrix.ext; unfold doubleCharges sourceA1803 sourceB1803 sourceC1803 raw26130; decide +kernel
    rw [ha]
    exact (canonical26130 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1803 sourceB1803 sourceC1803
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1803, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1804 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1804 : Charge := ![1, 0, -1, 1, -1, 0]
def sourceC1804 : Charge := ![3, 0, 1, -2, 0, -2]
def sourceForm1804 : Integer.Sparse Master := [(Sum.inr 876, 1), (Sum.inr 881, 1), (Sum.inr 883, 1), (Sum.inr 891, 1), (Sum.inr 1000, 1), (Sum.inr 1945, 1), (Sum.inr 4082, -1)]

theorem sourceEq1804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1804 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1804 + difference 0 2) (sourceB1804 + difference 2 0) sourceC1804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1945) := by
    have ha : (tripleCharges (sourceA1804 + difference 0 2) (sourceB1804 + difference 2 0) sourceC1804) = raw26126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1804 sourceB1804 sourceC1804 difference raw26126; decide +kernel
    rw [ha]
    exact (canonical26126 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1804 + difference 1 2) (sourceB1804 + difference 2 1) sourceC1804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 876) := by
    have ha : (tripleCharges (sourceA1804 + difference 1 2) (sourceB1804 + difference 2 1) sourceC1804) = raw26131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1804 sourceB1804 sourceC1804 difference raw26131; decide +kernel
    rw [ha]
    exact (canonical26131 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1804 + difference 2 2) (sourceB1804 + difference 2 2) sourceC1804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1804 + difference 2 2) (sourceB1804 + difference 2 2) sourceC1804) = raw26124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1804 sourceB1804 sourceC1804 difference raw26124; decide +kernel
    rw [ha]
    exact (canonical26124 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1804 + difference 3 2) (sourceB1804 + difference 2 3) sourceC1804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 883) := by
    have ha : (tripleCharges (sourceA1804 + difference 3 2) (sourceB1804 + difference 2 3) sourceC1804) = raw26132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1804 sourceB1804 sourceC1804 difference raw26132; decide +kernel
    rw [ha]
    exact (canonical26132 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1804 + difference 4 2) (sourceB1804 + difference 2 4) sourceC1804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 891) := by
    have ha : (tripleCharges (sourceA1804 + difference 4 2) (sourceB1804 + difference 2 4) sourceC1804) = raw26133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1804 sourceB1804 sourceC1804 difference raw26133; decide +kernel
    rw [ha]
    exact (canonical26133 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1804 + difference 5 2) (sourceB1804 + difference 2 5) sourceC1804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 881) := by
    have ha : (tripleCharges (sourceA1804 + difference 5 2) (sourceB1804 + difference 2 5) sourceC1804) = raw26134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1804 sourceB1804 sourceC1804 difference raw26134; decide +kernel
    rw [ha]
    exact (canonical26134 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1804 + sourceB1804) sourceC1804) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1804 + sourceB1804) sourceC1804) = raw26130 := by
      apply Matrix.ext; unfold doubleCharges sourceA1804 sourceB1804 sourceC1804 raw26130; decide +kernel
    rw [ha]
    exact (canonical26130 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1804 sourceB1804 sourceC1804
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1804, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1805 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1805 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceC1805 : Charge := ![3, 0, 1, -1, -1, -2]
def sourceForm1805 : Integer.Sparse Master := [(Sum.inr 4080, 1), (Sum.inr 4139, 1), (Sum.inr 4144, 1), (Sum.inr 4145, 2), (Sum.inr 4165, 1), (Sum.inr 4300, 1), (Sum.inr 4308, 1), (Sum.inr 4311, 2), (Sum.inr 4322, 1), (Sum.inr 4323, 2), (Sum.inr 4337, 1), (Sum.inr 4396, 2), (Sum.inr 4401, 2), (Sum.inr 4404, 2), (Sum.inr 4417, 1), (Sum.inr 4424, 2), (Sum.inr 4452, 2), (Sum.inr 4489, 1), (Sum.inr 4786, 1), (Sum.inr 4834, 2), (Sum.inr 4838, 1)]

theorem sourceEq1805 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1805 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1805 + difference 0 1) (sourceB1805 + difference 1 0) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4786) := by
    have ha : (tripleCharges (sourceA1805 + difference 0 1) (sourceB1805 + difference 1 0) sourceC1805) = raw26135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26135; decide +kernel
    rw [ha]
    exact (canonical26135 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1805 + difference 0 2) (sourceB1805 + difference 2 0) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA1805 + difference 0 2) (sourceB1805 + difference 2 0) sourceC1805) = raw26136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26136; decide +kernel
    rw [ha]
    exact (canonical26136 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1805 + difference 0 3) (sourceB1805 + difference 3 0) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA1805 + difference 0 3) (sourceB1805 + difference 3 0) sourceC1805) = raw26137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26137; decide +kernel
    rw [ha]
    exact (canonical26137 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1805 + difference 0 4) (sourceB1805 + difference 4 0) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA1805 + difference 0 4) (sourceB1805 + difference 4 0) sourceC1805) = raw26138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26138; decide +kernel
    rw [ha]
    exact (canonical26138 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1805 + difference 0 5) (sourceB1805 + difference 5 0) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA1805 + difference 0 5) (sourceB1805 + difference 5 0) sourceC1805) = raw26139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26139; decide +kernel
    rw [ha]
    exact (canonical26139 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1805 + difference 1 0) (sourceB1805 + difference 0 1) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4139) := by
    have ha : (tripleCharges (sourceA1805 + difference 1 0) (sourceB1805 + difference 0 1) sourceC1805) = raw26140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26140; decide +kernel
    rw [ha]
    exact (canonical26140 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1805 + difference 1 2) (sourceB1805 + difference 2 1) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4300) := by
    have ha : (tripleCharges (sourceA1805 + difference 1 2) (sourceB1805 + difference 2 1) sourceC1805) = raw26141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26141; decide +kernel
    rw [ha]
    exact (canonical26141 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1805 + difference 1 3) (sourceB1805 + difference 3 1) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1805 + difference 1 3) (sourceB1805 + difference 3 1) sourceC1805) = raw26142 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26142; decide +kernel
    rw [ha]
    exact (canonical26142 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1805 + difference 1 4) (sourceB1805 + difference 4 1) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1805 + difference 1 4) (sourceB1805 + difference 4 1) sourceC1805) = raw26143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26143; decide +kernel
    rw [ha]
    exact (canonical26143 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1805 + difference 1 5) (sourceB1805 + difference 5 1) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1805 + difference 1 5) (sourceB1805 + difference 5 1) sourceC1805) = raw26144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26144; decide +kernel
    rw [ha]
    exact (canonical26144 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1805 + difference 2 0) (sourceB1805 + difference 0 2) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4165) := by
    have ha : (tripleCharges (sourceA1805 + difference 2 0) (sourceB1805 + difference 0 2) sourceC1805) = raw26145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26145; decide +kernel
    rw [ha]
    exact (canonical26145 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1805 + difference 2 1) (sourceB1805 + difference 1 2) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4337) := by
    have ha : (tripleCharges (sourceA1805 + difference 2 1) (sourceB1805 + difference 1 2) sourceC1805) = raw26146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26146; decide +kernel
    rw [ha]
    exact (canonical26146 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1805 + difference 2 3) (sourceB1805 + difference 3 2) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1805 + difference 2 3) (sourceB1805 + difference 3 2) sourceC1805) = raw26147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26147; decide +kernel
    rw [ha]
    exact (canonical26147 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1805 + difference 2 4) (sourceB1805 + difference 4 2) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1805 + difference 2 4) (sourceB1805 + difference 4 2) sourceC1805) = raw26148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26148; decide +kernel
    rw [ha]
    exact (canonical26148 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1805 + difference 2 5) (sourceB1805 + difference 5 2) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA1805 + difference 2 5) (sourceB1805 + difference 5 2) sourceC1805) = raw26149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26149; decide +kernel
    rw [ha]
    exact (canonical26149 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1805 + difference 3 0) (sourceB1805 + difference 0 3) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4145) := by
    have ha : (tripleCharges (sourceA1805 + difference 3 0) (sourceB1805 + difference 0 3) sourceC1805) = raw26150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26150; decide +kernel
    rw [ha]
    exact (canonical26150 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1805 + difference 3 1) (sourceB1805 + difference 1 3) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4323) := by
    have ha : (tripleCharges (sourceA1805 + difference 3 1) (sourceB1805 + difference 1 3) sourceC1805) = raw26151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26151; decide +kernel
    rw [ha]
    exact (canonical26151 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1805 + difference 3 2) (sourceB1805 + difference 2 3) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4311) := by
    have ha : (tripleCharges (sourceA1805 + difference 3 2) (sourceB1805 + difference 2 3) sourceC1805) = raw26152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26152; decide +kernel
    rw [ha]
    exact (canonical26152 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1805 + difference 3 4) (sourceB1805 + difference 4 3) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1805 + difference 3 4) (sourceB1805 + difference 4 3) sourceC1805) = raw26153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26153; decide +kernel
    rw [ha]
    exact (canonical26153 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1805 + difference 3 5) (sourceB1805 + difference 5 3) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1805 + difference 3 5) (sourceB1805 + difference 5 3) sourceC1805) = raw26154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26154; decide +kernel
    rw [ha]
    exact (canonical26154 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1805 + difference 4 0) (sourceB1805 + difference 0 4) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4145) := by
    have ha : (tripleCharges (sourceA1805 + difference 4 0) (sourceB1805 + difference 0 4) sourceC1805) = raw26155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26155; decide +kernel
    rw [ha]
    exact (canonical26155 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1805 + difference 4 1) (sourceB1805 + difference 1 4) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4323) := by
    have ha : (tripleCharges (sourceA1805 + difference 4 1) (sourceB1805 + difference 1 4) sourceC1805) = raw26156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26156; decide +kernel
    rw [ha]
    exact (canonical26156 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1805 + difference 4 2) (sourceB1805 + difference 2 4) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4311) := by
    have ha : (tripleCharges (sourceA1805 + difference 4 2) (sourceB1805 + difference 2 4) sourceC1805) = raw26157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26157; decide +kernel
    rw [ha]
    exact (canonical26157 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1805 + difference 4 3) (sourceB1805 + difference 3 4) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1805 + difference 4 3) (sourceB1805 + difference 3 4) sourceC1805) = raw26158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26158; decide +kernel
    rw [ha]
    exact (canonical26158 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1805 + difference 4 5) (sourceB1805 + difference 5 4) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1805 + difference 4 5) (sourceB1805 + difference 5 4) sourceC1805) = raw26159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26159; decide +kernel
    rw [ha]
    exact (canonical26159 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1805 + difference 5 0) (sourceB1805 + difference 0 5) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4144) := by
    have ha : (tripleCharges (sourceA1805 + difference 5 0) (sourceB1805 + difference 0 5) sourceC1805) = raw26160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26160; decide +kernel
    rw [ha]
    exact (canonical26160 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1805 + difference 5 1) (sourceB1805 + difference 1 5) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4322) := by
    have ha : (tripleCharges (sourceA1805 + difference 5 1) (sourceB1805 + difference 1 5) sourceC1805) = raw26161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26161; decide +kernel
    rw [ha]
    exact (canonical26161 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1805 + difference 5 2) (sourceB1805 + difference 2 5) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4308) := by
    have ha : (tripleCharges (sourceA1805 + difference 5 2) (sourceB1805 + difference 2 5) sourceC1805) = raw26162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26162; decide +kernel
    rw [ha]
    exact (canonical26162 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1805 + difference 5 3) (sourceB1805 + difference 3 5) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1805 + difference 5 3) (sourceB1805 + difference 3 5) sourceC1805) = raw26163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26163; decide +kernel
    rw [ha]
    exact (canonical26163 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1805 + difference 5 4) (sourceB1805 + difference 4 5) sourceC1805) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1805 + difference 5 4) (sourceB1805 + difference 4 5) sourceC1805) = raw26164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1805 sourceB1805 sourceC1805 difference raw26164; decide +kernel
    rw [ha]
    exact (canonical26164 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1805 sourceB1805 sourceC1805
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1805, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1806 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceB1806 : Charge := ![3, 0, 1, -1, -1, -2]
def sourceC1806 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1806 : Integer.Sparse Master := [(Sum.inr 4069, 1), (Sum.inr 4209, 1), (Sum.inr 4218, 1), (Sum.inr 4221, 2), (Sum.inr 4376, 1), (Sum.inr 4380, 1), (Sum.inr 4381, 2), (Sum.inr 4386, 1), (Sum.inr 4387, 2), (Sum.inr 4396, 2), (Sum.inr 4399, 1), (Sum.inr 4418, 2), (Sum.inr 4419, 2), (Sum.inr 4423, 1), (Sum.inr 4424, 2), (Sum.inr 4498, 2), (Sum.inr 4502, 1), (Sum.inr 4570, 1), (Sum.inr 4581, 1), (Sum.inr 4602, 2), (Sum.inr 4606, 1)]

theorem sourceEq1806 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1806 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1806 + difference 0 1) (sourceB1806 + difference 1 0) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA1806 + difference 0 1) (sourceB1806 + difference 1 0) sourceC1806) = raw24618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw24618; decide +kernel
    rw [ha]
    exact (canonical24618 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1806 + difference 0 2) (sourceB1806 + difference 2 0) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4570) := by
    have ha : (tripleCharges (sourceA1806 + difference 0 2) (sourceB1806 + difference 2 0) sourceC1806) = raw24619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw24619; decide +kernel
    rw [ha]
    exact (canonical24619 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1806 + difference 0 3) (sourceB1806 + difference 3 0) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1806 + difference 0 3) (sourceB1806 + difference 3 0) sourceC1806) = raw24174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw24174; decide +kernel
    rw [ha]
    exact (canonical24174 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1806 + difference 0 4) (sourceB1806 + difference 4 0) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1806 + difference 0 4) (sourceB1806 + difference 4 0) sourceC1806) = raw24169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw24169; decide +kernel
    rw [ha]
    exact (canonical24169 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1806 + difference 0 5) (sourceB1806 + difference 5 0) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1806 + difference 0 5) (sourceB1806 + difference 5 0) sourceC1806) = raw24262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw24262; decide +kernel
    rw [ha]
    exact (canonical24262 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1806 + difference 1 0) (sourceB1806 + difference 0 1) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4209) := by
    have ha : (tripleCharges (sourceA1806 + difference 1 0) (sourceB1806 + difference 0 1) sourceC1806) = raw26165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw26165; decide +kernel
    rw [ha]
    exact (canonical26165 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1806 + difference 1 2) (sourceB1806 + difference 2 1) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4376) := by
    have ha : (tripleCharges (sourceA1806 + difference 1 2) (sourceB1806 + difference 2 1) sourceC1806) = raw26166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw26166; decide +kernel
    rw [ha]
    exact (canonical26166 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1806 + difference 1 3) (sourceB1806 + difference 3 1) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1806 + difference 1 3) (sourceB1806 + difference 3 1) sourceC1806) = raw25479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw25479; decide +kernel
    rw [ha]
    exact (canonical25479 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1806 + difference 1 4) (sourceB1806 + difference 4 1) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1806 + difference 1 4) (sourceB1806 + difference 4 1) sourceC1806) = raw24815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw24815; decide +kernel
    rw [ha]
    exact (canonical24815 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1806 + difference 1 5) (sourceB1806 + difference 5 1) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1806 + difference 1 5) (sourceB1806 + difference 5 1) sourceC1806) = raw24605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw24605; decide +kernel
    rw [ha]
    exact (canonical24605 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1806 + difference 2 0) (sourceB1806 + difference 0 2) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1806 + difference 2 0) (sourceB1806 + difference 0 2) sourceC1806) = raw26167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw26167; decide +kernel
    rw [ha]
    exact (canonical26167 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1806 + difference 2 1) (sourceB1806 + difference 1 2) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4423) := by
    have ha : (tripleCharges (sourceA1806 + difference 2 1) (sourceB1806 + difference 1 2) sourceC1806) = raw26168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw26168; decide +kernel
    rw [ha]
    exact (canonical26168 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1806 + difference 2 3) (sourceB1806 + difference 3 2) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1806 + difference 2 3) (sourceB1806 + difference 3 2) sourceC1806) = raw24172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw24172; decide +kernel
    rw [ha]
    exact (canonical24172 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1806 + difference 2 4) (sourceB1806 + difference 4 2) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1806 + difference 2 4) (sourceB1806 + difference 4 2) sourceC1806) = raw24167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw24167; decide +kernel
    rw [ha]
    exact (canonical24167 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1806 + difference 2 5) (sourceB1806 + difference 5 2) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1806 + difference 2 5) (sourceB1806 + difference 5 2) sourceC1806) = raw24260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw24260; decide +kernel
    rw [ha]
    exact (canonical24260 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1806 + difference 3 0) (sourceB1806 + difference 0 3) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4221) := by
    have ha : (tripleCharges (sourceA1806 + difference 3 0) (sourceB1806 + difference 0 3) sourceC1806) = raw26169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw26169; decide +kernel
    rw [ha]
    exact (canonical26169 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1806 + difference 3 1) (sourceB1806 + difference 1 3) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4387) := by
    have ha : (tripleCharges (sourceA1806 + difference 3 1) (sourceB1806 + difference 1 3) sourceC1806) = raw26170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw26170; decide +kernel
    rw [ha]
    exact (canonical26170 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1806 + difference 3 2) (sourceB1806 + difference 2 3) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4381) := by
    have ha : (tripleCharges (sourceA1806 + difference 3 2) (sourceB1806 + difference 2 3) sourceC1806) = raw26171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw26171; decide +kernel
    rw [ha]
    exact (canonical26171 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1806 + difference 3 4) (sourceB1806 + difference 4 3) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1806 + difference 3 4) (sourceB1806 + difference 4 3) sourceC1806) = raw24818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw24818; decide +kernel
    rw [ha]
    exact (canonical24818 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1806 + difference 3 5) (sourceB1806 + difference 5 3) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1806 + difference 3 5) (sourceB1806 + difference 5 3) sourceC1806) = raw24609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw24609; decide +kernel
    rw [ha]
    exact (canonical24609 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1806 + difference 4 0) (sourceB1806 + difference 0 4) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4221) := by
    have ha : (tripleCharges (sourceA1806 + difference 4 0) (sourceB1806 + difference 0 4) sourceC1806) = raw26172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw26172; decide +kernel
    rw [ha]
    exact (canonical26172 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1806 + difference 4 1) (sourceB1806 + difference 1 4) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4387) := by
    have ha : (tripleCharges (sourceA1806 + difference 4 1) (sourceB1806 + difference 1 4) sourceC1806) = raw26173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw26173; decide +kernel
    rw [ha]
    exact (canonical26173 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1806 + difference 4 2) (sourceB1806 + difference 2 4) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4381) := by
    have ha : (tripleCharges (sourceA1806 + difference 4 2) (sourceB1806 + difference 2 4) sourceC1806) = raw26174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw26174; decide +kernel
    rw [ha]
    exact (canonical26174 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1806 + difference 4 3) (sourceB1806 + difference 3 4) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1806 + difference 4 3) (sourceB1806 + difference 3 4) sourceC1806) = raw26175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw26175; decide +kernel
    rw [ha]
    exact (canonical26175 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1806 + difference 4 5) (sourceB1806 + difference 5 4) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1806 + difference 4 5) (sourceB1806 + difference 5 4) sourceC1806) = raw24614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw24614; decide +kernel
    rw [ha]
    exact (canonical24614 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1806 + difference 5 0) (sourceB1806 + difference 0 5) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4218) := by
    have ha : (tripleCharges (sourceA1806 + difference 5 0) (sourceB1806 + difference 0 5) sourceC1806) = raw26176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw26176; decide +kernel
    rw [ha]
    exact (canonical26176 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1806 + difference 5 1) (sourceB1806 + difference 1 5) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4386) := by
    have ha : (tripleCharges (sourceA1806 + difference 5 1) (sourceB1806 + difference 1 5) sourceC1806) = raw26177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw26177; decide +kernel
    rw [ha]
    exact (canonical26177 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1806 + difference 5 2) (sourceB1806 + difference 2 5) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4380) := by
    have ha : (tripleCharges (sourceA1806 + difference 5 2) (sourceB1806 + difference 2 5) sourceC1806) = raw26178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw26178; decide +kernel
    rw [ha]
    exact (canonical26178 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1806 + difference 5 3) (sourceB1806 + difference 3 5) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1806 + difference 5 3) (sourceB1806 + difference 3 5) sourceC1806) = raw26050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw26050; decide +kernel
    rw [ha]
    exact (canonical26050 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1806 + difference 5 4) (sourceB1806 + difference 4 5) sourceC1806) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1806 + difference 5 4) (sourceB1806 + difference 4 5) sourceC1806) = raw24822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1806 sourceB1806 sourceC1806 difference raw24822; decide +kernel
    rw [ha]
    exact (canonical24822 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1806 sourceB1806 sourceC1806
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1806, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1807 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1807 : Charge := ![1, 0, -1, 0, -1, 1]
def sourceC1807 : Charge := ![3, 0, 1, -1, 0, -3]
def sourceForm1807 : Integer.Sparse Master := [(Sum.inr 999, 1), (Sum.inr 1944, 1), (Sum.inr 1996, 1), (Sum.inr 2203, 1), (Sum.inr 2224, 1), (Sum.inr 2228, 1), (Sum.inr 4081, -1)]

theorem sourceEq1807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1807 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1807 + difference 0 0) (sourceB1807 + difference 0 0) sourceC1807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 999) := by
    have ha : (tripleCharges (sourceA1807 + difference 0 0) (sourceB1807 + difference 0 0) sourceC1807) = raw26179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1807 sourceB1807 sourceC1807 difference raw26179; decide +kernel
    rw [ha]
    exact (canonical26179 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1807 + difference 0 1) (sourceB1807 + difference 1 0) sourceC1807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1996) := by
    have ha : (tripleCharges (sourceA1807 + difference 0 1) (sourceB1807 + difference 1 0) sourceC1807) = raw26180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1807 sourceB1807 sourceC1807 difference raw26180; decide +kernel
    rw [ha]
    exact (canonical26180 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1807 + difference 0 2) (sourceB1807 + difference 2 0) sourceC1807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1944) := by
    have ha : (tripleCharges (sourceA1807 + difference 0 2) (sourceB1807 + difference 2 0) sourceC1807) = raw26181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1807 sourceB1807 sourceC1807 difference raw26181; decide +kernel
    rw [ha]
    exact (canonical26181 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1807 + difference 0 3) (sourceB1807 + difference 3 0) sourceC1807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1807 + difference 0 3) (sourceB1807 + difference 3 0) sourceC1807) = raw26182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1807 sourceB1807 sourceC1807 difference raw26182; decide +kernel
    rw [ha]
    exact (canonical26182 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1807 + difference 0 4) (sourceB1807 + difference 4 0) sourceC1807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA1807 + difference 0 4) (sourceB1807 + difference 4 0) sourceC1807) = raw26183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1807 sourceB1807 sourceC1807 difference raw26183; decide +kernel
    rw [ha]
    exact (canonical26183 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1807 + difference 0 5) (sourceB1807 + difference 5 0) sourceC1807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1807 + difference 0 5) (sourceB1807 + difference 5 0) sourceC1807) = raw26184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1807 sourceB1807 sourceC1807 difference raw26184; decide +kernel
    rw [ha]
    exact (canonical26184 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1807 + sourceB1807) sourceC1807) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1807 + sourceB1807) sourceC1807) = raw26185 := by
      apply Matrix.ext; unfold doubleCharges sourceA1807 sourceB1807 sourceC1807 raw26185; decide +kernel
    rw [ha]
    exact (canonical26185 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1807 sourceB1807 sourceC1807
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1807, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1808 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1808 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC1808 : Charge := ![4, -2, 0, -1, -1, 0]
def sourceForm1808 : Integer.Sparse Master := [(Sum.inr 557, 1), (Sum.inr 719, 1), (Sum.inr 811, 2), (Sum.inr 827, 1), (Sum.inr 850, 1), (Sum.inr 4069, -1)]

theorem sourceEq1808 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1808 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1808 + difference 1 0) (sourceB1808 + difference 0 1) sourceC1808) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 557) := by
    have ha : (tripleCharges (sourceA1808 + difference 1 0) (sourceB1808 + difference 0 1) sourceC1808) = raw26186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1808 sourceB1808 sourceC1808 difference raw26186; decide +kernel
    rw [ha]
    exact (canonical26186 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1808 + difference 1 1) (sourceB1808 + difference 1 1) sourceC1808) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 827) := by
    have ha : (tripleCharges (sourceA1808 + difference 1 1) (sourceB1808 + difference 1 1) sourceC1808) = raw26187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1808 sourceB1808 sourceC1808 difference raw26187; decide +kernel
    rw [ha]
    exact (canonical26187 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1808 + difference 1 2) (sourceB1808 + difference 2 1) sourceC1808) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 719) := by
    have ha : (tripleCharges (sourceA1808 + difference 1 2) (sourceB1808 + difference 2 1) sourceC1808) = raw26188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1808 sourceB1808 sourceC1808 difference raw26188; decide +kernel
    rw [ha]
    exact (canonical26188 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1808 + difference 1 3) (sourceB1808 + difference 3 1) sourceC1808) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA1808 + difference 1 3) (sourceB1808 + difference 3 1) sourceC1808) = raw26189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1808 sourceB1808 sourceC1808 difference raw26189; decide +kernel
    rw [ha]
    exact (canonical26189 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1808 + difference 1 4) (sourceB1808 + difference 4 1) sourceC1808) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA1808 + difference 1 4) (sourceB1808 + difference 4 1) sourceC1808) = raw26190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1808 sourceB1808 sourceC1808 difference raw26190; decide +kernel
    rw [ha]
    exact (canonical26190 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1808 + difference 1 5) (sourceB1808 + difference 5 1) sourceC1808) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 850) := by
    have ha : (tripleCharges (sourceA1808 + difference 1 5) (sourceB1808 + difference 5 1) sourceC1808) = raw26191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1808 sourceB1808 sourceC1808 difference raw26191; decide +kernel
    rw [ha]
    exact (canonical26191 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1808 + sourceB1808) sourceC1808) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1808 + sourceB1808) sourceC1808) = raw26192 := by
      apply Matrix.ext; unfold doubleCharges sourceA1808 sourceB1808 sourceC1808 raw26192; decide +kernel
    rw [ha]
    exact (canonical26192 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1808 sourceB1808 sourceC1808
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1808, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1809 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1809 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1809 : Charge := ![4, -1, -1, -1, -1, 0]
def sourceForm1809 : Integer.Sparse Master := [(Sum.inr 786, 1), (Sum.inr 1638, 2), (Sum.inr 1699, 2), (Sum.inr 1706, 1), (Sum.inr 4068, -1)]

theorem sourceEq1809 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1809 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1809 + difference 0 0) (sourceB1809 + difference 0 0) sourceC1809) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 786) := by
    have ha : (tripleCharges (sourceA1809 + difference 0 0) (sourceB1809 + difference 0 0) sourceC1809) = raw22061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1809 sourceB1809 sourceC1809 difference raw22061; decide +kernel
    rw [ha]
    exact (canonical22061 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1809 + difference 0 1) (sourceB1809 + difference 1 0) sourceC1809) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1638) := by
    have ha : (tripleCharges (sourceA1809 + difference 0 1) (sourceB1809 + difference 1 0) sourceC1809) = raw26193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1809 sourceB1809 sourceC1809 difference raw26193; decide +kernel
    rw [ha]
    exact (canonical26193 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1809 + difference 0 2) (sourceB1809 + difference 2 0) sourceC1809) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1638) := by
    have ha : (tripleCharges (sourceA1809 + difference 0 2) (sourceB1809 + difference 2 0) sourceC1809) = raw26194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1809 sourceB1809 sourceC1809 difference raw26194; decide +kernel
    rw [ha]
    exact (canonical26194 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1809 + difference 0 3) (sourceB1809 + difference 3 0) sourceC1809) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA1809 + difference 0 3) (sourceB1809 + difference 3 0) sourceC1809) = raw22058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1809 sourceB1809 sourceC1809 difference raw22058; decide +kernel
    rw [ha]
    exact (canonical22058 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1809 + difference 0 4) (sourceB1809 + difference 4 0) sourceC1809) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA1809 + difference 0 4) (sourceB1809 + difference 4 0) sourceC1809) = raw26195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1809 sourceB1809 sourceC1809 difference raw26195; decide +kernel
    rw [ha]
    exact (canonical26195 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1809 + difference 0 5) (sourceB1809 + difference 5 0) sourceC1809) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1809 + difference 0 5) (sourceB1809 + difference 5 0) sourceC1809) = raw26196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1809 sourceB1809 sourceC1809 difference raw26196; decide +kernel
    rw [ha]
    exact (canonical26196 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1809 + sourceB1809) sourceC1809) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1809 + sourceB1809) sourceC1809) = raw22064 := by
      apply Matrix.ext; unfold doubleCharges sourceA1809 sourceB1809 sourceC1809 raw22064; decide +kernel
    rw [ha]
    exact (canonical22064 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1809 sourceB1809 sourceC1809
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1809, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1810 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1810 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1810 : Charge := ![4, -1, -1, -1, -1, 0]
def sourceForm1810 : Integer.Sparse Master := [(Sum.inr 541, 1), (Sum.inr 736, 1), (Sum.inr 786, 3), (Sum.inr 805, 1), (Sum.inr 4068, -1)]

theorem sourceEq1810 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1810 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1810 + difference 1 0) (sourceB1810 + difference 0 1) sourceC1810) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 541) := by
    have ha : (tripleCharges (sourceA1810 + difference 1 0) (sourceB1810 + difference 0 1) sourceC1810) = raw26197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1810 sourceB1810 sourceC1810 difference raw26197; decide +kernel
    rw [ha]
    exact (canonical26197 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1810 + difference 1 1) (sourceB1810 + difference 1 1) sourceC1810) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 786) := by
    have ha : (tripleCharges (sourceA1810 + difference 1 1) (sourceB1810 + difference 1 1) sourceC1810) = raw22061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1810 sourceB1810 sourceC1810 difference raw22061; decide +kernel
    rw [ha]
    exact (canonical22061 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1810 + difference 1 2) (sourceB1810 + difference 2 1) sourceC1810) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 736) := by
    have ha : (tripleCharges (sourceA1810 + difference 1 2) (sourceB1810 + difference 2 1) sourceC1810) = raw26198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1810 sourceB1810 sourceC1810 difference raw26198; decide +kernel
    rw [ha]
    exact (canonical26198 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1810 + difference 1 3) (sourceB1810 + difference 3 1) sourceC1810) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 786) := by
    have ha : (tripleCharges (sourceA1810 + difference 1 3) (sourceB1810 + difference 3 1) sourceC1810) = raw22059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1810 sourceB1810 sourceC1810 difference raw22059; decide +kernel
    rw [ha]
    exact (canonical22059 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1810 + difference 1 4) (sourceB1810 + difference 4 1) sourceC1810) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 786) := by
    have ha : (tripleCharges (sourceA1810 + difference 1 4) (sourceB1810 + difference 4 1) sourceC1810) = raw26199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1810 sourceB1810 sourceC1810 difference raw26199; decide +kernel
    rw [ha]
    exact (canonical26199 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1810 + difference 1 5) (sourceB1810 + difference 5 1) sourceC1810) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 805) := by
    have ha : (tripleCharges (sourceA1810 + difference 1 5) (sourceB1810 + difference 5 1) sourceC1810) = raw26200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1810 sourceB1810 sourceC1810 difference raw26200; decide +kernel
    rw [ha]
    exact (canonical26200 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1810 + sourceB1810) sourceC1810) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1810 + sourceB1810) sourceC1810) = raw22064 := by
      apply Matrix.ext; unfold doubleCharges sourceA1810 sourceB1810 sourceC1810 raw22064; decide +kernel
    rw [ha]
    exact (canonical22064 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1810 sourceB1810 sourceC1810
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1810, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1811 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1811 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1811 : Charge := ![4, -1, -1, -1, -1, 0]
def sourceForm1811 : Integer.Sparse Master := [(Sum.inr 783, 2), (Sum.inr 786, 1), (Sum.inr 805, 2), (Sum.inr 1706, 1), (Sum.inr 4068, -1)]

theorem sourceEq1811 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1811 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1811 + difference 0 5) (sourceB1811 + difference 5 0) sourceC1811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1811 + difference 0 5) (sourceB1811 + difference 5 0) sourceC1811) = raw26196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1811 sourceB1811 sourceC1811 difference raw26196; decide +kernel
    rw [ha]
    exact (canonical26196 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1811 + difference 1 5) (sourceB1811 + difference 5 1) sourceC1811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 805) := by
    have ha : (tripleCharges (sourceA1811 + difference 1 5) (sourceB1811 + difference 5 1) sourceC1811) = raw26200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1811 sourceB1811 sourceC1811 difference raw26200; decide +kernel
    rw [ha]
    exact (canonical26200 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1811 + difference 2 5) (sourceB1811 + difference 5 2) sourceC1811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 805) := by
    have ha : (tripleCharges (sourceA1811 + difference 2 5) (sourceB1811 + difference 5 2) sourceC1811) = raw26201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1811 sourceB1811 sourceC1811 difference raw26201; decide +kernel
    rw [ha]
    exact (canonical26201 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1811 + difference 3 5) (sourceB1811 + difference 5 3) sourceC1811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1811 + difference 3 5) (sourceB1811 + difference 5 3) sourceC1811) = raw26202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1811 sourceB1811 sourceC1811 difference raw26202; decide +kernel
    rw [ha]
    exact (canonical26202 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1811 + difference 4 5) (sourceB1811 + difference 5 4) sourceC1811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1811 + difference 4 5) (sourceB1811 + difference 5 4) sourceC1811) = raw26203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1811 sourceB1811 sourceC1811 difference raw26203; decide +kernel
    rw [ha]
    exact (canonical26203 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1811 + difference 5 5) (sourceB1811 + difference 5 5) sourceC1811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 786) := by
    have ha : (tripleCharges (sourceA1811 + difference 5 5) (sourceB1811 + difference 5 5) sourceC1811) = raw22061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1811 sourceB1811 sourceC1811 difference raw22061; decide +kernel
    rw [ha]
    exact (canonical22061 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1811 + sourceB1811) sourceC1811) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1811 + sourceB1811) sourceC1811) = raw22064 := by
      apply Matrix.ext; unfold doubleCharges sourceA1811 sourceB1811 sourceC1811 raw22064; decide +kernel
    rw [ha]
    exact (canonical22064 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1811 sourceB1811 sourceC1811
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1811, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1812 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB1812 : Charge := ![4, -1, -1, -1, -1, 0]
def sourceC1812 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1812 : Integer.Sparse Master := [(Sum.inr 550, 1), (Sum.inr 803, 2), (Sum.inr 822, 1), (Sum.inr 850, 2), (Sum.inr 4069, -1)]

theorem sourceEq1812 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1812 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1812 + difference 5 0) (sourceB1812 + difference 0 5) sourceC1812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 550) := by
    have ha : (tripleCharges (sourceA1812 + difference 5 0) (sourceB1812 + difference 0 5) sourceC1812) = raw26204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1812 sourceB1812 sourceC1812 difference raw26204; decide +kernel
    rw [ha]
    exact (canonical26204 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1812 + difference 5 1) (sourceB1812 + difference 1 5) sourceC1812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 850) := by
    have ha : (tripleCharges (sourceA1812 + difference 5 1) (sourceB1812 + difference 1 5) sourceC1812) = raw26205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1812 sourceB1812 sourceC1812 difference raw26205; decide +kernel
    rw [ha]
    exact (canonical26205 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1812 + difference 5 2) (sourceB1812 + difference 2 5) sourceC1812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 850) := by
    have ha : (tripleCharges (sourceA1812 + difference 5 2) (sourceB1812 + difference 2 5) sourceC1812) = raw25543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1812 sourceB1812 sourceC1812 difference raw25543; decide +kernel
    rw [ha]
    exact (canonical25543 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1812 + difference 5 3) (sourceB1812 + difference 3 5) sourceC1812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 803) := by
    have ha : (tripleCharges (sourceA1812 + difference 5 3) (sourceB1812 + difference 3 5) sourceC1812) = raw23891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1812 sourceB1812 sourceC1812 difference raw23891; decide +kernel
    rw [ha]
    exact (canonical23891 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1812 + difference 5 4) (sourceB1812 + difference 4 5) sourceC1812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 803) := by
    have ha : (tripleCharges (sourceA1812 + difference 5 4) (sourceB1812 + difference 4 5) sourceC1812) = raw23890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1812 sourceB1812 sourceC1812 difference raw23890; decide +kernel
    rw [ha]
    exact (canonical23890 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1812 + difference 5 5) (sourceB1812 + difference 5 5) sourceC1812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 822) := by
    have ha : (tripleCharges (sourceA1812 + difference 5 5) (sourceB1812 + difference 5 5) sourceC1812) = raw23917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1812 sourceB1812 sourceC1812 difference raw23917; decide +kernel
    rw [ha]
    exact (canonical23917 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1812 + sourceB1812) sourceC1812) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1812 + sourceB1812) sourceC1812) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1812 sourceB1812 sourceC1812 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1812 sourceB1812 sourceC1812
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1812, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1813 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1813 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1813 : Charge := ![4, -1, -1, -1, 0, -1]
def sourceForm1813 : Integer.Sparse Master := [(Sum.inr 783, 1), (Sum.inr 1636, 2), (Sum.inr 1698, 1), (Sum.inr 1706, 1), (Sum.inr 1708, 1), (Sum.inr 4068, -1)]

theorem sourceEq1813 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1813 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1813 + difference 0 0) (sourceB1813 + difference 0 0) sourceC1813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1813 + difference 0 0) (sourceB1813 + difference 0 0) sourceC1813) = raw22068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1813 sourceB1813 sourceC1813 difference raw22068; decide +kernel
    rw [ha]
    exact (canonical22068 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1813 + difference 0 1) (sourceB1813 + difference 1 0) sourceC1813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1636) := by
    have ha : (tripleCharges (sourceA1813 + difference 0 1) (sourceB1813 + difference 1 0) sourceC1813) = raw26206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1813 sourceB1813 sourceC1813 difference raw26206; decide +kernel
    rw [ha]
    exact (canonical26206 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1813 + difference 0 2) (sourceB1813 + difference 2 0) sourceC1813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1636) := by
    have ha : (tripleCharges (sourceA1813 + difference 0 2) (sourceB1813 + difference 2 0) sourceC1813) = raw26207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1813 sourceB1813 sourceC1813 difference raw26207; decide +kernel
    rw [ha]
    exact (canonical26207 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1813 + difference 0 3) (sourceB1813 + difference 3 0) sourceC1813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA1813 + difference 0 3) (sourceB1813 + difference 3 0) sourceC1813) = raw22065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1813 sourceB1813 sourceC1813 difference raw22065; decide +kernel
    rw [ha]
    exact (canonical22065 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1813 + difference 0 4) (sourceB1813 + difference 4 0) sourceC1813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1813 + difference 0 4) (sourceB1813 + difference 4 0) sourceC1813) = raw26208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1813 sourceB1813 sourceC1813 difference raw26208; decide +kernel
    rw [ha]
    exact (canonical26208 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1813 + difference 0 5) (sourceB1813 + difference 5 0) sourceC1813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1813 + difference 0 5) (sourceB1813 + difference 5 0) sourceC1813) = raw26209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1813 sourceB1813 sourceC1813 difference raw26209; decide +kernel
    rw [ha]
    exact (canonical26209 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1813 + sourceB1813) sourceC1813) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1813 + sourceB1813) sourceC1813) = raw22071 := by
      apply Matrix.ext; unfold doubleCharges sourceA1813 sourceB1813 sourceC1813 raw22071; decide +kernel
    rw [ha]
    exact (canonical22071 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1813 sourceB1813 sourceC1813
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1813, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1814 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1814 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1814 : Charge := ![4, -1, -1, -1, 0, -1]
def sourceForm1814 : Integer.Sparse Master := [(Sum.inr 537, 1), (Sum.inr 732, 1), (Sum.inr 783, 2), (Sum.inr 805, 1), (Sum.inr 810, 1), (Sum.inr 4068, -1)]

theorem sourceEq1814 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1814 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1814 + difference 1 0) (sourceB1814 + difference 0 1) sourceC1814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 537) := by
    have ha : (tripleCharges (sourceA1814 + difference 1 0) (sourceB1814 + difference 0 1) sourceC1814) = raw26210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1814 sourceB1814 sourceC1814 difference raw26210; decide +kernel
    rw [ha]
    exact (canonical26210 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1814 + difference 1 1) (sourceB1814 + difference 1 1) sourceC1814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1814 + difference 1 1) (sourceB1814 + difference 1 1) sourceC1814) = raw22068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1814 sourceB1814 sourceC1814 difference raw22068; decide +kernel
    rw [ha]
    exact (canonical22068 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1814 + difference 1 2) (sourceB1814 + difference 2 1) sourceC1814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 732) := by
    have ha : (tripleCharges (sourceA1814 + difference 1 2) (sourceB1814 + difference 2 1) sourceC1814) = raw26211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1814 sourceB1814 sourceC1814 difference raw26211; decide +kernel
    rw [ha]
    exact (canonical26211 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1814 + difference 1 3) (sourceB1814 + difference 3 1) sourceC1814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1814 + difference 1 3) (sourceB1814 + difference 3 1) sourceC1814) = raw22066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1814 sourceB1814 sourceC1814 difference raw22066; decide +kernel
    rw [ha]
    exact (canonical22066 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1814 + difference 1 4) (sourceB1814 + difference 4 1) sourceC1814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1814 + difference 1 4) (sourceB1814 + difference 4 1) sourceC1814) = raw26212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1814 sourceB1814 sourceC1814 difference raw26212; decide +kernel
    rw [ha]
    exact (canonical26212 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1814 + difference 1 5) (sourceB1814 + difference 5 1) sourceC1814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 805) := by
    have ha : (tripleCharges (sourceA1814 + difference 1 5) (sourceB1814 + difference 5 1) sourceC1814) = raw26213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1814 sourceB1814 sourceC1814 difference raw26213; decide +kernel
    rw [ha]
    exact (canonical26213 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1814 + sourceB1814) sourceC1814) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1814 + sourceB1814) sourceC1814) = raw22071 := by
      apply Matrix.ext; unfold doubleCharges sourceA1814 sourceB1814 sourceC1814 raw22071; decide +kernel
    rw [ha]
    exact (canonical22071 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1814 sourceB1814 sourceC1814
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1814, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1815 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1815 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1815 : Charge := ![4, -1, 0, -1, -1, -1]
def sourceForm1815 : Integer.Sparse Master := [(Sum.inr 4068, 1), (Sum.inr 4100, 1), (Sum.inr 4105, 1), (Sum.inr 4107, 2), (Sum.inr 4125, 1), (Sum.inr 4199, 1), (Sum.inr 4201, 2), (Sum.inr 4216, 1), (Sum.inr 4232, 1), (Sum.inr 4237, 1), (Sum.inr 4239, 2), (Sum.inr 4249, 2), (Sum.inr 4253, 2), (Sum.inr 4256, 2), (Sum.inr 4263, 1), (Sum.inr 4267, 4), (Sum.inr 4417, 1), (Sum.inr 4489, 1), (Sum.inr 4495, 2), (Sum.inr 4497, 1)]

theorem sourceEq1815 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1815 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1815 + difference 0 1) (sourceB1815 + difference 1 0) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA1815 + difference 0 1) (sourceB1815 + difference 1 0) sourceC1815) = raw26214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26214; decide +kernel
    rw [ha]
    exact (canonical26214 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1815 + difference 0 2) (sourceB1815 + difference 2 0) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1815 + difference 0 2) (sourceB1815 + difference 2 0) sourceC1815) = raw26215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26215; decide +kernel
    rw [ha]
    exact (canonical26215 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1815 + difference 0 3) (sourceB1815 + difference 3 0) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1815 + difference 0 3) (sourceB1815 + difference 3 0) sourceC1815) = raw26216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26216; decide +kernel
    rw [ha]
    exact (canonical26216 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1815 + difference 0 4) (sourceB1815 + difference 4 0) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1815 + difference 0 4) (sourceB1815 + difference 4 0) sourceC1815) = raw26217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26217; decide +kernel
    rw [ha]
    exact (canonical26217 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1815 + difference 0 5) (sourceB1815 + difference 5 0) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1815 + difference 0 5) (sourceB1815 + difference 5 0) sourceC1815) = raw26218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26218; decide +kernel
    rw [ha]
    exact (canonical26218 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1815 + difference 1 0) (sourceB1815 + difference 0 1) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4125) := by
    have ha : (tripleCharges (sourceA1815 + difference 1 0) (sourceB1815 + difference 0 1) sourceC1815) = raw26219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26219; decide +kernel
    rw [ha]
    exact (canonical26219 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1815 + difference 1 2) (sourceB1815 + difference 2 1) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4216) := by
    have ha : (tripleCharges (sourceA1815 + difference 1 2) (sourceB1815 + difference 2 1) sourceC1815) = raw26220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26220; decide +kernel
    rw [ha]
    exact (canonical26220 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1815 + difference 1 3) (sourceB1815 + difference 3 1) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1815 + difference 1 3) (sourceB1815 + difference 3 1) sourceC1815) = raw26221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26221; decide +kernel
    rw [ha]
    exact (canonical26221 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1815 + difference 1 4) (sourceB1815 + difference 4 1) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1815 + difference 1 4) (sourceB1815 + difference 4 1) sourceC1815) = raw26222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26222; decide +kernel
    rw [ha]
    exact (canonical26222 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1815 + difference 1 5) (sourceB1815 + difference 5 1) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1815 + difference 1 5) (sourceB1815 + difference 5 1) sourceC1815) = raw26223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26223; decide +kernel
    rw [ha]
    exact (canonical26223 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1815 + difference 2 0) (sourceB1815 + difference 0 2) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4100) := by
    have ha : (tripleCharges (sourceA1815 + difference 2 0) (sourceB1815 + difference 0 2) sourceC1815) = raw26224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26224; decide +kernel
    rw [ha]
    exact (canonical26224 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1815 + difference 2 1) (sourceB1815 + difference 1 2) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4232) := by
    have ha : (tripleCharges (sourceA1815 + difference 2 1) (sourceB1815 + difference 1 2) sourceC1815) = raw26225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26225; decide +kernel
    rw [ha]
    exact (canonical26225 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1815 + difference 2 3) (sourceB1815 + difference 3 2) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1815 + difference 2 3) (sourceB1815 + difference 3 2) sourceC1815) = raw26226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26226; decide +kernel
    rw [ha]
    exact (canonical26226 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1815 + difference 2 4) (sourceB1815 + difference 4 2) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1815 + difference 2 4) (sourceB1815 + difference 4 2) sourceC1815) = raw26227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26227; decide +kernel
    rw [ha]
    exact (canonical26227 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1815 + difference 2 5) (sourceB1815 + difference 5 2) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4263) := by
    have ha : (tripleCharges (sourceA1815 + difference 2 5) (sourceB1815 + difference 5 2) sourceC1815) = raw26228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26228; decide +kernel
    rw [ha]
    exact (canonical26228 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1815 + difference 3 0) (sourceB1815 + difference 0 3) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4107) := by
    have ha : (tripleCharges (sourceA1815 + difference 3 0) (sourceB1815 + difference 0 3) sourceC1815) = raw26229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26229; decide +kernel
    rw [ha]
    exact (canonical26229 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1815 + difference 3 1) (sourceB1815 + difference 1 3) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4239) := by
    have ha : (tripleCharges (sourceA1815 + difference 3 1) (sourceB1815 + difference 1 3) sourceC1815) = raw26230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26230; decide +kernel
    rw [ha]
    exact (canonical26230 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1815 + difference 3 2) (sourceB1815 + difference 2 3) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4201) := by
    have ha : (tripleCharges (sourceA1815 + difference 3 2) (sourceB1815 + difference 2 3) sourceC1815) = raw26231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26231; decide +kernel
    rw [ha]
    exact (canonical26231 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1815 + difference 3 4) (sourceB1815 + difference 4 3) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4256) := by
    have ha : (tripleCharges (sourceA1815 + difference 3 4) (sourceB1815 + difference 4 3) sourceC1815) = raw26232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26232; decide +kernel
    rw [ha]
    exact (canonical26232 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1815 + difference 3 5) (sourceB1815 + difference 5 3) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1815 + difference 3 5) (sourceB1815 + difference 5 3) sourceC1815) = raw26233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26233; decide +kernel
    rw [ha]
    exact (canonical26233 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1815 + difference 4 0) (sourceB1815 + difference 0 4) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4107) := by
    have ha : (tripleCharges (sourceA1815 + difference 4 0) (sourceB1815 + difference 0 4) sourceC1815) = raw26234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26234; decide +kernel
    rw [ha]
    exact (canonical26234 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1815 + difference 4 1) (sourceB1815 + difference 1 4) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4239) := by
    have ha : (tripleCharges (sourceA1815 + difference 4 1) (sourceB1815 + difference 1 4) sourceC1815) = raw26235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26235; decide +kernel
    rw [ha]
    exact (canonical26235 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1815 + difference 4 2) (sourceB1815 + difference 2 4) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4201) := by
    have ha : (tripleCharges (sourceA1815 + difference 4 2) (sourceB1815 + difference 2 4) sourceC1815) = raw26236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26236; decide +kernel
    rw [ha]
    exact (canonical26236 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1815 + difference 4 3) (sourceB1815 + difference 3 4) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4256) := by
    have ha : (tripleCharges (sourceA1815 + difference 4 3) (sourceB1815 + difference 3 4) sourceC1815) = raw26237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26237; decide +kernel
    rw [ha]
    exact (canonical26237 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1815 + difference 4 5) (sourceB1815 + difference 5 4) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1815 + difference 4 5) (sourceB1815 + difference 5 4) sourceC1815) = raw26238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26238; decide +kernel
    rw [ha]
    exact (canonical26238 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1815 + difference 5 0) (sourceB1815 + difference 0 5) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4105) := by
    have ha : (tripleCharges (sourceA1815 + difference 5 0) (sourceB1815 + difference 0 5) sourceC1815) = raw26239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26239; decide +kernel
    rw [ha]
    exact (canonical26239 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1815 + difference 5 1) (sourceB1815 + difference 1 5) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4237) := by
    have ha : (tripleCharges (sourceA1815 + difference 5 1) (sourceB1815 + difference 1 5) sourceC1815) = raw26240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26240; decide +kernel
    rw [ha]
    exact (canonical26240 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1815 + difference 5 2) (sourceB1815 + difference 2 5) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4199) := by
    have ha : (tripleCharges (sourceA1815 + difference 5 2) (sourceB1815 + difference 2 5) sourceC1815) = raw26241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26241; decide +kernel
    rw [ha]
    exact (canonical26241 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1815 + difference 5 3) (sourceB1815 + difference 3 5) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4253) := by
    have ha : (tripleCharges (sourceA1815 + difference 5 3) (sourceB1815 + difference 3 5) sourceC1815) = raw26242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26242; decide +kernel
    rw [ha]
    exact (canonical26242 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1815 + difference 5 4) (sourceB1815 + difference 4 5) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4253) := by
    have ha : (tripleCharges (sourceA1815 + difference 5 4) (sourceB1815 + difference 4 5) sourceC1815) = raw26243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26243; decide +kernel
    rw [ha]
    exact (canonical26243 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1815 sourceB1815 sourceC1815
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1815, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1816 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1816 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1816 : Charge := ![4, -1, 0, -1, -1, -1]
def sourceForm1816 : Integer.Sparse Master := [(Sum.inr 662, 1), (Sum.inr 681, 1), (Sum.inr 682, 2), (Sum.inr 687, 1), (Sum.inr 760, 1), (Sum.inr 761, 2), (Sum.inr 766, 1), (Sum.inr 798, 1), (Sum.inr 803, 2), (Sum.inr 805, 1), (Sum.inr 840, 1), (Sum.inr 841, 2), (Sum.inr 847, 2), (Sum.inr 848, 2), (Sum.inr 850, 4), (Sum.inr 998, 1), (Sum.inr 1073, 1), (Sum.inr 1079, 2), (Sum.inr 1081, 1), (Sum.inr 4068, 1)]

theorem sourceEq1816 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1816 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1816 + difference 0 1) (sourceB1816 + difference 1 0) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1816 + difference 0 1) (sourceB1816 + difference 1 0) sourceC1816) = raw26244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26244; decide +kernel
    rw [ha]
    exact (canonical26244 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1816 + difference 0 2) (sourceB1816 + difference 2 0) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 998) := by
    have ha : (tripleCharges (sourceA1816 + difference 0 2) (sourceB1816 + difference 2 0) sourceC1816) = raw26245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26245; decide +kernel
    rw [ha]
    exact (canonical26245 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1816 + difference 0 3) (sourceB1816 + difference 3 0) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1816 + difference 0 3) (sourceB1816 + difference 3 0) sourceC1816) = raw26246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26246; decide +kernel
    rw [ha]
    exact (canonical26246 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1816 + difference 0 4) (sourceB1816 + difference 4 0) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1816 + difference 0 4) (sourceB1816 + difference 4 0) sourceC1816) = raw26247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26247; decide +kernel
    rw [ha]
    exact (canonical26247 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1816 + difference 0 5) (sourceB1816 + difference 5 0) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1081) := by
    have ha : (tripleCharges (sourceA1816 + difference 0 5) (sourceB1816 + difference 5 0) sourceC1816) = raw26248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26248; decide +kernel
    rw [ha]
    exact (canonical26248 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1816 + difference 1 0) (sourceB1816 + difference 0 1) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 687) := by
    have ha : (tripleCharges (sourceA1816 + difference 1 0) (sourceB1816 + difference 0 1) sourceC1816) = raw26249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26249; decide +kernel
    rw [ha]
    exact (canonical26249 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1816 + difference 1 2) (sourceB1816 + difference 2 1) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 766) := by
    have ha : (tripleCharges (sourceA1816 + difference 1 2) (sourceB1816 + difference 2 1) sourceC1816) = raw26250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26250; decide +kernel
    rw [ha]
    exact (canonical26250 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1816 + difference 1 3) (sourceB1816 + difference 3 1) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 850) := by
    have ha : (tripleCharges (sourceA1816 + difference 1 3) (sourceB1816 + difference 3 1) sourceC1816) = raw26251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26251; decide +kernel
    rw [ha]
    exact (canonical26251 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1816 + difference 1 4) (sourceB1816 + difference 4 1) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 850) := by
    have ha : (tripleCharges (sourceA1816 + difference 1 4) (sourceB1816 + difference 4 1) sourceC1816) = raw26252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26252; decide +kernel
    rw [ha]
    exact (canonical26252 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1816 + difference 1 5) (sourceB1816 + difference 5 1) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1816 + difference 1 5) (sourceB1816 + difference 5 1) sourceC1816) = raw26253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26253; decide +kernel
    rw [ha]
    exact (canonical26253 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1816 + difference 2 0) (sourceB1816 + difference 0 2) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 662) := by
    have ha : (tripleCharges (sourceA1816 + difference 2 0) (sourceB1816 + difference 0 2) sourceC1816) = raw26254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26254; decide +kernel
    rw [ha]
    exact (canonical26254 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1816 + difference 2 1) (sourceB1816 + difference 1 2) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 798) := by
    have ha : (tripleCharges (sourceA1816 + difference 2 1) (sourceB1816 + difference 1 2) sourceC1816) = raw26255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26255; decide +kernel
    rw [ha]
    exact (canonical26255 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1816 + difference 2 3) (sourceB1816 + difference 3 2) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 803) := by
    have ha : (tripleCharges (sourceA1816 + difference 2 3) (sourceB1816 + difference 3 2) sourceC1816) = raw26256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26256; decide +kernel
    rw [ha]
    exact (canonical26256 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1816 + difference 2 4) (sourceB1816 + difference 4 2) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 803) := by
    have ha : (tripleCharges (sourceA1816 + difference 2 4) (sourceB1816 + difference 4 2) sourceC1816) = raw26257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26257; decide +kernel
    rw [ha]
    exact (canonical26257 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1816 + difference 2 5) (sourceB1816 + difference 5 2) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 805) := by
    have ha : (tripleCharges (sourceA1816 + difference 2 5) (sourceB1816 + difference 5 2) sourceC1816) = raw26258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26258; decide +kernel
    rw [ha]
    exact (canonical26258 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1816 + difference 3 0) (sourceB1816 + difference 0 3) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 682) := by
    have ha : (tripleCharges (sourceA1816 + difference 3 0) (sourceB1816 + difference 0 3) sourceC1816) = raw26259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26259; decide +kernel
    rw [ha]
    exact (canonical26259 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1816 + difference 3 1) (sourceB1816 + difference 1 3) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 841) := by
    have ha : (tripleCharges (sourceA1816 + difference 3 1) (sourceB1816 + difference 1 3) sourceC1816) = raw26260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26260; decide +kernel
    rw [ha]
    exact (canonical26260 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1816 + difference 3 2) (sourceB1816 + difference 2 3) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 761) := by
    have ha : (tripleCharges (sourceA1816 + difference 3 2) (sourceB1816 + difference 2 3) sourceC1816) = raw26261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26261; decide +kernel
    rw [ha]
    exact (canonical26261 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1816 + difference 3 4) (sourceB1816 + difference 4 3) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 848) := by
    have ha : (tripleCharges (sourceA1816 + difference 3 4) (sourceB1816 + difference 4 3) sourceC1816) = raw26262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26262; decide +kernel
    rw [ha]
    exact (canonical26262 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1816 + difference 3 5) (sourceB1816 + difference 5 3) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 850) := by
    have ha : (tripleCharges (sourceA1816 + difference 3 5) (sourceB1816 + difference 5 3) sourceC1816) = raw26263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26263; decide +kernel
    rw [ha]
    exact (canonical26263 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1816 + difference 4 0) (sourceB1816 + difference 0 4) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 682) := by
    have ha : (tripleCharges (sourceA1816 + difference 4 0) (sourceB1816 + difference 0 4) sourceC1816) = raw26264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26264; decide +kernel
    rw [ha]
    exact (canonical26264 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1816 + difference 4 1) (sourceB1816 + difference 1 4) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 841) := by
    have ha : (tripleCharges (sourceA1816 + difference 4 1) (sourceB1816 + difference 1 4) sourceC1816) = raw26265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26265; decide +kernel
    rw [ha]
    exact (canonical26265 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1816 + difference 4 2) (sourceB1816 + difference 2 4) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 761) := by
    have ha : (tripleCharges (sourceA1816 + difference 4 2) (sourceB1816 + difference 2 4) sourceC1816) = raw26266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26266; decide +kernel
    rw [ha]
    exact (canonical26266 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1816 + difference 4 3) (sourceB1816 + difference 3 4) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 848) := by
    have ha : (tripleCharges (sourceA1816 + difference 4 3) (sourceB1816 + difference 3 4) sourceC1816) = raw26267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26267; decide +kernel
    rw [ha]
    exact (canonical26267 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1816 + difference 4 5) (sourceB1816 + difference 5 4) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 850) := by
    have ha : (tripleCharges (sourceA1816 + difference 4 5) (sourceB1816 + difference 5 4) sourceC1816) = raw26268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26268; decide +kernel
    rw [ha]
    exact (canonical26268 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1816 + difference 5 0) (sourceB1816 + difference 0 5) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 681) := by
    have ha : (tripleCharges (sourceA1816 + difference 5 0) (sourceB1816 + difference 0 5) sourceC1816) = raw26269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26269; decide +kernel
    rw [ha]
    exact (canonical26269 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1816 + difference 5 1) (sourceB1816 + difference 1 5) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 840) := by
    have ha : (tripleCharges (sourceA1816 + difference 5 1) (sourceB1816 + difference 1 5) sourceC1816) = raw26270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26270; decide +kernel
    rw [ha]
    exact (canonical26270 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1816 + difference 5 2) (sourceB1816 + difference 2 5) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 760) := by
    have ha : (tripleCharges (sourceA1816 + difference 5 2) (sourceB1816 + difference 2 5) sourceC1816) = raw26271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26271; decide +kernel
    rw [ha]
    exact (canonical26271 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1816 + difference 5 3) (sourceB1816 + difference 3 5) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 847) := by
    have ha : (tripleCharges (sourceA1816 + difference 5 3) (sourceB1816 + difference 3 5) sourceC1816) = raw26272 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26272; decide +kernel
    rw [ha]
    exact (canonical26272 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1816 + difference 5 4) (sourceB1816 + difference 4 5) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 847) := by
    have ha : (tripleCharges (sourceA1816 + difference 5 4) (sourceB1816 + difference 4 5) sourceC1816) = raw26273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26273; decide +kernel
    rw [ha]
    exact (canonical26273 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1816 sourceB1816 sourceC1816
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1816, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1817 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1817 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1817 : Charge := ![4, -1, 0, -1, -1, -1]
def sourceForm1817 : Integer.Sparse Master := [(Sum.inr 732, 1), (Sum.inr 737, 1), (Sum.inr 739, 2), (Sum.inr 810, 1), (Sum.inr 1648, 1), (Sum.inr 4068, -1)]

theorem sourceEq1817 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1817 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1817 + difference 0 1) (sourceB1817 + difference 1 0) sourceC1817) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1648) := by
    have ha : (tripleCharges (sourceA1817 + difference 0 1) (sourceB1817 + difference 1 0) sourceC1817) = raw26274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1817 sourceB1817 sourceC1817 difference raw26274; decide +kernel
    rw [ha]
    exact (canonical26274 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1817 + difference 1 1) (sourceB1817 + difference 1 1) sourceC1817) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1817 + difference 1 1) (sourceB1817 + difference 1 1) sourceC1817) = raw26275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1817 sourceB1817 sourceC1817 difference raw26275; decide +kernel
    rw [ha]
    exact (canonical26275 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1817 + difference 2 1) (sourceB1817 + difference 1 2) sourceC1817) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 732) := by
    have ha : (tripleCharges (sourceA1817 + difference 2 1) (sourceB1817 + difference 1 2) sourceC1817) = raw26276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1817 sourceB1817 sourceC1817 difference raw26276; decide +kernel
    rw [ha]
    exact (canonical26276 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1817 + difference 3 1) (sourceB1817 + difference 1 3) sourceC1817) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 739) := by
    have ha : (tripleCharges (sourceA1817 + difference 3 1) (sourceB1817 + difference 1 3) sourceC1817) = raw26277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1817 sourceB1817 sourceC1817 difference raw26277; decide +kernel
    rw [ha]
    exact (canonical26277 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1817 + difference 4 1) (sourceB1817 + difference 1 4) sourceC1817) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 739) := by
    have ha : (tripleCharges (sourceA1817 + difference 4 1) (sourceB1817 + difference 1 4) sourceC1817) = raw26278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1817 sourceB1817 sourceC1817 difference raw26278; decide +kernel
    rw [ha]
    exact (canonical26278 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1817 + difference 5 1) (sourceB1817 + difference 1 5) sourceC1817) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 737) := by
    have ha : (tripleCharges (sourceA1817 + difference 5 1) (sourceB1817 + difference 1 5) sourceC1817) = raw26279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1817 sourceB1817 sourceC1817 difference raw26279; decide +kernel
    rw [ha]
    exact (canonical26279 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1817 + sourceB1817) sourceC1817) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1817 + sourceB1817) sourceC1817) = raw26280 := by
      apply Matrix.ext; unfold doubleCharges sourceA1817 sourceB1817 sourceC1817 raw26280; decide +kernel
    rw [ha]
    exact (canonical26280 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1817 sourceB1817 sourceC1817
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1817, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1818 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceB1818 : Charge := ![4, -1, 0, -1, -1, -1]
def sourceC1818 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1818 : Integer.Sparse Master := [(Sum.inr 4069, 1), (Sum.inr 4113, 1), (Sum.inr 4118, 1), (Sum.inr 4119, 2), (Sum.inr 4126, 1), (Sum.inr 4209, 1), (Sum.inr 4210, 2), (Sum.inr 4217, 1), (Sum.inr 4249, 2), (Sum.inr 4252, 1), (Sum.inr 4264, 2), (Sum.inr 4265, 2), (Sum.inr 4267, 1), (Sum.inr 4268, 4), (Sum.inr 4275, 1), (Sum.inr 4283, 2), (Sum.inr 4399, 1), (Sum.inr 4458, 2), (Sum.inr 4461, 1), (Sum.inr 4502, 1)]

theorem sourceEq1818 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1818 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1818 + difference 0 1) (sourceB1818 + difference 1 0) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1818 + difference 0 1) (sourceB1818 + difference 1 0) sourceC1818) = raw24260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw24260; decide +kernel
    rw [ha]
    exact (canonical24260 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1818 + difference 0 2) (sourceB1818 + difference 2 0) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1818 + difference 0 2) (sourceB1818 + difference 2 0) sourceC1818) = raw24605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw24605; decide +kernel
    rw [ha]
    exact (canonical24605 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1818 + difference 0 3) (sourceB1818 + difference 3 0) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1818 + difference 0 3) (sourceB1818 + difference 3 0) sourceC1818) = raw24252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw24252; decide +kernel
    rw [ha]
    exact (canonical24252 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1818 + difference 0 4) (sourceB1818 + difference 4 0) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1818 + difference 0 4) (sourceB1818 + difference 4 0) sourceC1818) = raw25108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25108; decide +kernel
    rw [ha]
    exact (canonical25108 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1818 + difference 0 5) (sourceB1818 + difference 5 0) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1818 + difference 0 5) (sourceB1818 + difference 5 0) sourceC1818) = raw25285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25285; decide +kernel
    rw [ha]
    exact (canonical25285 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1818 + difference 1 0) (sourceB1818 + difference 0 1) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4126) := by
    have ha : (tripleCharges (sourceA1818 + difference 1 0) (sourceB1818 + difference 0 1) sourceC1818) = raw26281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26281; decide +kernel
    rw [ha]
    exact (canonical26281 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1818 + difference 1 2) (sourceB1818 + difference 2 1) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4217) := by
    have ha : (tripleCharges (sourceA1818 + difference 1 2) (sourceB1818 + difference 2 1) sourceC1818) = raw26282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26282; decide +kernel
    rw [ha]
    exact (canonical26282 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1818 + difference 1 3) (sourceB1818 + difference 3 1) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1818 + difference 1 3) (sourceB1818 + difference 3 1) sourceC1818) = raw26283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26283; decide +kernel
    rw [ha]
    exact (canonical26283 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1818 + difference 1 4) (sourceB1818 + difference 4 1) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1818 + difference 1 4) (sourceB1818 + difference 4 1) sourceC1818) = raw25273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25273; decide +kernel
    rw [ha]
    exact (canonical25273 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1818 + difference 1 5) (sourceB1818 + difference 5 1) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4275) := by
    have ha : (tripleCharges (sourceA1818 + difference 1 5) (sourceB1818 + difference 5 1) sourceC1818) = raw25089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25089; decide +kernel
    rw [ha]
    exact (canonical25089 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1818 + difference 2 0) (sourceB1818 + difference 0 2) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4113) := by
    have ha : (tripleCharges (sourceA1818 + difference 2 0) (sourceB1818 + difference 0 2) sourceC1818) = raw26284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26284; decide +kernel
    rw [ha]
    exact (canonical26284 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1818 + difference 2 1) (sourceB1818 + difference 1 2) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1818 + difference 2 1) (sourceB1818 + difference 1 2) sourceC1818) = raw26285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26285; decide +kernel
    rw [ha]
    exact (canonical26285 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1818 + difference 2 3) (sourceB1818 + difference 3 2) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1818 + difference 2 3) (sourceB1818 + difference 3 2) sourceC1818) = raw26286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26286; decide +kernel
    rw [ha]
    exact (canonical26286 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1818 + difference 2 4) (sourceB1818 + difference 4 2) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1818 + difference 2 4) (sourceB1818 + difference 4 2) sourceC1818) = raw25277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25277; decide +kernel
    rw [ha]
    exact (canonical25277 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1818 + difference 2 5) (sourceB1818 + difference 5 2) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4252) := by
    have ha : (tripleCharges (sourceA1818 + difference 2 5) (sourceB1818 + difference 5 2) sourceC1818) = raw25094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25094; decide +kernel
    rw [ha]
    exact (canonical25094 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1818 + difference 3 0) (sourceB1818 + difference 0 3) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4119) := by
    have ha : (tripleCharges (sourceA1818 + difference 3 0) (sourceB1818 + difference 0 3) sourceC1818) = raw26287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26287; decide +kernel
    rw [ha]
    exact (canonical26287 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1818 + difference 3 1) (sourceB1818 + difference 1 3) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4283) := by
    have ha : (tripleCharges (sourceA1818 + difference 3 1) (sourceB1818 + difference 1 3) sourceC1818) = raw25713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25713; decide +kernel
    rw [ha]
    exact (canonical25713 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1818 + difference 3 2) (sourceB1818 + difference 2 3) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4210) := by
    have ha : (tripleCharges (sourceA1818 + difference 3 2) (sourceB1818 + difference 2 3) sourceC1818) = raw26288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26288; decide +kernel
    rw [ha]
    exact (canonical26288 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1818 + difference 3 4) (sourceB1818 + difference 4 3) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA1818 + difference 3 4) (sourceB1818 + difference 4 3) sourceC1818) = raw25281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25281; decide +kernel
    rw [ha]
    exact (canonical25281 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1818 + difference 3 5) (sourceB1818 + difference 5 3) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1818 + difference 3 5) (sourceB1818 + difference 5 3) sourceC1818) = raw25099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25099; decide +kernel
    rw [ha]
    exact (canonical25099 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1818 + difference 4 0) (sourceB1818 + difference 0 4) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4119) := by
    have ha : (tripleCharges (sourceA1818 + difference 4 0) (sourceB1818 + difference 0 4) sourceC1818) = raw26289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26289; decide +kernel
    rw [ha]
    exact (canonical26289 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1818 + difference 4 1) (sourceB1818 + difference 1 4) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4283) := by
    have ha : (tripleCharges (sourceA1818 + difference 4 1) (sourceB1818 + difference 1 4) sourceC1818) = raw26290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26290; decide +kernel
    rw [ha]
    exact (canonical26290 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1818 + difference 4 2) (sourceB1818 + difference 2 4) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4210) := by
    have ha : (tripleCharges (sourceA1818 + difference 4 2) (sourceB1818 + difference 2 4) sourceC1818) = raw26291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26291; decide +kernel
    rw [ha]
    exact (canonical26291 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1818 + difference 4 3) (sourceB1818 + difference 3 4) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA1818 + difference 4 3) (sourceB1818 + difference 3 4) sourceC1818) = raw26292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26292; decide +kernel
    rw [ha]
    exact (canonical26292 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1818 + difference 4 5) (sourceB1818 + difference 5 4) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1818 + difference 4 5) (sourceB1818 + difference 5 4) sourceC1818) = raw25104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25104; decide +kernel
    rw [ha]
    exact (canonical25104 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1818 + difference 5 0) (sourceB1818 + difference 0 5) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4118) := by
    have ha : (tripleCharges (sourceA1818 + difference 5 0) (sourceB1818 + difference 0 5) sourceC1818) = raw26293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26293; decide +kernel
    rw [ha]
    exact (canonical26293 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1818 + difference 5 1) (sourceB1818 + difference 1 5) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1818 + difference 5 1) (sourceB1818 + difference 1 5) sourceC1818) = raw26167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26167; decide +kernel
    rw [ha]
    exact (canonical26167 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1818 + difference 5 2) (sourceB1818 + difference 2 5) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4209) := by
    have ha : (tripleCharges (sourceA1818 + difference 5 2) (sourceB1818 + difference 2 5) sourceC1818) = raw26165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26165; decide +kernel
    rw [ha]
    exact (canonical26165 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1818 + difference 5 3) (sourceB1818 + difference 3 5) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1818 + difference 5 3) (sourceB1818 + difference 3 5) sourceC1818) = raw25478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25478; decide +kernel
    rw [ha]
    exact (canonical25478 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1818 + difference 5 4) (sourceB1818 + difference 4 5) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1818 + difference 5 4) (sourceB1818 + difference 4 5) sourceC1818) = raw25286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25286; decide +kernel
    rw [ha]
    exact (canonical25286 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1818 sourceB1818 sourceC1818
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1818, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1819 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1819 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC1819 : Charge := ![4, -1, 0, -1, 0, -2]
def sourceForm1819 : Integer.Sparse Master := [(Sum.inr 4069, 1), (Sum.inr 4098, 1), (Sum.inr 4101, 1), (Sum.inr 4102, 1), (Sum.inr 4106, 1), (Sum.inr 4118, 1), (Sum.inr 4196, 1), (Sum.inr 4197, 1), (Sum.inr 4200, 1), (Sum.inr 4209, 1), (Sum.inr 4230, 1), (Sum.inr 4233, 1), (Sum.inr 4234, 1), (Sum.inr 4238, 1), (Sum.inr 4248, 1), (Sum.inr 4249, 1), (Sum.inr 4251, 1), (Sum.inr 4255, 1), (Sum.inr 4264, 2), (Sum.inr 4265, 1), (Sum.inr 4267, 1), (Sum.inr 4268, 1), (Sum.inr 4269, 1), (Sum.inr 4273, 1), (Sum.inr 4396, 1), (Sum.inr 4452, 1), (Sum.inr 4457, 1), (Sum.inr 4458, 1), (Sum.inr 4498, 1)]

theorem sourceEq1819 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1819 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1819 + difference 0 1) (sourceB1819 + difference 1 0) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1819 + difference 0 1) (sourceB1819 + difference 1 0) sourceC1819) = raw26294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26294; decide +kernel
    rw [ha]
    exact (canonical26294 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1819 + difference 0 2) (sourceB1819 + difference 2 0) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1819 + difference 0 2) (sourceB1819 + difference 2 0) sourceC1819) = raw26295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26295; decide +kernel
    rw [ha]
    exact (canonical26295 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1819 + difference 0 3) (sourceB1819 + difference 3 0) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1819 + difference 0 3) (sourceB1819 + difference 3 0) sourceC1819) = raw26296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26296; decide +kernel
    rw [ha]
    exact (canonical26296 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1819 + difference 0 4) (sourceB1819 + difference 4 0) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1819 + difference 0 4) (sourceB1819 + difference 4 0) sourceC1819) = raw26297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26297; decide +kernel
    rw [ha]
    exact (canonical26297 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1819 + difference 0 5) (sourceB1819 + difference 5 0) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1819 + difference 0 5) (sourceB1819 + difference 5 0) sourceC1819) = raw26298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26298; decide +kernel
    rw [ha]
    exact (canonical26298 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1819 + difference 1 0) (sourceB1819 + difference 0 1) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4118) := by
    have ha : (tripleCharges (sourceA1819 + difference 1 0) (sourceB1819 + difference 0 1) sourceC1819) = raw26299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26299; decide +kernel
    rw [ha]
    exact (canonical26299 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1819 + difference 1 2) (sourceB1819 + difference 2 1) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4209) := by
    have ha : (tripleCharges (sourceA1819 + difference 1 2) (sourceB1819 + difference 2 1) sourceC1819) = raw26300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26300; decide +kernel
    rw [ha]
    exact (canonical26300 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1819 + difference 1 3) (sourceB1819 + difference 3 1) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1819 + difference 1 3) (sourceB1819 + difference 3 1) sourceC1819) = raw26301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26301; decide +kernel
    rw [ha]
    exact (canonical26301 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1819 + difference 1 4) (sourceB1819 + difference 4 1) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1819 + difference 1 4) (sourceB1819 + difference 4 1) sourceC1819) = raw26302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26302; decide +kernel
    rw [ha]
    exact (canonical26302 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1819 + difference 1 5) (sourceB1819 + difference 5 1) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1819 + difference 1 5) (sourceB1819 + difference 5 1) sourceC1819) = raw26303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26303; decide +kernel
    rw [ha]
    exact (canonical26303 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1819 + difference 2 0) (sourceB1819 + difference 0 2) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4098) := by
    have ha : (tripleCharges (sourceA1819 + difference 2 0) (sourceB1819 + difference 0 2) sourceC1819) = raw26304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26304; decide +kernel
    rw [ha]
    exact (canonical26304 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1819 + difference 2 1) (sourceB1819 + difference 1 2) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4230) := by
    have ha : (tripleCharges (sourceA1819 + difference 2 1) (sourceB1819 + difference 1 2) sourceC1819) = raw26305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26305; decide +kernel
    rw [ha]
    exact (canonical26305 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1819 + difference 2 3) (sourceB1819 + difference 3 2) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4248) := by
    have ha : (tripleCharges (sourceA1819 + difference 2 3) (sourceB1819 + difference 3 2) sourceC1819) = raw26306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26306; decide +kernel
    rw [ha]
    exact (canonical26306 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1819 + difference 2 4) (sourceB1819 + difference 4 2) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1819 + difference 2 4) (sourceB1819 + difference 4 2) sourceC1819) = raw26307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26307; decide +kernel
    rw [ha]
    exact (canonical26307 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1819 + difference 2 5) (sourceB1819 + difference 5 2) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1819 + difference 2 5) (sourceB1819 + difference 5 2) sourceC1819) = raw26308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26308; decide +kernel
    rw [ha]
    exact (canonical26308 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1819 + difference 3 0) (sourceB1819 + difference 0 3) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4102) := by
    have ha : (tripleCharges (sourceA1819 + difference 3 0) (sourceB1819 + difference 0 3) sourceC1819) = raw26309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26309; decide +kernel
    rw [ha]
    exact (canonical26309 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1819 + difference 3 1) (sourceB1819 + difference 1 3) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4234) := by
    have ha : (tripleCharges (sourceA1819 + difference 3 1) (sourceB1819 + difference 1 3) sourceC1819) = raw26310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26310; decide +kernel
    rw [ha]
    exact (canonical26310 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1819 + difference 3 2) (sourceB1819 + difference 2 3) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4197) := by
    have ha : (tripleCharges (sourceA1819 + difference 3 2) (sourceB1819 + difference 2 3) sourceC1819) = raw26311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26311; decide +kernel
    rw [ha]
    exact (canonical26311 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1819 + difference 3 4) (sourceB1819 + difference 4 3) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1819 + difference 3 4) (sourceB1819 + difference 4 3) sourceC1819) = raw26312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26312; decide +kernel
    rw [ha]
    exact (canonical26312 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1819 + difference 3 5) (sourceB1819 + difference 5 3) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA1819 + difference 3 5) (sourceB1819 + difference 5 3) sourceC1819) = raw26313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26313; decide +kernel
    rw [ha]
    exact (canonical26313 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1819 + difference 4 0) (sourceB1819 + difference 0 4) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4106) := by
    have ha : (tripleCharges (sourceA1819 + difference 4 0) (sourceB1819 + difference 0 4) sourceC1819) = raw26314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26314; decide +kernel
    rw [ha]
    exact (canonical26314 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1819 + difference 4 1) (sourceB1819 + difference 1 4) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4238) := by
    have ha : (tripleCharges (sourceA1819 + difference 4 1) (sourceB1819 + difference 1 4) sourceC1819) = raw26315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26315; decide +kernel
    rw [ha]
    exact (canonical26315 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1819 + difference 4 2) (sourceB1819 + difference 2 4) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4200) := by
    have ha : (tripleCharges (sourceA1819 + difference 4 2) (sourceB1819 + difference 2 4) sourceC1819) = raw26316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26316; decide +kernel
    rw [ha]
    exact (canonical26316 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1819 + difference 4 3) (sourceB1819 + difference 3 4) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4255) := by
    have ha : (tripleCharges (sourceA1819 + difference 4 3) (sourceB1819 + difference 3 4) sourceC1819) = raw26317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26317; decide +kernel
    rw [ha]
    exact (canonical26317 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1819 + difference 4 5) (sourceB1819 + difference 5 4) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1819 + difference 4 5) (sourceB1819 + difference 5 4) sourceC1819) = raw26318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26318; decide +kernel
    rw [ha]
    exact (canonical26318 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1819 + difference 5 0) (sourceB1819 + difference 0 5) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4101) := by
    have ha : (tripleCharges (sourceA1819 + difference 5 0) (sourceB1819 + difference 0 5) sourceC1819) = raw26319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26319; decide +kernel
    rw [ha]
    exact (canonical26319 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1819 + difference 5 1) (sourceB1819 + difference 1 5) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4233) := by
    have ha : (tripleCharges (sourceA1819 + difference 5 1) (sourceB1819 + difference 1 5) sourceC1819) = raw26320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26320; decide +kernel
    rw [ha]
    exact (canonical26320 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1819 + difference 5 2) (sourceB1819 + difference 2 5) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4196) := by
    have ha : (tripleCharges (sourceA1819 + difference 5 2) (sourceB1819 + difference 2 5) sourceC1819) = raw26321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26321; decide +kernel
    rw [ha]
    exact (canonical26321 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1819 + difference 5 3) (sourceB1819 + difference 3 5) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1819 + difference 5 3) (sourceB1819 + difference 3 5) sourceC1819) = raw26322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26322; decide +kernel
    rw [ha]
    exact (canonical26322 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1819 + difference 5 4) (sourceB1819 + difference 4 5) sourceC1819) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1819 + difference 5 4) (sourceB1819 + difference 4 5) sourceC1819) = raw26323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1819 sourceB1819 sourceC1819 difference raw26323; decide +kernel
    rw [ha]
    exact (canonical26323 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1819 sourceB1819 sourceC1819
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1819, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1820 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1820 : Charge := ![0, 0, 0, 1, 0, -1]
def sourceC1820 : Charge := ![4, 0, 0, -2, -1, -1]
def sourceForm1820 : Integer.Sparse Master := [(Sum.inr 4069, 1), (Sum.inr 4119, 2), (Sum.inr 4128, 1), (Sum.inr 4130, 1), (Sum.inr 4133, 1), (Sum.inr 4210, 2), (Sum.inr 4219, 2), (Sum.inr 4221, 2), (Sum.inr 4224, 2), (Sum.inr 4265, 2), (Sum.inr 4267, 2), (Sum.inr 4268, 2), (Sum.inr 4270, 1), (Sum.inr 4273, 1), (Sum.inr 4276, 1), (Sum.inr 4279, 1), (Sum.inr 4283, 1), (Sum.inr 4424, 2), (Sum.inr 4499, 1), (Sum.inr 4502, 1), (Sum.inr 4503, 1)]

theorem sourceEq1820 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1820 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1820 + difference 0 1) (sourceB1820 + difference 1 0) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1820 + difference 0 1) (sourceB1820 + difference 1 0) sourceC1820) = raw26324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26324; decide +kernel
    rw [ha]
    exact (canonical26324 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1820 + difference 0 2) (sourceB1820 + difference 2 0) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1820 + difference 0 2) (sourceB1820 + difference 2 0) sourceC1820) = raw26325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26325; decide +kernel
    rw [ha]
    exact (canonical26325 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1820 + difference 0 3) (sourceB1820 + difference 3 0) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1820 + difference 0 3) (sourceB1820 + difference 3 0) sourceC1820) = raw26326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26326; decide +kernel
    rw [ha]
    exact (canonical26326 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1820 + difference 0 4) (sourceB1820 + difference 4 0) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1820 + difference 0 4) (sourceB1820 + difference 4 0) sourceC1820) = raw26327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26327; decide +kernel
    rw [ha]
    exact (canonical26327 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1820 + difference 0 5) (sourceB1820 + difference 5 0) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1820 + difference 0 5) (sourceB1820 + difference 5 0) sourceC1820) = raw26328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26328; decide +kernel
    rw [ha]
    exact (canonical26328 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1820 + difference 1 0) (sourceB1820 + difference 0 1) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4119) := by
    have ha : (tripleCharges (sourceA1820 + difference 1 0) (sourceB1820 + difference 0 1) sourceC1820) = raw26329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26329; decide +kernel
    rw [ha]
    exact (canonical26329 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1820 + difference 1 2) (sourceB1820 + difference 2 1) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4210) := by
    have ha : (tripleCharges (sourceA1820 + difference 1 2) (sourceB1820 + difference 2 1) sourceC1820) = raw26330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26330; decide +kernel
    rw [ha]
    exact (canonical26330 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1820 + difference 1 3) (sourceB1820 + difference 3 1) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1820 + difference 1 3) (sourceB1820 + difference 3 1) sourceC1820) = raw26331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26331; decide +kernel
    rw [ha]
    exact (canonical26331 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1820 + difference 1 4) (sourceB1820 + difference 4 1) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA1820 + difference 1 4) (sourceB1820 + difference 4 1) sourceC1820) = raw26332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26332; decide +kernel
    rw [ha]
    exact (canonical26332 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1820 + difference 1 5) (sourceB1820 + difference 5 1) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1820 + difference 1 5) (sourceB1820 + difference 5 1) sourceC1820) = raw26333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26333; decide +kernel
    rw [ha]
    exact (canonical26333 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1820 + difference 2 0) (sourceB1820 + difference 0 2) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4119) := by
    have ha : (tripleCharges (sourceA1820 + difference 2 0) (sourceB1820 + difference 0 2) sourceC1820) = raw26334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26334; decide +kernel
    rw [ha]
    exact (canonical26334 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1820 + difference 2 1) (sourceB1820 + difference 1 2) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4210) := by
    have ha : (tripleCharges (sourceA1820 + difference 2 1) (sourceB1820 + difference 1 2) sourceC1820) = raw26335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26335; decide +kernel
    rw [ha]
    exact (canonical26335 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1820 + difference 2 3) (sourceB1820 + difference 3 2) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1820 + difference 2 3) (sourceB1820 + difference 3 2) sourceC1820) = raw26336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26336; decide +kernel
    rw [ha]
    exact (canonical26336 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1820 + difference 2 4) (sourceB1820 + difference 4 2) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA1820 + difference 2 4) (sourceB1820 + difference 4 2) sourceC1820) = raw26337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26337; decide +kernel
    rw [ha]
    exact (canonical26337 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1820 + difference 2 5) (sourceB1820 + difference 5 2) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1820 + difference 2 5) (sourceB1820 + difference 5 2) sourceC1820) = raw26338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26338; decide +kernel
    rw [ha]
    exact (canonical26338 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1820 + difference 3 0) (sourceB1820 + difference 0 3) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4130) := by
    have ha : (tripleCharges (sourceA1820 + difference 3 0) (sourceB1820 + difference 0 3) sourceC1820) = raw26339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26339; decide +kernel
    rw [ha]
    exact (canonical26339 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1820 + difference 3 1) (sourceB1820 + difference 1 3) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4221) := by
    have ha : (tripleCharges (sourceA1820 + difference 3 1) (sourceB1820 + difference 1 3) sourceC1820) = raw26340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26340; decide +kernel
    rw [ha]
    exact (canonical26340 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1820 + difference 3 2) (sourceB1820 + difference 2 3) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4221) := by
    have ha : (tripleCharges (sourceA1820 + difference 3 2) (sourceB1820 + difference 2 3) sourceC1820) = raw26341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26341; decide +kernel
    rw [ha]
    exact (canonical26341 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1820 + difference 3 4) (sourceB1820 + difference 4 3) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1820 + difference 3 4) (sourceB1820 + difference 4 3) sourceC1820) = raw26342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26342; decide +kernel
    rw [ha]
    exact (canonical26342 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1820 + difference 3 5) (sourceB1820 + difference 5 3) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1820 + difference 3 5) (sourceB1820 + difference 5 3) sourceC1820) = raw26343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26343; decide +kernel
    rw [ha]
    exact (canonical26343 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1820 + difference 4 0) (sourceB1820 + difference 0 4) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4133) := by
    have ha : (tripleCharges (sourceA1820 + difference 4 0) (sourceB1820 + difference 0 4) sourceC1820) = raw26344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26344; decide +kernel
    rw [ha]
    exact (canonical26344 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1820 + difference 4 1) (sourceB1820 + difference 1 4) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4224) := by
    have ha : (tripleCharges (sourceA1820 + difference 4 1) (sourceB1820 + difference 1 4) sourceC1820) = raw26345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26345; decide +kernel
    rw [ha]
    exact (canonical26345 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1820 + difference 4 2) (sourceB1820 + difference 2 4) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4224) := by
    have ha : (tripleCharges (sourceA1820 + difference 4 2) (sourceB1820 + difference 2 4) sourceC1820) = raw26346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26346; decide +kernel
    rw [ha]
    exact (canonical26346 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1820 + difference 4 3) (sourceB1820 + difference 3 4) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4279) := by
    have ha : (tripleCharges (sourceA1820 + difference 4 3) (sourceB1820 + difference 3 4) sourceC1820) = raw26347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26347; decide +kernel
    rw [ha]
    exact (canonical26347 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1820 + difference 4 5) (sourceB1820 + difference 5 4) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4283) := by
    have ha : (tripleCharges (sourceA1820 + difference 4 5) (sourceB1820 + difference 5 4) sourceC1820) = raw26348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26348; decide +kernel
    rw [ha]
    exact (canonical26348 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1820 + difference 5 0) (sourceB1820 + difference 0 5) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4128) := by
    have ha : (tripleCharges (sourceA1820 + difference 5 0) (sourceB1820 + difference 0 5) sourceC1820) = raw26349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26349; decide +kernel
    rw [ha]
    exact (canonical26349 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1820 + difference 5 1) (sourceB1820 + difference 1 5) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4219) := by
    have ha : (tripleCharges (sourceA1820 + difference 5 1) (sourceB1820 + difference 1 5) sourceC1820) = raw26350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26350; decide +kernel
    rw [ha]
    exact (canonical26350 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1820 + difference 5 2) (sourceB1820 + difference 2 5) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4219) := by
    have ha : (tripleCharges (sourceA1820 + difference 5 2) (sourceB1820 + difference 2 5) sourceC1820) = raw26351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26351; decide +kernel
    rw [ha]
    exact (canonical26351 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1820 + difference 5 3) (sourceB1820 + difference 3 5) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4276) := by
    have ha : (tripleCharges (sourceA1820 + difference 5 3) (sourceB1820 + difference 3 5) sourceC1820) = raw26352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26352; decide +kernel
    rw [ha]
    exact (canonical26352 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1820 + difference 5 4) (sourceB1820 + difference 4 5) sourceC1820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1820 + difference 5 4) (sourceB1820 + difference 4 5) sourceC1820) = raw26353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1820 sourceB1820 sourceC1820 difference raw26353; decide +kernel
    rw [ha]
    exact (canonical26353 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1820 sourceB1820 sourceC1820
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1820, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1821 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1821 : Charge := ![4, 0, 0, -1, -1, -2]
def sourceC1821 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm1821 : Integer.Sparse Master := [(Sum.inr 4057, 2), (Sum.inr 4058, 1), (Sum.inr 4059, 2), (Sum.inr 4063, 2), (Sum.inr 4064, 2), (Sum.inr 4065, 4), (Sum.inr 4068, 2), (Sum.inr 4069, 6), (Sum.inr 4070, 2), (Sum.inr 4071, 2), (Sum.inr 4080, 2), (Sum.inr 4083, 1), (Sum.inr 4084, 2)]

theorem sourceEq1821 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1821 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1821 + difference 0 1) (sourceB1821 + difference 1 0) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA1821 + difference 0 1) (sourceB1821 + difference 1 0) sourceC1821) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1821 + difference 0 2) (sourceB1821 + difference 2 0) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA1821 + difference 0 2) (sourceB1821 + difference 2 0) sourceC1821) = raw11539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw11539; decide +kernel
    rw [ha]
    exact (canonical11539 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1821 + difference 0 3) (sourceB1821 + difference 3 0) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1821 + difference 0 3) (sourceB1821 + difference 3 0) sourceC1821) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1821 + difference 0 4) (sourceB1821 + difference 4 0) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1821 + difference 0 4) (sourceB1821 + difference 4 0) sourceC1821) = raw2924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw2924; decide +kernel
    rw [ha]
    exact (canonical2924 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1821 + difference 0 5) (sourceB1821 + difference 5 0) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA1821 + difference 0 5) (sourceB1821 + difference 5 0) sourceC1821) = raw3331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw3331; decide +kernel
    rw [ha]
    exact (canonical3331 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1821 + difference 1 0) (sourceB1821 + difference 0 1) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (tripleCharges (sourceA1821 + difference 1 0) (sourceB1821 + difference 0 1) sourceC1821) = raw26354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26354; decide +kernel
    rw [ha]
    exact (canonical26354 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1821 + difference 1 2) (sourceB1821 + difference 2 1) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA1821 + difference 1 2) (sourceB1821 + difference 2 1) sourceC1821) = raw26355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26355; decide +kernel
    rw [ha]
    exact (canonical26355 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1821 + difference 1 3) (sourceB1821 + difference 3 1) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1821 + difference 1 3) (sourceB1821 + difference 3 1) sourceC1821) = raw11531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw11531; decide +kernel
    rw [ha]
    exact (canonical11531 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1821 + difference 1 4) (sourceB1821 + difference 4 1) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1821 + difference 1 4) (sourceB1821 + difference 4 1) sourceC1821) = raw26356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26356; decide +kernel
    rw [ha]
    exact (canonical26356 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1821 + difference 1 5) (sourceB1821 + difference 5 1) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1821 + difference 1 5) (sourceB1821 + difference 5 1) sourceC1821) = raw14360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw14360; decide +kernel
    rw [ha]
    exact (canonical14360 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1821 + difference 2 0) (sourceB1821 + difference 0 2) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (tripleCharges (sourceA1821 + difference 2 0) (sourceB1821 + difference 0 2) sourceC1821) = raw26357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26357; decide +kernel
    rw [ha]
    exact (canonical26357 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1821 + difference 2 1) (sourceB1821 + difference 1 2) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA1821 + difference 2 1) (sourceB1821 + difference 1 2) sourceC1821) = raw26358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26358; decide +kernel
    rw [ha]
    exact (canonical26358 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1821 + difference 2 3) (sourceB1821 + difference 3 2) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1821 + difference 2 3) (sourceB1821 + difference 3 2) sourceC1821) = raw11534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw11534; decide +kernel
    rw [ha]
    exact (canonical11534 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1821 + difference 2 4) (sourceB1821 + difference 4 2) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1821 + difference 2 4) (sourceB1821 + difference 4 2) sourceC1821) = raw26359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26359; decide +kernel
    rw [ha]
    exact (canonical26359 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1821 + difference 2 5) (sourceB1821 + difference 5 2) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1821 + difference 2 5) (sourceB1821 + difference 5 2) sourceC1821) = raw14364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw14364; decide +kernel
    rw [ha]
    exact (canonical14364 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1821 + difference 3 0) (sourceB1821 + difference 0 3) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (tripleCharges (sourceA1821 + difference 3 0) (sourceB1821 + difference 0 3) sourceC1821) = raw26360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26360; decide +kernel
    rw [ha]
    exact (canonical26360 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1821 + difference 3 1) (sourceB1821 + difference 1 3) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1821 + difference 3 1) (sourceB1821 + difference 1 3) sourceC1821) = raw26361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26361; decide +kernel
    rw [ha]
    exact (canonical26361 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1821 + difference 3 2) (sourceB1821 + difference 2 3) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1821 + difference 3 2) (sourceB1821 + difference 2 3) sourceC1821) = raw26362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26362; decide +kernel
    rw [ha]
    exact (canonical26362 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1821 + difference 3 4) (sourceB1821 + difference 4 3) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (tripleCharges (sourceA1821 + difference 3 4) (sourceB1821 + difference 4 3) sourceC1821) = raw26363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26363; decide +kernel
    rw [ha]
    exact (canonical26363 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1821 + difference 3 5) (sourceB1821 + difference 5 3) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1821 + difference 3 5) (sourceB1821 + difference 5 3) sourceC1821) = raw14368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw14368; decide +kernel
    rw [ha]
    exact (canonical14368 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1821 + difference 4 0) (sourceB1821 + difference 0 4) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (tripleCharges (sourceA1821 + difference 4 0) (sourceB1821 + difference 0 4) sourceC1821) = raw23785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw23785; decide +kernel
    rw [ha]
    exact (canonical23785 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1821 + difference 4 1) (sourceB1821 + difference 1 4) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1821 + difference 4 1) (sourceB1821 + difference 1 4) sourceC1821) = raw23786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw23786; decide +kernel
    rw [ha]
    exact (canonical23786 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1821 + difference 4 2) (sourceB1821 + difference 2 4) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1821 + difference 4 2) (sourceB1821 + difference 2 4) sourceC1821) = raw23787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw23787; decide +kernel
    rw [ha]
    exact (canonical23787 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1821 + difference 4 3) (sourceB1821 + difference 3 4) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (tripleCharges (sourceA1821 + difference 4 3) (sourceB1821 + difference 3 4) sourceC1821) = raw11540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw11540; decide +kernel
    rw [ha]
    exact (canonical11540 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1821 + difference 4 5) (sourceB1821 + difference 5 4) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1821 + difference 4 5) (sourceB1821 + difference 5 4) sourceC1821) = raw14373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw14373; decide +kernel
    rw [ha]
    exact (canonical14373 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1821 + difference 5 0) (sourceB1821 + difference 0 5) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (tripleCharges (sourceA1821 + difference 5 0) (sourceB1821 + difference 0 5) sourceC1821) = raw22307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw22307; decide +kernel
    rw [ha]
    exact (canonical22307 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1821 + difference 5 1) (sourceB1821 + difference 1 5) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1821 + difference 5 1) (sourceB1821 + difference 1 5) sourceC1821) = raw22308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw22308; decide +kernel
    rw [ha]
    exact (canonical22308 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1821 + difference 5 2) (sourceB1821 + difference 2 5) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1821 + difference 5 2) (sourceB1821 + difference 2 5) sourceC1821) = raw22309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw22309; decide +kernel
    rw [ha]
    exact (canonical22309 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1821 + difference 5 3) (sourceB1821 + difference 3 5) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1821 + difference 5 3) (sourceB1821 + difference 3 5) sourceC1821) = raw5209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw5209; decide +kernel
    rw [ha]
    exact (canonical5209 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1821 + difference 5 4) (sourceB1821 + difference 4 5) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1821 + difference 5 4) (sourceB1821 + difference 4 5) sourceC1821) = raw5205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw5205; decide +kernel
    rw [ha]
    exact (canonical5205 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1821 sourceB1821 sourceC1821
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1821, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1822 : Charge := ![1, 0, -1, -1, -1, 2]
def sourceB1822 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC1822 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1822 : Integer.Sparse Master := [(Sum.inr 1700, 1), (Sum.inr 3057, 1), (Sum.inr 3072, 3), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

theorem sourceEq1822 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1822 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1822 + difference 0 0) (sourceB1822 + difference 0 0) sourceC1822) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA1822 + difference 0 0) (sourceB1822 + difference 0 0) sourceC1822) = raw26364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1822 sourceB1822 sourceC1822 difference raw26364; decide +kernel
    rw [ha]
    exact (canonical26364 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1822 + difference 0 1) (sourceB1822 + difference 1 0) sourceC1822) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3057) := by
    have ha : (tripleCharges (sourceA1822 + difference 0 1) (sourceB1822 + difference 1 0) sourceC1822) = raw26365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1822 sourceB1822 sourceC1822 difference raw26365; decide +kernel
    rw [ha]
    exact (canonical26365 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1822 + difference 0 2) (sourceB1822 + difference 2 0) sourceC1822) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3072) := by
    have ha : (tripleCharges (sourceA1822 + difference 0 2) (sourceB1822 + difference 2 0) sourceC1822) = raw26366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1822 sourceB1822 sourceC1822 difference raw26366; decide +kernel
    rw [ha]
    exact (canonical26366 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1822 + difference 0 3) (sourceB1822 + difference 3 0) sourceC1822) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3072) := by
    have ha : (tripleCharges (sourceA1822 + difference 0 3) (sourceB1822 + difference 3 0) sourceC1822) = raw26367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1822 sourceB1822 sourceC1822 difference raw26367; decide +kernel
    rw [ha]
    exact (canonical26367 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1822 + difference 0 4) (sourceB1822 + difference 4 0) sourceC1822) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3072) := by
    have ha : (tripleCharges (sourceA1822 + difference 0 4) (sourceB1822 + difference 4 0) sourceC1822) = raw26368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1822 sourceB1822 sourceC1822 difference raw26368; decide +kernel
    rw [ha]
    exact (canonical26368 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1822 + difference 0 5) (sourceB1822 + difference 5 0) sourceC1822) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1822 + difference 0 5) (sourceB1822 + difference 5 0) sourceC1822) = raw26369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1822 sourceB1822 sourceC1822 difference raw26369; decide +kernel
    rw [ha]
    exact (canonical26369 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1822 + sourceB1822) sourceC1822) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1822 + sourceB1822) sourceC1822) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1822 sourceB1822 sourceC1822 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1822 sourceB1822 sourceC1822
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1822, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1823 : Charge := ![1, 0, -1, -1, -1, 2]
def sourceB1823 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC1823 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1823 : Integer.Sparse Master := [(Sum.inr 1698, 1), (Sum.inr 1700, 1), (Sum.inr 1708, 3), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

theorem sourceEq1823 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1823 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1823 + difference 0 5) (sourceB1823 + difference 5 0) sourceC1823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1823 + difference 0 5) (sourceB1823 + difference 5 0) sourceC1823) = raw26369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1823 sourceB1823 sourceC1823 difference raw26369; decide +kernel
    rw [ha]
    exact (canonical26369 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1823 + difference 1 5) (sourceB1823 + difference 5 1) sourceC1823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA1823 + difference 1 5) (sourceB1823 + difference 5 1) sourceC1823) = raw26371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1823 sourceB1823 sourceC1823 difference raw26371; decide +kernel
    rw [ha]
    exact (canonical26371 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1823 + difference 2 5) (sourceB1823 + difference 5 2) sourceC1823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1823 + difference 2 5) (sourceB1823 + difference 5 2) sourceC1823) = raw26372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1823 sourceB1823 sourceC1823 difference raw26372; decide +kernel
    rw [ha]
    exact (canonical26372 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1823 + difference 3 5) (sourceB1823 + difference 5 3) sourceC1823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1823 + difference 3 5) (sourceB1823 + difference 5 3) sourceC1823) = raw26373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1823 sourceB1823 sourceC1823 difference raw26373; decide +kernel
    rw [ha]
    exact (canonical26373 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1823 + difference 4 5) (sourceB1823 + difference 5 4) sourceC1823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1823 + difference 4 5) (sourceB1823 + difference 5 4) sourceC1823) = raw26374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1823 sourceB1823 sourceC1823 difference raw26374; decide +kernel
    rw [ha]
    exact (canonical26374 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1823 + difference 5 5) (sourceB1823 + difference 5 5) sourceC1823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA1823 + difference 5 5) (sourceB1823 + difference 5 5) sourceC1823) = raw26364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1823 sourceB1823 sourceC1823 difference raw26364; decide +kernel
    rw [ha]
    exact (canonical26364 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1823 + sourceB1823) sourceC1823) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1823 + sourceB1823) sourceC1823) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1823 sourceB1823 sourceC1823 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1823 sourceB1823 sourceC1823
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1823, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
